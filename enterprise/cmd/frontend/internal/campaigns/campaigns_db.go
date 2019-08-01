package campaigns

import (
	"context"
	"time"

	"github.com/keegancsmith/sqlf"
	"github.com/pkg/errors"
	"github.com/sourcegraph/sourcegraph/cmd/frontend/db"
	"github.com/sourcegraph/sourcegraph/enterprise/cmd/frontend/internal/comments"
	"github.com/sourcegraph/sourcegraph/pkg/db/dbconn"
)

// dbCampaign describes a campaign.
type dbCampaign struct {
	ID              int64
	NamespaceUserID int32  // the user namespace where this campaign is defined
	NamespaceOrgID  int32  // the org namespace where this campaign is defined
	Name            string // the name (case-preserving)
	IsPreview       bool
	Rules           string // the JSON rules TODO!(sqs)

	PrimaryCommentID int64
	CreatedAt        time.Time
	UpdatedAt        time.Time
}

// errCampaignNotFound occurs when a database operation expects a specific campaign to exist but it
// does not exist.
var errCampaignNotFound = errors.New("campaign not found")

type dbCampaigns struct{}

const selectColumns = `id, namespace_user_id, namespace_org_id, name, is_preview, rules, primary_comment_id, created_at, updated_at`

// Create creates a campaign. The campaign argument's (Campaign).ID field is ignored. The new
// campaign is returned.
func (dbCampaigns) Create(ctx context.Context, campaign *dbCampaign, comment comments.DBObjectCommentFields) (*dbCampaign, error) {
	if mocks.campaigns.Create != nil {
		return mocks.campaigns.Create(campaign)
	}

	if campaign.PrimaryCommentID != 0 {
		panic("campaign.PrimaryCommentID must not be set")
	}

	nilIfZero := func(v int32) *int32 {
		if v == 0 {
			return nil
		}
		return &v
	}

	return campaign, comments.CreateWithObject(ctx, comment, func(ctx context.Context, tx comments.QueryRowContexter, commentID int64) (*comments.CommentObject, error) {
		var err error
		campaign, err = dbCampaigns{}.scanRow(tx.QueryRowContext(ctx,
			`INSERT INTO campaigns(`+selectColumns+`) VALUES(DEFAULT, $1, $2, $3, $4, $5, $6, DEFAULT, DEFAULT) RETURNING `+selectColumns,
			nilIfZero(campaign.NamespaceUserID),
			nilIfZero(campaign.NamespaceOrgID),
			campaign.Name,
			campaign.IsPreview,
			campaign.Rules,
			commentID,
		))
		if err != nil {
			return nil, err
		}
		return &comments.CommentObject{CampaignID: campaign.ID}, nil
	})
}

type dbCampaignUpdate struct {
	Name      *string
	IsPreview *bool
	Rules     *string
}

// Update updates a campaign given its ID.
func (s dbCampaigns) Update(ctx context.Context, id int64, update dbCampaignUpdate) (*dbCampaign, error) {
	if mocks.campaigns.Update != nil {
		return mocks.campaigns.Update(id, update)
	}

	var setFields []*sqlf.Query
	if update.Name != nil {
		setFields = append(setFields, sqlf.Sprintf("name=%s", *update.Name))
	}
	if update.IsPreview != nil {
		setFields = append(setFields, sqlf.Sprintf("is_preview=%s", *update.IsPreview))
	}
	if update.Rules != nil {
		setFields = append(setFields, sqlf.Sprintf("rules=%s", *update.Rules))
	}

	if len(setFields) == 0 {
		return nil, nil
	}
	setFields = append(setFields, sqlf.Sprintf("updated_at=now()"))

	results, err := s.query(ctx, sqlf.Sprintf(`UPDATE campaigns SET %v WHERE id=%s RETURNING `+selectColumns, sqlf.Join(setFields, ", "), id))
	if err != nil {
		return nil, err
	}
	if len(results) == 0 {
		return nil, errCampaignNotFound
	}
	return results[0], nil
}

// GetByID retrieves the campaign (if any) given its ID.
//
// 🚨 SECURITY: The caller must ensure that the actor is permitted to view this campaign.
func (s dbCampaigns) GetByID(ctx context.Context, id int64) (*dbCampaign, error) {
	if mocks.campaigns.GetByID != nil {
		return mocks.campaigns.GetByID(id)
	}

	results, err := s.list(ctx, []*sqlf.Query{sqlf.Sprintf("id=%d", id)}, nil)
	if err != nil {
		return nil, err
	}
	if len(results) == 0 {
		return nil, errCampaignNotFound
	}
	return results[0], nil
}

// dbCampaignsListOptions contains options for listing campaigns.
type dbCampaignsListOptions struct {
	Query           string // only list campaigns matching this query (case-insensitively)
	NamespaceUserID int32  // only list campaigns in this user's namespace
	NamespaceOrgID  int32  // only list campaigns in this org's namespace
	*db.LimitOffset
}

func (o dbCampaignsListOptions) sqlConditions() []*sqlf.Query {
	conds := []*sqlf.Query{sqlf.Sprintf("TRUE")}
	if o.Query != "" {
		conds = append(conds, sqlf.Sprintf("name ILIKE %s", "%"+o.Query+"%"))
	}
	if o.NamespaceUserID != 0 {
		conds = append(conds, sqlf.Sprintf("namespace_user_id=%d", o.NamespaceUserID))
	}
	if o.NamespaceOrgID != 0 {
		conds = append(conds, sqlf.Sprintf("namespace_org_id=%d", o.NamespaceOrgID))
	}
	return conds
}

// List lists all campaigns that satisfy the options.
//
// 🚨 SECURITY: The caller must ensure that the actor is permitted to list with the specified
// options.
func (s dbCampaigns) List(ctx context.Context, opt dbCampaignsListOptions) ([]*dbCampaign, error) {
	if mocks.campaigns.List != nil {
		return mocks.campaigns.List(opt)
	}

	return s.list(ctx, opt.sqlConditions(), opt.LimitOffset)
}

func (s dbCampaigns) list(ctx context.Context, conds []*sqlf.Query, limitOffset *db.LimitOffset) ([]*dbCampaign, error) {
	q := sqlf.Sprintf(`
SELECT `+selectColumns+` FROM campaigns
WHERE (%s)
ORDER BY name ASC
%s`,
		sqlf.Join(conds, ") AND ("),
		limitOffset.SQL(),
	)
	return s.query(ctx, q)
}

func (dbCampaigns) query(ctx context.Context, query *sqlf.Query) ([]*dbCampaign, error) {
	rows, err := dbconn.Global.QueryContext(ctx, query.Query(sqlf.PostgresBindVar), query.Args()...)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var results []*dbCampaign
	for rows.Next() {
		t, err := dbCampaigns{}.scanRow(rows)
		if err != nil {
			return nil, err
		}
		results = append(results, t)
	}
	return results, nil
}

func (dbCampaigns) scanRow(row interface {
	Scan(dest ...interface{}) error
}) (*dbCampaign, error) {
	var t dbCampaign
	var namespaceUserID, namespaceOrgID *int32
	if err := row.Scan(
		&t.ID,
		&namespaceUserID,
		&namespaceOrgID,
		&t.Name,
		&t.IsPreview,
		&t.Rules,
		&t.PrimaryCommentID,
		&t.CreatedAt,
		&t.UpdatedAt,
	); err != nil {
		return nil, err
	}
	if namespaceUserID != nil {
		t.NamespaceUserID = *namespaceUserID
	}
	if namespaceOrgID != nil {
		t.NamespaceOrgID = *namespaceOrgID
	}
	return &t, nil
}

// Count counts all campaigns that satisfy the options (ignoring limit and offset).
//
// 🚨 SECURITY: The caller must ensure that the actor is permitted to count the campaigns.
func (dbCampaigns) Count(ctx context.Context, opt dbCampaignsListOptions) (int, error) {
	if mocks.campaigns.Count != nil {
		return mocks.campaigns.Count(opt)
	}

	q := sqlf.Sprintf("SELECT COUNT(*) FROM campaigns WHERE (%s)", sqlf.Join(opt.sqlConditions(), ") AND ("))
	var count int
	if err := dbconn.Global.QueryRowContext(ctx, q.Query(sqlf.PostgresBindVar), q.Args()...).Scan(&count); err != nil {
		return 0, err
	}
	return count, nil
}

// Delete deletes a campaign given its ID.
//
// 🚨 SECURITY: The caller must ensure that the actor is permitted to delete the campaign.
func (s dbCampaigns) DeleteByID(ctx context.Context, id int64) error {
	if mocks.campaigns.DeleteByID != nil {
		return mocks.campaigns.DeleteByID(id)
	}
	return s.delete(ctx, sqlf.Sprintf("id=%d", id))
}

func (dbCampaigns) delete(ctx context.Context, cond *sqlf.Query) error {
	conds := []*sqlf.Query{cond, sqlf.Sprintf("TRUE")}
	q := sqlf.Sprintf("DELETE FROM campaigns WHERE (%s)", sqlf.Join(conds, ") AND ("))

	res, err := dbconn.Global.ExecContext(ctx, q.Query(sqlf.PostgresBindVar), q.Args()...)
	if err != nil {
		return err
	}
	nrows, err := res.RowsAffected()
	if err != nil {
		return err
	}
	if nrows == 0 {
		return errCampaignNotFound
	}
	return nil
}

// mockCampaigns mocks the campaigns-related DB operations.
type mockCampaigns struct {
	Create     func(*dbCampaign) (*dbCampaign, error)
	Update     func(int64, dbCampaignUpdate) (*dbCampaign, error)
	GetByID    func(int64) (*dbCampaign, error)
	List       func(dbCampaignsListOptions) ([]*dbCampaign, error)
	Count      func(dbCampaignsListOptions) (int, error)
	DeleteByID func(int64) error
}