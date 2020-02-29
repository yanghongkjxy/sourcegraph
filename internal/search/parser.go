package search

import (
	"errors"
	"fmt"
	"io"
	"strings"
)

/*
Parser implements a parser for the following grammar:

OrTerm     → AndTerm { OR AndTerm }
AndTerm    → Term { AND Term }
Term       → (OrTerm) | Parameters
Parameters → Parameter { " " Parameter }
*/

type Node interface {
	String() string
	node()
}

// All terms that implement Node.
func (Parameter) node() {}
func (Operator) node()  {}

// Parameter is a leaf node of expressions.
type Parameter struct {
	Field string `json:"field"`
	Value string `json:"value"`
}

type operatorKind int

const (
	Or operatorKind = iota
	And
)

// Operator is a nonterminal node of kind Kind with child nodes Operands.
type Operator struct {
	Kind     operatorKind
	Operands []Node
}

func (node Parameter) String() string {
	if node.Field == "" {
		return node.Value
	} else {
		return fmt.Sprintf("%s:%s", node.Field, node.Value)
	}
}

func (node Operator) String() string {
	var result []string
	for _, child := range node.Operands {
		result = append(result, child.String())
	}
	var kind string
	if node.Kind == Or {
		kind = "or"
	} else {
		kind = "and"
	}
	return fmt.Sprintf("(%s %s)", kind, strings.Join(result, " "))
}

type keyword string

// Reserved keyword syntax.
const (
	AND    keyword = "and"
	OR     keyword = "or"
	LPAREN keyword = "("
	RPAREN keyword = ")"
)

func isSpace(c byte) bool {
	return (c == ' ') || (c == '\n') || (c == '\r') || (c == '\t')
}

// skipSpace returns the number of spaces skipped from the beginning of a buffer buf.
func skipSpace(buf []byte) int {
	for i, c := range buf {
		if !isSpace(c) {
			return i
		}
	}
	return len(buf)
}

type parser struct {
	buf      []byte
	pos      int
	balanced int
}

func (p *parser) done() bool {
	return p.pos >= len(p.buf)
}

// peek looks ahead n bytes in the input and returns a string if it succeeds, or
// an error if the length exceeds what's available in the buffer.
func (p *parser) peek(n int) (string, error) {
	if p.pos+n > len(p.buf) {
		return "", io.ErrShortBuffer
	}
	return string(p.buf[p.pos : p.pos+n]), nil
}

// match returns whether it succeeded matching a keyword at the current
// position. It does not advance the position.
func (p *parser) match(keyword keyword) bool {
	v, err := p.peek(len(string(keyword)))
	if err != nil {
		return false
	}
	return strings.ToLower(v) == string(keyword)
}

// expect returns the result of match, and advances the position if it succeeds.
func (p *parser) expect(keyword keyword) bool {
	if !p.match(keyword) {
		return false
	}
	p.pos += len(string(keyword))
	return true
}

// isKeyword returns whether current parser position matches a reserved keyword.
func (p *parser) isKeyword() bool {
	return p.match(AND) || p.match(OR) || p.match(LPAREN) || p.match(RPAREN)
}

// skipSpaces advances the input and places the parser position at the next
// non-space value.
func (p *parser) skipSpaces() error {
	if p.pos > len(p.buf) {
		return io.ErrShortBuffer
	}

	p.pos += skipSpace(p.buf[p.pos:])
	if p.pos > len(p.buf) {
		return io.ErrShortBuffer
	}
	return nil
}

// Want: colons to be escapable so that we can use them in patterns. Must be recognized here.
// Implication: must detect \\ as well.
// Should not: interpret colon if we see quotes.
// Remember: '-' is legal.
// TODO: Must consume, for if we detect a pattern \\ or \:, we should return \ and : resp.
func scanField(input []byte) int {
	for i, b := range input {
		// If it starts with a colon, reject it.
		if b == ':' && i == 0 {
			return 0
		}
		// If it starts with quotes, reject it.
		if b == '\'' || b == '"' && i == 0 {
			return 0
		}
		if b == ':' && i > 0 && input[i-1] != '\\' {
			return i
		}
	}
	return 0
}

// scanParameter scans for leaf node values.
// A parameter in the parse tree is a contiguous sequence characters, where the
// following three forms are distinguished:
// (1) a string of syntax <string1>:<string2> for nonempty string1, where : matches the first encountered colon
// (2) <string>
// (3) :<string>
//
// When a parameter is of form (1), the string corresponds to Field:Value in Parameter.
// When of form (2), Value corresponds to <string> and Field is the empty string.
// When of form (3), Value corresponds to :<string>, including the colon, and Field is the empty string.
//
// There is no restriction on values that <string> may take on, except that
// (1) colons, single and double quotes, and backslash must be escaped if they should be interpretted literally, e.g., as part of a pattern.
// (2) quoted strings may only occur at the start of a field or value string, and must be balanced. Quoted strings must be well-formed in the usual sense.
func (p *parser) ScanParameter() (Parameter, error) {
	start := p.pos
	for {
		if p.expect(`\ `) || p.expect(`\(`) || p.expect(`\)`) {
			continue
		}
		if p.isKeyword() {
			break
		}
		if p.done() {
			break
		}
		if isSpace(p.buf[p.pos]) {
			break
		}
		p.pos++
	}
	parameter := p.buf[start:p.pos]
	fieldLength := scanField(parameter)
	field := parameter[:fieldLength]
	value := parameter[fieldLength:]
	if fieldLength > 0 {
		// A colon was matched, and it wasn't the first character. Strip it from value.
		value = value[1:]
	}
	return Parameter{Field: string(field), Value: string(value)}, nil
}

// scanParameterList scans for consecutive leaf nodes.
func (p *parser) parseParameterList() ([]Node, error) {
	var nodes []Node
	for {
		if err := p.skipSpaces(); err != nil {
			return nil, err
		}
		if p.done() {
			break
		}
		switch {
		case p.expect(LPAREN):
			p.balanced++
			result, err := p.parseOr()
			if err != nil {
				return nil, err
			}
			nodes = append(nodes, result...)
		case p.expect(RPAREN):
			p.balanced--
			if len(nodes) == 0 {
				// Return a non-nil node if we parsed "()".
				return []Node{Parameter{Value: ""}}, nil
			}
			goto Done
		case p.match(AND), p.match(OR):
			// Caller advances.
			goto Done
		default:
			parameter, err := p.ScanParameter()
			if err != nil {
				return nil, err
			}
			nodes = append(nodes, parameter)
		}
	}
Done:
	// coalesce pattern nodes here
	return nodes, nil
}

// reduce takes lists of left and right nodes and reduces them if possible. For example,
// (and a (b and c))       => (and a b c)
// (((a and b) or c) or d) => (or (and a b) c d)
func reduce(left, right []Node, kind operatorKind) ([]Node, bool) {
	if param, ok := left[0].(Parameter); ok && param.Value == "" {
		// Remove empty string parameter.
		return right, true
	}

	switch right[0].(type) {
	case Operator:
		if kind == right[0].(Operator).Kind {
			// Reduce right node.
			left = append(left, right[0].(Operator).Operands...)
			if len(right) > 1 {
				left = append(left, right[1:]...)
			}
			return left, true
		}
	case Parameter:
		if right[0].(Parameter).Value == "" {
			// Remove empty string parameter.
			if len(right) > 1 {
				return append(left, right[1:]...), true
			}
			return left, true
		}
		if operator, ok := left[0].(Operator); ok && operator.Kind == kind {
			// Reduce left node.
			return append(left[0].(Operator).Operands, right...), true

		}
	}
	if len(right) > 1 {
		// Reduce right list.
		reduced, changed := reduce(append(left, right[0]), right[1:], kind)
		if changed {
			return reduced, true
		}
	}
	return append(left, right...), false
}

// newOperator constructs a new node of kind operatorKind with operands nodes,
// reducing nodes as needed.
func newOperator(nodes []Node, kind operatorKind) []Node {
	if len(nodes) == 0 {
		return nil
	} else if len(nodes) == 1 {
		return nodes
	}

	reduced, changed := reduce([]Node{nodes[0]}, nodes[1:], kind)
	if changed {
		return newOperator(reduced, kind)
	}
	return []Node{Operator{Kind: kind, Operands: reduced}}
}

// parseAnd parses and-expressions.
func (p *parser) parseAnd() ([]Node, error) {
	left, err := p.parseParameterList()
	if err != nil {
		return nil, err
	}
	if left == nil {
		return nil, fmt.Errorf("expected operand at %d", p.pos)
	}
	if !p.expect(AND) {
		return left, nil
	}
	right, err := p.parseAnd()
	if err != nil {
		return nil, err
	}
	return newOperator(append(left, right...), And), nil
}

// parseOr parses or-expressions. Or operators have lower precedence than And
// operators, therefore this function calls parseAnd.
func (p *parser) parseOr() ([]Node, error) {
	left, err := p.parseAnd()
	if err != nil {
		return nil, err
	}
	if left == nil {
		return nil, fmt.Errorf("expected operand at %d", p.pos)
	}
	if !p.expect(OR) {
		return left, nil
	}
	right, err := p.parseOr()
	if err != nil {
		return nil, err
	}
	return newOperator(append(left, right...), Or), nil
}

// Parse parses a raw input string into a parse tree comprising Nodes.
func Parse(in string) ([]Node, error) {
	if in == "" {
		return nil, nil
	}
	parser := &parser{buf: []byte(in)}
	nodes, err := parser.parseOr()
	if err != nil {
		return nil, err
	}
	if parser.balanced != 0 {
		return nil, errors.New("unbalanced expression")
	}
	return newOperator(nodes, And), nil
}
