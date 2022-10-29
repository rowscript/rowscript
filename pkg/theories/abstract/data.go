package abstract

import "github.com/rowscript/rowscript/pkg/theories/base"

type Dir int

const (
	Left Dir = iota + 1
	Right
)

type (
	Term interface{}

	Ref struct{ Var *base.LocalVar }
	Let struct {
		Param    base.Param[Term]
		Tm, Body Term
	}

	univ struct{}

	Fn struct {
		Param base.Param[Term]
		Cod   Term
	}
	Lam struct {
		Param base.Param[Term]
		Body  Term
	}
	App struct{ F, A Term }

	RowConcatEq struct{ A, B, C Term }
	RowRefl     struct{}

	RowCont struct {
		Dir      Dir
		Lhs, Rhs Term
	}
	RowSat struct{}

	Row struct {
		Name string
		Type Term
	}
	Label struct {
		Name string
		Tm   Term
	}
	Unlabel struct {
		Tm   Term
		Name string
	}

	Record struct{ Rows []Term }
	Prj    struct {
		Dir Dir
		Tm  Term
	}
	Concat struct{ Lhs, Rhs Term }

	Variant struct{ Rows []Term }
	Inj     struct {
		Dir Dir
		Tm  Term
	}
	Branch struct{ Lhs, Rhs Term }
)

var (
	U = new(univ)
)
