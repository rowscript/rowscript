package base

import "fmt"

type LocalVar struct{ Name string }

func (l *LocalVar) String() string { return l.Name }

func Unbound() *LocalVar { return &LocalVar{"_"} }

type Param[Term any] struct {
	Var  *LocalVar
	Type Term
}

func (p *Param[Term]) String() string { return fmt.Sprintf("(%s: %s)", p.Var, p.Type) }
