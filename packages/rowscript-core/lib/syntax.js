'use strict'

export class Type {}

export class TVar extends Type {
  constructor(name) {
    this.name = name
  }
}

export class Arr extends Type {
  constructor(lhs, rhs) {
    this.lhs = lhs
    this.rhs = rhs
  }
}

export class Forall extends Type {
  constructor(tp, body) {
    this.tp = tp
    this.body = body
  }
}

export class Obj extends Type {
  constructor(types) {
    this.types = types
  }
}

export class Enum extends Type {
  constructor(types) {
    this.types = types
  }
}

export class Term {}

export class Var extends Term {
  constructor(name) {
    super()
    this.name = name
  }
}

export class Lam extends Term {
  constructor(v, tp, body) {
    this.var = v
    this.tp = tp
    this.body = body
  }
}

export class App extends Term {
  constructor(lhs, rhs) {
    this.lhs = lhs
    this.rhs = rhs
  }
}

export class TLam extends Term {
  constructor(tp, body) {
    this.tp = tp
    this.body = body
  }
}

export class TApp extends Term {
  constructor(lhs, rhs) {
    this.lhs = lhs
    this.rhs = rhs
  }
}

export class MkObj extends Term {
  constructor(tms) {
    this.tms = tms
  }
}

export class Prj extends Term {
  constructor(tm, name) {
    this.tm = tm
    this.name = name
  }
}

export class Inj extends Term {
  constructor(tm, name) {
    this.tm = tm
    this.name = name
  }
}

export class Case extends Term {
  constructor(tm, fns) {
    this.tm = tm
    this.fns = fns
  }
}
