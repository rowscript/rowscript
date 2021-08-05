'use strict'

export class Type {}

export class TVar extends Type {
  constructor(name) {
    this._name = name
  }
}

export class Arr extends Type {
  constructor(lhs, rhs) {
    this._lhs = lhs
    this._rhs = rhs
  }
}

export class Forall extends Type {
  constructor(tp, body) {
    this._tp = tp
    this._body = body
  }
}

export class Obj extends Type {
  constructor(types) {
    this._types = types
  }
}

export class Enum extends Type {
  constructor(types) {
    this._types = types
  }
}

export class Term {}

export class Var extends Term {
  constructor(name) {
    super()
    this._name = name
  }
}

export class Lam extends Term {
  constructor(v, tp, body) {
    this._var = v
    this._tp = tp
    this._body = body
  }
}

export class App extends Term {
  constructor(lhs, rhs) {
    this._lhs = lhs
    this._rhs = rhs
  }
}

export class TLam extends Term {
  constructor(tp, body) {
    this._tp = tp
    this._body = body
  }
}

export class TApp extends Term {
  constructor(lhs, rhs) {
    this._lhs = lhs
    this._rhs = rhs
  }
}

export class MkObj extends Term {
  constructor(tms) {
    this._tms = tms
  }
}

export class Proj extends Term {
  constructor(tm, name) {
    this._tm = tm
    this._name = name
  }
}

export class Inj extends Term {
  constructor(tm, name) {
    this._tm = tm
    this._name = name
  }
}

export class Case extends Term {
  constructor(tm, fns) {
    this._tm = tm
    this._fns = fns
  }
}
