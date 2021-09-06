export const DirL = 'L'
export const DirR = 'R'

export class Var {
  constructor(name) {
    this.name = name
  }
}

export class Env {
  constructor() {
    this.wellTyped = {}
  }
}

export class Ctx {
  constructor() {
    this.satisfied = {}
  }
}

export class Term {}

export class Ref extends Term {
  constructor(v) {
    this.v = v
  }
}

export class Lam extends Term {
  constructor(v, body) {
    this.v = v
    this.body = body
  }
}

export class App extends Term {
  constructor(lhs, rhs) {
    this.lhs = lhs
    this.rhs = rhs
  }
}

export class Let extends Term {
  constructor(v, sch, tm, body) {
    this.v = v
    this.sch = sch
    this.tm = tm
    this.body = body
  }
}

export class Label extends Term {
  constructor(l, tm) {
    this.l = l
    this.tm = tm
  }
}

export class Extr extends Term {
  constructor(tm, l) {
    this.tm = tm
    this.l = l
  }
}

export class Prj extends Term {
  constructor(dir, tm) {
    this.dir = dir
    this.tm = tm
  }
}

export class Concat extends Term {
  constructor(lhs, rhs) {
    this.lhs = lhs
    this.rhs = rhs
  }
}

export class Inj extends Term {
  constructor(dir, tm) {
    this.dir = dir
    this.tm = tm
  }
}

export class Case extends Term {
  constructor(lhs, rhs) {
    this.lhs = lhs
    this.rhs = rhs
  }
}
