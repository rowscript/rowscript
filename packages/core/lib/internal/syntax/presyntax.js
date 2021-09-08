import * as presyntax from './presyntaxData.js'

export class Presyntax {
  constructor(concreteTree) {
    this._root = concreteTree.rootNode
    this._preTree = this._transform()
  }

  _transform() {
    console.log(this._root)
    return new presyntax.Var('x')
  }
}
