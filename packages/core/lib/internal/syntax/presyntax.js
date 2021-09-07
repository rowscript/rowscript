import * as presyntax from './presyntaxData.js'

export class Presyntax {
  of(concreteTree) {
    const root = concreteTree.rootNode
    console.log(root)
    return new presyntax.Var('x')
  }
}
