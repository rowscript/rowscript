import * as presyntax from './presyntaxData.js'

export function of(concreteTree) {
  const root = concreteTree.rootNode
  console.log(root)
  console.log('hasError:', root.hasError())
  console.log('isMissing:', root.isMissing())
  return new presyntax.Var('x')
}
