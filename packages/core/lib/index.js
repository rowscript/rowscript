import { ConcreteSyntax } from './internal/syntax/concreteSyntax.js'
import { Presyntax } from './internal/syntax/presyntax.js'

export const compileFile = async file => {
  try {
    const concreteTree = await new ConcreteSyntax(file).parseFile()
    const preTree = new Presyntax(concreteTree)
    console.log(preTree)
  } catch (err) {
    console.error(err)
  }
}
