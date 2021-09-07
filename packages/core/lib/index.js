import { ConcreteSyntax } from './internal/syntax/concreteSyntax.js'
import { Presyntax } from './internal/syntax/presyntax.js'

export const runCli = async args => {
  try {
    const concreteTree = await new ConcreteSyntax(args.file).parseFile()
    const preTree = new Presyntax().of(concreteTree)
    console.log(preTree)
  } catch (err) {
    console.error(err)
  }
}
