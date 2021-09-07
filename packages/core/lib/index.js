import { readFile } from 'fs/promises'
import { parseString } from './internal/syntax/concreteSyntax.js'
import * as presyntax from './internal/syntax/presyntax.js'

export const runCli = async args => {
  try {
    const data = await readFile(args.file)
    const concreteTree = parseString(data.toString())
    const preTree = presyntax.of(concreteTree)
    console.log(preTree)
  } catch (err) {
    console.error(err)
  }
}
