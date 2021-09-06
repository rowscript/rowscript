import { readFile } from 'fs/promises'
import Parser from 'tree-sitter'
import RowScript from '@rowscript/tree-sitter'

export const runCli = async args => {
  try {
    const data = (await readFile(args.file)).toString()
    const parser = new Parser()
    parser.setLanguage(RowScript)
    const tree = parser.parse(data)
    console.log(tree)
  } catch (err) {
    console.error(err)
  }
}
