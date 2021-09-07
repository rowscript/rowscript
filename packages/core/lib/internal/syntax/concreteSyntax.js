import Parser from 'tree-sitter'
import RowScript from '@rowscript/tree-sitter'

export const parseString = text => {
  const parser = new Parser()
  parser.setLanguage(RowScript)
  return parser.parse(text)
}
