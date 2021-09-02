'use strict'

import Parser from 'tree-sitter'
import RowScript from '@rowscript/tree-sitter'

export default args => {
  console.log(args)
  const parser = new Parser()
  parser.setLanguage(RowScript)
  const tree = parser.parse(`function a() {}`)
  console.log(tree)
}
