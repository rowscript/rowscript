'use strict'

const Parser = require('tree-sitter')
const RowScript = require('@rowscript/tree-sitter')

module.exports = { run }

function run(args) {
  console.log(args)
  const parser = new Parser()
  parser.setLanguage(RowScript)
  const tree = parser.parse(`function a() {}`)
  console.log(tree)
}
