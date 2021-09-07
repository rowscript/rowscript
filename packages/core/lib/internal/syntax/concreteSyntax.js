import { readFile } from 'fs/promises'
import Parser from 'tree-sitter'
import RowScript from '@rowscript/tree-sitter'

export class ConcreteSyntax {
  constructor(file = '<stdin>') {
    this.file = file
    this.parser = new Parser()
    this.parser.setLanguage(RowScript)
  }

  parseString(text) {
    const tree = this.parser.parse(text)
    const errs = this.collectErrs(tree.rootNode)
    if (errs) {
      throw errs.map(s => s.toString()).join('\n')
    }
    return tree
  }

  async parseFile() {
    return this.parseString((await readFile(this.file)).toString())
  }

  collectErrs(tree) {
    const errs = []
    const nodes = [tree]

    while (nodes.length > 0) {
      const node = nodes.pop()

      if (!node.hasError()) {
        continue
      }

      if (node.type === 'ERROR') {
        errs.push(new SyntaxErr(this.file, node, 'Syntax error'))
      } else if (node.isMissing()) {
        errs.push(new SyntaxErr(this.file, node, 'Syntax error (missing)'))
      }

      for (const child of node.children) {
        nodes.push(child)
      }
    }

    if (errs.length > 0) {
      return errs
    }

    return null
  }
}

class SyntaxErr {
  constructor(file, node, msg) {
    this.file = file
    const { row, column } = node.startPosition
    this.pos = [row, column]
    this.msg = msg
  }

  toString() {
    const [line, col] = this.pos
    return `${this.file}:${line + 1}:${col}: ${this.msg}`
  }
}
