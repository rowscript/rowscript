/**
 * @file Tree-sitter grammar for RowScript
 * @author RowScript developers <anqurvanillapy@gmail.com>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: "rowscript",

  rules: {
    // TODO: add the actual grammar rules
    source_file: $ => "hello"
  }
});
