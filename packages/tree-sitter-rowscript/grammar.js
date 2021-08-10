const ALPHA =
  /[^\x00-\x1F\s0-9:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/
const ALNUM =
  /[^\x00-\x1F\s:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/

function commaSep(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

export default grammar({
  name: 'rowscript',

  precedences: $ => [['declaration', 'literal']],

  rules: {
    program: $ => repeat($.declaration),

    declaration: $ =>
      choice(
        $.functionDeclaration,
        $.lexicalDeclaration,
        $.typeAliasDeclaration
      ),

    functionDeclaration: $ =>
      prec.right(
        'declaration',
        seq(
          'function',
          field('name', $.identifier),
          $.declarationSignature,
          field('field', $.statementBlock)
        )
      ),

    lexicalDeclaration: $ => seq('const', commaSep($.variableDeclarator), ';'),

    variableDeclarator: $ => seq(field('name', $.identifier), $._initializer),

    _initializer: $ => seq('=', field('value', $.expression)),

    typeAliasDeclaration: $ =>
      seq(
        'type',
        field('name', $.identifier),
        '=',
        field('target', $.typeExpression),
        ';'
      ),

    declarationSignature: $ =>
      seq('(', optional(seq(commaSep($.formalParameter))), ')'),

    formalParameter: $ => seq($.identifier, optional(seq(':', typeExpression))),

    statementBlock: $ => prec.right(seq('{', repeat($.statement), '}')),

    statement: $ =>
      choice(
        $.lexicalDeclaration,

        $.ifExpression,
        $.switchExpression, // pattern matching
        $.tryExpression, // checked exceptions
        $.doExpression, // do-notation

        $.returnExpression,
        $.throwExpression
      ),

    identifier: $ => {
      return token(seq(ALPHA, repeat(ALNUM)))
    }
  }
})
