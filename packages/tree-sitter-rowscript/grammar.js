const ALPHA =
  /[^\x00-\x1F\s0-9:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/
const ALNUM =
  /[^\x00-\x1F\s:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/

function commaSep(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

export default grammar({
  name: 'rowscript',

  extras: $ => [$.comment, /[\s\t\r\n\uFEFF\u2060\u200B\u00A0]/],

  precedences: $ => [['declaration', 'literal']],

  word: $ => $.identifier,

  rules: {
    program: $ => repeat($.declaration),

    declaration: $ =>
      choice(
        $.functionDeclaration,
        $.classDeclaration,
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

    classDeclaration: $ =>
      prec(
        'declaration',
        seq(
          'class',
          field('name', $.identifier),
          optional($.classHeritage),
          field('body', $.classBody)
        )
      ),

    classHeritage: $ => seq('extends', field('base', $.identifier)),

    classBody: $ =>
      seq(
        '{',
        repeat(
          choice(
            field('member', $.methodDefinition),
            field('member', $.fieldDefinition)
          )
        ),
        '}'
      ),

    methodDefinition: $ =>
      seq(
        field('name', $._propertyName),
        field('parameters', $.declarationSignature),
        field('body', $.statementBlock)
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

    expression: $ =>
      choice(
        $.primaryExpression,
        $.assignmentExpression,
        $.augmentedAssignmentExpression,
        $.unaryExpression,
        $.binaryExpression,
        $.ternaryExpression,
        $.updateExpression,
        $.newExpression
      ),

    _propertyName: $ => choice($.identifier, $.string, $.number),

    identifier: $ => {
      return token(seq(ALPHA, repeat(ALNUM)))
    }
  }
})
