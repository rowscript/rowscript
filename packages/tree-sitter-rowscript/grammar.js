const ALPHA =
  /[^\x00-\x1F\s0-9:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/
const ALNUM =
  /[^\x00-\x1F\s:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/

function commaSep(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

// TODO:
// 1. Support `??` (nullish coalescing) and `?.` (optional chaining) operators?
module.exports = grammar({
  name: 'rowscript',

  extras: $ => [$.comment, /[\s\t\r\n\uFEFF\u2060\u200B\u00A0]/],

  precedences: $ => [
    [
      'unary',
      'binary_exp',
      'binary_times',
      'binary_plus',
      'binary_ordering',
      'binary_and',
      'binary_or',
      'ternary'
    ],
    ['declaration', 'literal'],
    ['member', 'new', 'call', $.expression]
  ],

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

    fieldDefinition: $ =>
      seq(field('property', $._propertyName), optional($._initializer)),

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

        $.ifStatement,
        $.switchStatement, // pattern matching
        $.tryStatement, // checked exceptions
        $.doStatement, // do-notation

        $.returnStatement,
        $.throwStatement
      ),

    ifStatement: $ =>
      prec.right(
        seq(
          'if',
          field('cond', $.parenthesizedExpression),
          field('then', $.statementBlock),
          optional(field('else', $.elseClause))
        )
      ),

    elseClause: $ => seq('else', $.statementBlock),

    switchStatement: $ =>
      seq(
        'switch',
        field('value', $.parenthesizedExpression, field('body', $.switchBody))
      ),

    switchBody: $ =>
      seq('{', repeat(choice($.switchCase, $.switchDefault)), '}'),

    switchCase: $ =>
      seq('case', field('value', $.expression, ':', repeat($.statement))),

    switchDefault: $ => seq('default', ':', repeat($.statement)),

    tryStatement: $ =>
      seq(
        'try',
        field('body', $.statementBlock),
        repeat(field('handlers', $.catchClause))
      ),

    catchClause: $ =>
      seq(
        'catch',
        seq(
          '(',
          field('parameter', $.identifier),
          optional(seq(':', field('type', $.typeExpression))),
          ')'
        ),
        field('body', $.statementBlock)
      ),

    doStatement: $ =>
      seq(
        'do',
        field('body', $.statementBlock),
        'while',
        field('lift', $.parenthesizedExpression),
        ';'
      ),

    // TODO: Statement is actually some kind of a `let` expression, so it must
    // end with `returnStatement` or `throwStatement` which makes rest of the
    // code unreachable.
    returnStatement: $ => seq('return', optional($.expression), ';'),

    throwStatement: $ => seq('throw', $.expression, ';'),

    typeExpression: $ =>
      seq(
        optional(repeat1($.identifier), '=>'),
        $.typeTerm,
        repeat(seq('->', $.typeTerm))
      ),

    // TODO: Records, variants, and perhaps arrays.
    typeTerm: $ =>
      choice(
        $.recordType,
        $.variantType,
        $.stringType,
        $.numberType,
        $.booleanType,
        $.bigintType,
        $.identifier
      ),

    stringType: $ => 'string',
    numberType: $ => 'number',
    booleanType: $ => 'boolean',
    bigintType: $ => 'bigint',

    expression: $ =>
      choice(
        $.primaryExpression,
        $.unaryExpression,
        $.binaryExpression,
        $.ternaryExpression,
        $.newExpression
      ),

    primaryExpression: $ =>
      choice(
        $.subscriptExpression,
        $.memberExpression,
        $.parenthesizedExpression,
        $.identifier,
        $.this,
        $.super,
        $.number,
        $.string,
        $.regex,
        $.false,
        $.true,
        $.object,
        $.array,
        $.arrowFunction,
        $.callExpression
      ),

    subscriptExpression: $ =>
      prec.right(
        'member',
        seq(
          field('object', $.expression),
          '[',
          field('index', $.expression),
          ']'
        )
      ),

    unaryExpression: $ =>
      prec.left(
        'unary',
        seq(
          field('operator', choice('!', '~', '-', '+')),
          field('argument', $.expression)
        )
      ),

    binaryExpression: $ =>
      choice(
        ...[
          ['**', 'binary_exp'],
          ['*', 'binary_times'],
          ['/', 'binary_times'],
          ['%', 'binary_times'],
          ['>>', 'binary_times'],
          ['>>>', 'binary_times'],
          ['<<', 'binary_times'],
          ['+', 'binary_plus'],
          ['-', 'binary_plus'],
          ['<', 'binary_ordering'],
          ['<=', 'binary_ordering'],
          ['==', 'binary_ordering'],
          ['!=', 'binary_ordering'],
          ['>=', 'binary_ordering'],
          ['>', 'binary_ordering'],
          ['&&', 'binary_and'],
          ['&', 'binary_and'],
          ['||', 'binary_or'],
          ['|', 'binary_or'],
          ['^', 'binary_or']
        ].map(([operator, precedence]) =>
          prec.left(
            precedence,
            seq(
              field('left', $.expression),
              field('operator', operator),
              field('right', $.expression)
            )
          )
        )
      ),

    ternaryExpression: $ =>
      prec.right(
        'ternary',
        seq(
          field('cond', $.expression),
          '?',
          field('then', $.expression),
          ':',
          field('else', $.expression)
        )
      ),

    newExpression: $ =>
      prec.right(
        'new',
        seq(
          'new',
          field('constructor', $.identifier),
          field('arguments', $.arguments)
        )
      ),

    arguments: $ => seq('(', optional(commaSep($.expression)), ')'),

    parenthesizedExpression: $ => seq('(', $.expression, ')'),

    _propertyName: $ => choice($.identifier, $.string, $.number),

    object: $ =>
      prec(
        'object',
        seq(
          '{',
          optional(
            commaSep(optional(choice($.pair, $.methodDefinition, $.identifier)))
          ),
          '}'
        )
      ),

    pair: $ =>
      seq(field('key', $._propertyName), ':', field('value', $.expression)),

    array: $ => seq('[', commaSep(optional($.expression)), ']'),

    arrowFunction: $ =>
      seq(
        choice(field('parameter', $.identifier), $.declarationSignature),
        '=>',
        field('body', choice($.expression, $.statementBlock))
      ),

    callExpression: $ =>
      prec(
        'call',
        seq(field('function', $.expression), field('arguments', $.arguments))
      ),

    identifier: $ => token(seq(ALPHA, repeat(ALNUM))),

    this: $ => 'this',
    super: $ => 'super',
    true: $ => 'true',
    false: $ => 'false',

    number: $ => {
      const hexLiteral = seq(choice('0x', '0X'), /[\da-fA-F](_?[\da-fA-F])*/)

      const decimalDigits = /\d(_?\d)*/
      const signedInteger = seq(optional(choice('-', '+')), decimalDigits)
      const exponentPart = seq(choice('e', 'E'), signedInteger)

      const binaryLiteral = seq(choice('0b', '0B'), /[0-1](_?[0-1])*/)

      const octalLiteral = seq(choice('0o', '0O'), /[0-7](_?[0-7])*/)

      const bigintLiteral = seq(
        choice(hexLiteral, binaryLiteral, octalLiteral, decimalDigits),
        'n'
      )

      const decimalIntegerLiteral = choice(
        '0',
        seq(optional('0'), /[1-9]/, optional(seq(optional('_'), decimalDigits)))
      )

      const decimalLiteral = choice(
        seq(
          decimalIntegerLiteral,
          '.',
          optional(decimalDigits),
          optional(exponentPart)
        ),
        seq('.', decimalDigits, optional(exponentPart)),
        seq(decimalIntegerLiteral, exponentPart),
        seq(decimalDigits)
      )

      return token(
        choice(
          hexLiteral,
          decimalLiteral,
          binaryLiteral,
          octalLiteral,
          bigintLiteral
        )
      )
    },

    string: $ =>
      choice(
        seq(
          '"',
          repeat(
            choice(
              alias($.unescapedDoubleStringFragment, $.stringFragment),
              $.escapeSequence
            )
          ),
          '"'
        ),
        seq(
          "'",
          repeat(
            choice(
              alias($.unescapedSingleStringFragment, $.stringFragment),
              $.escapeSequence
            )
          ),
          "'"
        )
      ),

    unescapedDoubleStringFragment: $ => token.immediate(prec(1, /[^"\\]+/)),

    unescapedSingleStringFragment: $ => token.immediate(prec(1, /[^'\\]+/)),

    escapeSequence: $ =>
      token.immediate(
        seq(
          '\\',
          choice(
            /[^xu0-7]/,
            /[0-7]{1,3}/,
            /x[0-9a-fA-F]{2}/,
            /u[0-9a-fA-F]{4}/,
            /u{[0-9a-fA-F]+}/
          )
        )
      ),

    regex: $ =>
      seq(
        '/',
        field('pattern', $.regexPattern),
        token.immediate('/'),
        optional(field('flags', $.regexFlags))
      ),

    regexPattern: $ =>
      token.immediate(
        prec(
          -1,
          repeat1(
            choice(
              seq('[', repeat(choice(seq('\\', /./), /[^\]\n\\]/)), ']'),
              seq('\\', /./),
              /[^/\\\[\n]/
            )
          )
        )
      ),

    regexFlags: $ => token.immediate(/[a-z]+/),

    comment: $ =>
      token(choice(seq('//', /.*/), seq('/*', /[^*]*\*+([^/*][^*]*\*+)*/, '/')))
  }
})
