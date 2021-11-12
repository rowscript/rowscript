const ALPHA =
  /[^\x00-\x1F\s0-9:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/
const ALNUM =
  /[^\x00-\x1F\s:;`"'@#.,|^&<=>+\-*/\\%?!~()\[\]{}\uFEFF\u2060\u200B\u00A0]|\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]+\}/

function commaSep(rule) {
  return seq(rule, repeat(seq(',', rule)))
}

function sep(s, rule) {
  return seq(rule, repeat(seq(s, rule)))
}

module.exports = grammar({
  name: 'rowscript',

  extras: $ => [$._comment, /[\s\t\r\n\uFEFF\u2060\u200B\u00A0]/],

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
    ['member', 'new', 'call', $.expression],
    ['declaration', 'literal'],
    [$.abstractionSignature, $.primaryExpression, $.statementBlock, 'object']
  ],

  word: $ => $.identifier,

  rules: {
    program: $ => repeat($.declaration),

    declaration: $ =>
      choice($.functionDeclaration, $.classDeclaration, $.typeAliasDeclaration),

    functionDeclaration: $ =>
      prec.right(
        'declaration',
        seq(
          'function',
          field('name', $.identifier),
          field('scheme', optional($.typeSchemeBinders)),
          field('sig', $.declarationSignature),
          optional(seq(':', field('ret', $.typeExpression))),
          field('body', $.statementBlock)
        )
      ),

    classDeclaration: $ =>
      prec(
        'declaration',
        seq(
          'class',
          field('name', $.identifier),
          optional($.typeSchemeBinders),
          optional($.classHeritage),
          field('body', $.classBody)
        )
      ),

    classHeritage: $ =>
      seq(
        'extends',
        field('base', $.identifier),
        optional($.typeSchemeBinders)
      ),

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
        field('name', $.identifier),
        field('parameters', $.declarationSignature),
        field('body', $.statementBlock)
      ),

    fieldDefinition: $ =>
      seq(field('property', $.identifier), optional($._initializer)),

    lexicalDeclaration: $ =>
      seq('let', commaSep($.variableDeclarator), ';', $.statement),

    variableDeclarator: $ =>
      seq(
        field('name', $.identifier),
        optional(seq(':', field('type', $.typeExpression))),
        $._initializer
      ),

    _initializer: $ => seq('=', field('value', $.expression)),

    typeAliasDeclaration: $ =>
      seq(
        'type',
        field('name', $.identifier),
        '=',
        field('target', $.typeScheme),
        ';'
      ),

    declarationSignature: $ =>
      seq('(', optional(commaSep($.formalParameter)), ')'),

    formalParameter: $ => seq($.identifier, ':', $.typeExpression),

    abstractionSignature: $ => seq('(', optional(commaSep($.identifier)), ')'),

    statementBlock: $ => prec.right(seq('{', optional($.statement), '}')),

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
          'else',
          field('else', $.statementBlock)
        )
      ),

    switchStatement: $ =>
      seq(
        'switch',
        field('value', $.parenthesizedExpression),
        field('body', $.switchBody)
      ),

    switchBody: $ =>
      seq('{', repeat($.switchCase), optional($.switchDefault), '}'),

    switchCase: $ =>
      seq(
        'case',
        field('label', $.identifier),
        optional(field('variable', $.identifier)),
        ':',
        field('statement', $.statement)
      ),

    switchDefault: $ => seq('default', ':', $.statement),

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

    returnStatement: $ => seq('return', optional($.expression)),

    throwStatement: $ => seq('throw', $.expression),

    typeSchemeBinders: $ => seq('<', optional(commaSep($.identifier)), '>'),

    typeScheme: $ => seq(optional($.typeSchemeBinders), $.typeExpression),

    typeExpression: $ => prec.right(sep('->', $.typeTerm)),

    typeTerm: $ =>
      choice(
        $.recordType,
        $.variantType,
        $.arrayType,
        // "Wow we got tuple type!" no it's just a sugar for records.
        $.tupleType,
        $.stringType,
        $.numberType,
        $.booleanType,
        $.bigintType,
        $.identifier
      ),

    recordType: $ =>
      choice(
        '{}',
        seq('{', $.identifier, '}'),
        seq('{', commaSep(seq($.identifier, ':', $.typeExpression)), '}')
      ),

    variantType: $ =>
      prec.left(
        choice(
          seq('@|', optional($.identifier)),
          sep('|', seq('@', $.identifier, optional($.typeExpression)))
        )
      ),

    arrayType: $ => seq('[', $.typeExpression, ']'),

    tupleType: $ => choice('()', seq('(', commaSep($.typeExpression), ')')),

    stringType: () => 'string',
    numberType: () => 'number',
    booleanType: () => 'boolean',
    bigintType: () => 'bigint',

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
        $.variant,
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

    memberExpression: $ =>
      prec(
        'member',
        seq(
          field('object', choice($.expression, $.primaryExpression)),
          '.',
          field('property', $.identifier)
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

    object: $ => prec('object', seq('{', optional(commaSep($.pair)), '}')),

    variant: $ => prec.left(seq('@', $.identifier, optional($.expression))),

    pair: $ =>
      seq(field('key', $.identifier), ':', field('value', $.expression)),

    array: $ => seq('[', commaSep(optional($.expression)), ']'),

    arrowFunction: $ =>
      prec.right(
        seq(
          field('parameter', $.abstractionSignature),
          '=>',
          field('body', choice($.expression, $.statementBlock))
        )
      ),

    callExpression: $ =>
      prec(
        'call',
        seq(field('function', $.expression), field('arguments', $.arguments))
      ),

    identifier: () => token(seq(ALPHA, repeat(ALNUM))),

    this: () => 'this',
    super: () => 'super',
    true: () => 'true',
    false: () => 'false',

    number: () => {
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

    unescapedDoubleStringFragment: () => token.immediate(prec(1, /[^"\\]+/)),

    unescapedSingleStringFragment: () => token.immediate(prec(1, /[^'\\]+/)),

    escapeSequence: () =>
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

    regexPattern: () =>
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

    regexFlags: () => token.immediate(/[a-z]+/),

    // TODO: Comment group should be attached for documentation. Ignored now for being lazy.
    _comment: () =>
      token(choice(seq('//', /.*/), seq('/*', /[^*]*\*+([^/*][^*]*\*+)*/, '/')))
  }
})
