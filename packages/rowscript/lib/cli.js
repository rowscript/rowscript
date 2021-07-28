'use strict'

import factory from 'yargs/yargs'
import rowscript from './rowscript'

export default cli

function cli (cwd) {
  const parser = factory(null, cwd)

  parser.alias('h', 'help')
  parser.alias('v', 'version')

  parser.usage(
    '$0',
    'TODO: description',
    yargs => {
      yargs.options({
        // TODO: options
      })
    },
    argv => rowscript(argv)
  )

  return parser
}
