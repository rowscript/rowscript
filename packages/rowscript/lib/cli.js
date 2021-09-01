'use strict'

import factory from 'yargs/yargs'
import run from '@rowscript/core'

export default cwd =>
  factory(null, cwd)
    .alias('h', 'help')
    .alias('v', 'version')
    .usage(
      '$0',
      'RowScript programming language',
      yargs => {
        yargs.options({
          f: {
            alias: 'file',
            demandOption: true,
            describe: 'input file',
            type: 'string'
          }
        })
      },
      argv => run(argv)
    )
