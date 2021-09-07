#!/usr/bin/env node

import yargs from 'yargs'
import { hideBin } from 'yargs/helpers'
import { runCli } from '@rowscript/core'

yargs()
  .alias('h', 'help')
  .alias('v', 'version')
  .usage(
    '$0',
    'RowScript programming language',
    y => {
      y.options({
        f: {
          alias: 'file',
          demandOption: true,
          describe: 'input file',
          type: 'string'
        }
      })
    },
    runCli
  )
  .parse(hideBin(process.argv))
