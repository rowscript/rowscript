#!/usr/bin/env node

import yargs from 'yargs'
import { hideBin } from 'yargs/helpers'
import { compileFile } from '@rowscript/core'

yargs()
  .alias('h', 'help')
  .alias('v', 'version')
  .usage(
    '$0 [file]',
    'RowScript programming language',
    y => {
      y.positional('file', {
        describe: 'input file',
        type: 'string'
      })
    },
    ({ file }) => compileFile(file)
  )
  .parse(hideBin(process.argv))
