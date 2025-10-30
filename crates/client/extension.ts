"use strict";

import * as path from "path";
import { ExtensionContext, workspace } from "vscode";
import { LanguageClient } from "vscode-languageclient/node";

const name = "RowScript";
const id = name.toLowerCase();
const isProd = process.env.NODE_ENV === "production";

function commandHost() {
  const host = `${process.platform}-${process.arch}`;
  switch (host) {
    case "darwin-arm64":
      return "macos-latest";
    case "win32-x64":
      return "windows-latest";
    case "linux-x64":
      return "ubuntu-latest";
    default:
      throw new Error(`Unsupported platform: ${host}`);
  }
}

// noinspection JSUnusedGlobalSymbols
export async function activate(ctx: ExtensionContext) {
  const command = isProd ? path.join(ctx.extensionPath, commandHost(), id) : id;
  const run = { command, args: ["server"] };
  const serverOptions = {
    run,
    debug: run,
  };
  const language = id;
  const clientOptions = {
    documentSelector: [{ scheme: "file", language }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher("**/*.rows"),
    },
  };
  await new LanguageClient(id, name, serverOptions, clientOptions).start();
}
