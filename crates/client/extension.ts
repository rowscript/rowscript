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

function command(extensionPath: string) {
  return isProd ? path.join(extensionPath, commandHost(), id) : id;
}

// noinspection JSUnusedGlobalSymbols
export async function activate(ctx: ExtensionContext) {
  const run = { command: command(ctx.extensionPath), args: ["server"] };
  await new LanguageClient(
    id,
    name,
    { run, debug: run },
    {
      documentSelector: [{ scheme: "file", language: id }],
      synchronize: {
        fileEvents: workspace.createFileSystemWatcher("**/*.rows"),
      },
    },
  ).start();
}
