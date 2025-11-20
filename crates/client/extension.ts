"use strict";

import * as path from "path";
import * as which from "which";
import * as vscode from "vscode";
import { LanguageClient } from "vscode-languageclient/node";

const name = "RowScript";
const id = name.toLowerCase();
const isProd = process.env.NODE_ENV === "production";
const ext = ".rows";

let extensionPath: string;

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

function command() {
  return isProd
    ? path.join(extensionPath, commandHost(), id)
    : (which.sync(id, { nothrow: true }) ?? id);
}

// noinspection JSUnusedGlobalSymbols
export async function activate(ctx: vscode.ExtensionContext) {
  extensionPath = ctx.extensionPath;

  await activateDebugger(ctx);

  const run = { command: command(), args: ["server"] };
  await new LanguageClient(
    id,
    name,
    { run, debug: run },
    {
      documentSelector: [{ scheme: "file", language: id }],
      synchronize: {
        fileEvents: vscode.workspace.createFileSystemWatcher("**/*.rows"),
      },
    },
  ).start();
}

async function activateDebugger(ctx: vscode.ExtensionContext) {
  const lldb = "vadimcn.vscode-lldb";
  const dbg = vscode.extensions.getExtension(lldb);
  if (!dbg) {
    const link = `command:extension.open?${encodeURIComponent(`"${lldb}"`)}`;
    await vscode.window.showInformationMessage(
      `Install or enable [CodeLLDB](${link} "Open CodeLLDB") for further debugging`,
    );
    return;
  }
  const debugConfig = {
    name: "Debug RowScript Program",
    type: "lldb",
    request: "launch",
    program: command(),
    args: ["run", "${file}"],
    initCommands: ["settings set plugin.jit-loader.gdb.enable on"],
  };
  ctx.subscriptions.push(
    vscode.debug.registerDebugConfigurationProvider("lldb", {
      provideDebugConfigurations: (_folder) => [debugConfig],
      resolveDebugConfiguration(_folder, _debugConfiguration) {
        return vscode.window.activeTextEditor?.document.fileName.endsWith(ext)
          ? debugConfig
          : undefined;
      },
    }),
  );
}
