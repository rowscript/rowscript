#!/usr/bin/env node

const {spawnSync} = require("child_process");

function binPath() {
    let os = process.platform;
    let extension = "";
    if (os === "win32" || os === "cygwin") {
        os = "win32";
        extension = ".exe";
    }
    const arch = process.arch;
    try {
        return require.resolve(`@rowscript/cli-${os}-${arch}/rowscript${extension}`);
    } catch (e) {
        throw new Error(`Binary not found in node_modules (${os}-${arch})`);
    }
}

process.exit(spawnSync(binPath(), process.argv.slice(2), {stdio: "inherit"}).status ?? 0);
