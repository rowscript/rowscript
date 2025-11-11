<!--suppress HtmlDeprecatedAttribute -->
<h1 align="center">
<!--suppress CheckImageSize -->
<img src="banner.jpeg" alt="banner" width="50%" height="50%">
<br>
RowScript
</h1>

![Build](https://github.com/rowscript/rowscript/actions/workflows/test.yml/badge.svg)

[RowScript] is a statically-typed JavaScript dialect that can compile to native code.

[RowScript]: https://rows.ro

> [!NOTE]
>
> We're working on a rewrite of RowScript, new features and releases are to be declared. See [#195] for an overview of
> new designs.

[#195]: https://github.com/rowscript/rowscript/issues/195

## Status

Update 2025-11-11:

* Language features and **an IDE** will be developed at the same time, development experience will now be prioritized
  even for very early releases.
* Setting breakpoints at a program is now possible. Shout out to [CodeLLDB].

![debugging](debugging.png)

[CodeLLDB]: https://marketplace.visualstudio.com/items?itemName=vadimcn.vscode-lldb

## Development

If you want to try all the latest features from the main branch, follow these steps:

```bash
# Install the compiler to your PATH.
$ cargo install --debug --path crates/server

# Make a debug build of the extension.
$ cd crates/client
$ npm run dev

```

Now, open your VS Code and press <kbd>F5</kbd> to debug the extension. Everything will work like a charm.

## License

MIT
