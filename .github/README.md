<!--suppress HtmlDeprecatedAttribute -->
<h1 align="center">
<!--suppress CheckImageSize -->
<img src="banner.jpeg" alt="banner" width="50%" height="50%">
<br>
RowScript
</h1>

![Build](https://github.com/rowscript/rowscript/actions/workflows/build.yml/badge.svg)

[RowScript] is a robustly-typed functional language that compiles to efficient and reliable JavaScript.

What if you have a language to have all these for a better frontend development experience?

| Features            | In RowScript |
|---------------------|--------------|
| Haskell's typeclass | `interface`  |
| Rust's `impl`       | `class`      |
| Go's interface      | `interface`  |

And luckily, the overall syntax would be in the style of TypeScript!

## Example

A hello-world example:

```ts
console.log("Hello, RowScript!");
```

More complicated example with classes and interfaces:

```ts
class Person {
    name: string;

    dial() {
        console.log(this.name)
    }
}

interface Phonebook {
    dial(a: Phonebook);
}

function dialPerson<P>(person: P) where Phonebook<P> {
    person.dial();
}

dialPerson(new Person("John Doe"));

```

[RowScript]: https://rowscript.github.io

## Installation

```bash
$ npm install -D rowscript
```

## Development status

This project is at early stage and under active development, syntax and APIs are expected to change.

We separate our development into following phases:

* [x] Proof-of-concept of research ideas and a most viable compiler
* [x] Get ready for open sourcing, targeting the **library writer** user group
* [ ] Get ready for production, targeting the **application writer** (end users) user group

## License

MIT
