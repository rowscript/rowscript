<h1 align="center">RowScript</h1>

![Rust Workflow](https://github.com/rowscript/rowscript/actions/workflows/rust.yml/badge.svg)

RowScript is a robustly-typed functional language that compiles to efficient and reliable JavaScript.

## Installing

```bash
$ npm i -g rowscript
```

## Features

### Dependent types

The type system is based on a dialect of Martin-Löf type theory with Π, Σ, universe, unit, and its elaboration uses the
normalization by evaluation (NbE) technique.

### JavaScript friendliness

Primitive types are JavaScript-based, e.g. `boolean`, `number`, `string`, `bigint`.

### User-friendly elaboration techniques

* Holes and pattern unification
* Implicit arguments

### Row polymorphism

Row polymorphism (or extensible types) is supported based on record concatenation.

### Object-oriented programming

OOP style constructs are based on row polymorphism and hence just some syntactic sugar.

### Interfaces

Powerful construct `interface` that acts like Haskell's typeclasses.

## Roadmap

* JavaScript code generation
    * [ ] Basic transpilation
    * [ ] FBIP (functional but in-place) and reuse analysis
* [ ] Datatype generics
* [ ] Auto-deriving
* [ ] Algebraic effects

## License

MIT
