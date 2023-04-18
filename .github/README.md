<h1 align="center">RowScript</h1>

![Rust Build](https://github.com/rowscript/rowscript/actions/workflows/build.yml/badge.svg)
![Rust Check](https://github.com/rowscript/rowscript/actions/workflows/check.yml/badge.svg)

RowScript is a robustly-typed functional language that compiles to efficient and reliable JavaScript.

## Installing

```bash
$ npm i -g rowscript
```

## Ideas

There are several ideas about how to answer this question: *Why RowScript?*

### Totality

> Total type theory really is adequate for general-purpose programming.
>
> -- Jon Sterling, [Make Three To Throw Away], WITS '22

[Make Three To Throw Away]: https://www.jonmsterling.com/slides/sterling-2022-wits.pdf

### Universal scripting

> It makes sense to think of JavaScript as the universal scripting language.
>
> -- Ryan Dahl, [JavaScript Containers]

[JavaScript Containers]: https://tinyclouds.org/javascript_containers

### Row polymorphism

> Row polymorphism can be a typed solution to JavaScript's prototype-based design.
>
> -- [玩火 (niltok)], from a group talk in 2021

[玩火 (niltok)]: https://github.com/niltok

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

## License

MIT
