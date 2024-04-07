import { Foo, Foo$new, Foo$update } from "./foo/index.mjs"

export function hello() {
    new Foo(42).update("hello")
    Foo$update(Foo$new(69), "world")
}
