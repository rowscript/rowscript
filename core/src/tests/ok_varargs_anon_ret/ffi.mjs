export function f0(m, ...args) {
    console.log(m, ...args);
    return [0, "0"]
}

export function f1(...args) {
    console.log(...args);
    return [1, "1"]
}
