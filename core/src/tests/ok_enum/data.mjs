const enumify = (tag, v) => ({tag: v});

export function getData() { return enumify("Age", 42) }
export function setData(a) { console.log(a) }
