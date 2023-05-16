const enumify = (tag, v) => ({__enumT: tag, __enumV: v});

export function getData() { return enumify("Age", 42) }
export function setData(a) { console.log(a) }
