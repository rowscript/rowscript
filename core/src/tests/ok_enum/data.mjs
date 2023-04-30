const enumize = (tag, v) => ({__enumT: tag, __enumV: v});

export function getData() { return enumize("Age", 42) }
export function setData(a) { console.log(a) }
