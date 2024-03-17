export const enumify = (tag, v) => ({__enumT: tag, __enumV: v});

export const arrayify = a => ({a: a, __enumV: a});
