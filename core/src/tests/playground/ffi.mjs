import * as fs from 'node:fs';

export const enumify = (tag, v) => ({__enumT: tag, __enumV: v});

export const arrayify = a => ({a: a, __enumV: a});

export function string$split(str, sep) { return arrayify(str.split(sep)); }
export function string$match(s, regexp) { return arrayify(s.match(regexp)); }

export function regExp$new(s, flags) { return new RegExp(s, flags); }
export function regExpnew(s, flags) { return new RegExp(s, flags); } // temporary

export function readfile(fname) {
    return fs.readFileSync(fname, {encoding:'utf8', flag:'r'}).replaceAll('\r','');
}
