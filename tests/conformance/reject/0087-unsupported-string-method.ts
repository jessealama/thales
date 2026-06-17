// Most String.prototype methods type-check (tsc accepts them) but have no
// correct Lean lowering: many emit a nonexistent `String.<m>`, and some are
// semantically wrong — e.g. JS `replace` replaces only the first match, while
// Lean's `String.replace` replaces every one. They are out of the Thales
// subset rather than miscompiled. Only `startsWith`, `endsWith`, and `split`
// (plus the `length` property) are supported today.
const s: string = 'abcabc';
// @thales-expect-error TH0087
console.log(s.toUpperCase());
// @thales-expect-error TH0087
console.log(s.replace('a', 'X'));
