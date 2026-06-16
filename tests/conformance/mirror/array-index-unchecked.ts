// noUncheckedIndexedAccess mirror: xs[0] is `string | undefined`, not
// `string` — both type-checkers must reject the unnarrowed assignment
// identically.
const words: string[] = ['zero', 'one'];
const w: string = words[0];
console.log(w);
