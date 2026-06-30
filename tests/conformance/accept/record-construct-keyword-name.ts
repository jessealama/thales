// A record type whose NAME is a Lean keyword (legal TS identifier, not a JS
// reserved word) must have its type name escaped at emit (`«end»`), both in the
// `structure`/`abbrev` declaration and in the `{ … : T }` construction ascription
// — otherwise the emitted Lean fails to compile (the type-name analogue of #11).
interface end {
  v: bigint;
}
type match = { n: bigint };

function mkEnd(v: bigint): end {
  return { v };
}

function mkMatch(n: bigint): match {
  return { n };
}

console.log(mkEnd(7n).v);
console.log(mkMatch(3n).n);
