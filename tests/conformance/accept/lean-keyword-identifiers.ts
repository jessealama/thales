// Lean reserved keywords (end, at, match, def, theorem, show) are all legal
// TypeScript identifiers — none are JS reserved words. They must be escaped at
// emit time (`«end»`, etc.) or the emitted Lean fails to compile (issue #11).

// Keyword field names on a discriminated union: emitted as inductive
// constructor fields and read back via projection.
type Span = { kind: 'span'; end: number } | { kind: 'point'; at: number };

function width(s: Span): number {
  switch (s.kind) {
    case 'span':
      return s.end;
    case 'point':
      return s.at;
  }
}

// Keyword function name, parameter name, and local-binding names.
function show(match: number): number {
  const def = match * 2;
  const theorem = def + 1;
  return theorem;
}

console.log(width({ kind: 'span', end: 9 }));
console.log(width({ kind: 'point', at: 3 }));
console.log(show(5));
console.log(show(-3));
