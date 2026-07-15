// A null/undefined-guard ternary on an Option-typed value lowers through
// the same narrowing match as the statement-position `if`, so the narrowed
// branch reads the unwrapped value instead of projecting through the Option.
interface Box {
  v: bigint;
}

function fromNull(o: Box | null): bigint {
  return o === null ? 0n : o.v;
}

function fromNullNegated(o: Box | null): bigint {
  return o !== null ? o.v : 1n;
}

function fromUndefined(o: Box | undefined): bigint {
  return o === undefined ? 2n : o.v;
}

const b: Box = { v: 42n };
console.log(fromNull(null));
console.log(fromNull(b));
console.log(fromNullNegated(null));
console.log(fromNullNegated(b));
// Passing a bare `undefined` argument is outside the subset today (the
// emitter leaks it as an identifier); the undefined-guard arm is covered
// at the type level and by Test/Emit/NarrowingEmitTest.lean.
console.log(fromUndefined(b));
