// Narrowing error tests — these should produce type errors

// Un-narrowed union assigned to a string at top level: string | number is not assignable to string
function getUnion(): string | number {
  return 42;
}
let s: string = getUnion();
