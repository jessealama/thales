// Discriminated union error tests — these should produce type errors

type Shape =
  | { kind: 'circle'; radius: number }
  | { kind: 'rect'; width: number; height: number };

// Accessing property that doesn't exist on the un-narrowed union
function bad(s: Shape): number {
  return s.radius;
}
