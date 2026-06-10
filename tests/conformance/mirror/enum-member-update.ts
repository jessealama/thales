// Mirror: tsc emits TS2540 for each ++/-- on enum members; thales must match.
enum E {
  A,
  B,
}
E.A++;
++E.B;
--E['A'];
