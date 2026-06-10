// Mirror: tsc emits TS2540 for each enum-member assignment; thales must match.
enum E {
  A,
  B,
}
E.A = 1;
E['B'] = 2;
