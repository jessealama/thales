// Mirror: tsc emits TS2540 for assignment to a readonly-declared property.
interface I { readonly p: number }
declare const i: I;
i.p = 1;
