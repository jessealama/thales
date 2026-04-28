# disagree-missing

Exercises the FAIL branch when tsc flags a diagnostic that thales does not
produce. Current mechanism: `noUncheckedIndexedAccess` (TS2322). The first
candidate tried was literal-union narrowing (`type Color = "red" | "blue"`
with an assignment of `"green"`); thales actually rejects that case via
TH0022 (and produces a matching TS2322), so it did not yield a missing
diagnostic. The `noUncheckedIndexedAccess` case works: tsc reports TS2322
on the `const x: number = arr[0]` line because `arr[0]` has type
`number | undefined`, while thales's checker does not model indexed-access
narrowing and accepts the program. If thales gains coverage of the chosen TS
check, update `input.ts` to something still in tsc's coverage but outside
thales's, and record the new mechanism here.
