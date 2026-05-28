// tsc emits TS2630 "Cannot assign to 'f' because it is a function" —
// this PR does NOT implement TS2630, so the TS code is missing from
// thales's output and the harness must report `fail:missing`. If TS2630
// later lands, swap the body for another still-unimplemented TS code.
function f(): void {}
f = (() => {}) as any;
