// A definedness test against `undefined`/`null` is lowered only when its
// subject is a variable; the emitter cannot narrow a call (or other
// non-identifier) subject, so it is out of the Thales subset rather than
// miscompiled. `tsc` accepts this.
function g(): string {
  return 'a';
}
function f(): string {
  // @thales-expect-error TH0086
  if (g() !== undefined) {
    return g();
  }
  return 'n';
}
console.log(f());
