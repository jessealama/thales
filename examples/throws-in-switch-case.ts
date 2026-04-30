// Pins the exhaustive-walk requirement: a direct `throw` inside a
// switch case must produce TH0060 when the enclosing function lacks
// `@throws`. The pre-rewrite `collectUncaughtCalls` had a catchall
// that silently skipped `switchStmt`.

function classify(x: number): string {
  switch (x) {
    case 0:
      return 'zero';
    case 1:
      // @thales-expect-error TH0060
      throw new RangeError('one is forbidden');
    default:
      return 'other';
  }
}

console.log(classify(0));
