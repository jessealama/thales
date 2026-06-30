// Top-level while (issue #49): accepted; loop body never runs, prints nothing.
while (false) {
  console.log('unreachable');
}
