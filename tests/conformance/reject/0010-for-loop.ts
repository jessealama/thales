// Subset-rejected example: module-level while loop (TH0010). Loops are
// only admitted inside do-mode-lowerable declared functions (#26 admits
// while/do-while there); at module level every loop stays rejected.
// @thales-expect-error TH0010
while (false) {
  console.log('unreachable');
}
