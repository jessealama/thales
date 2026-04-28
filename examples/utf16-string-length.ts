// @thales-skip-runtime JS UTF-16 `"😀".length` is 2; Lean scalar count is 1.
function greetingLen(): number {
  return "😀".length;
}

const main = (): number => greetingLen();
console.log(main());
