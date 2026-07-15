// Bare `undefined` in value position lowers like the `null` literal:
// argument, return, and annotated-initializer positions pin it to an
// Option type; bare console.log arguments print as in JS.
function f(o: string | undefined): number {
  if (o === undefined) {
    return 0;
  }
  return o.length;
}

function g(b: boolean): string | undefined {
  if (b) {
    return 'yes';
  }
  return undefined;
}

function h(b: boolean): string | undefined {
  return b ? 'yes' : undefined;
}

const y: string | undefined = undefined;

console.log(f(undefined));
console.log(f('hello'));
console.log(f(y));
console.log(f(h(true)));
console.log(f(h(false)));
console.log(f(true ? 'ternary' : undefined));
console.log(undefined);
console.log(null);
console.log('a', null, undefined);
