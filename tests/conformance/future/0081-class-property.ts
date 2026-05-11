// PARKED: TH0081 for class property initializer context.
// Classes are not in the Thales subset (TH0030), so this context
// is unreachable until classes are supported.
// @thales-expect-error TH0030
class Container {
  // @thales-expect-error TH0081
  value: import('@thales/prelude').Integer = 5 as number;
}
console.log(new Container().value);
