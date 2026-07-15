// PARKED: TH0081 for class property initializer context.
// Classes v1 (#106) rejects field initializers outright (TH0097 fires
// before the refinement check can see the initializer), so the TH0081
// initializer context stays unreachable.
class Container {
  // @thales-expect-error TH0097
  value: import('@thales/prelude').Integer = 5 as number;
}
console.log(new Container().value);
