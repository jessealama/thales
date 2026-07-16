// Subset-rejected example: forward references to later top-level
// declarations (TH0105). tsc accepts both shapes (hoisted declarations
// are visible throughout their scope), but emitted Lean declarations
// appear in source order, so the references would not elaborate.
function caller(): bigint {
  // @thales-expect-error TH0105
  return helper() + 1n;
}
function helper(): bigint {
  return 41n;
}
class User {
  readonly id: bigint;
  constructor(id: bigint) {
    this.id = id;
  }
}
function makeUser(): User {
  // @thales-expect-error TH0105
  return new Later(7n).u;
}
class Later {
  readonly u: User;
  constructor(id: bigint) {
    this.u = new User(id);
  }
}
console.log(caller());
console.log(makeUser().id);
