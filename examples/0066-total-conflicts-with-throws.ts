// Subset-rejected example: `@total` and `@throws` cannot both be declared
// on the same function (TH0066). `@total` is a stronger source-level claim
// — that the function always returns a value of its declared return type
// — and `@throws` directly contradicts it.

type User = { name: string; age: number };

/**
 * @total
 * @throws RangeError when age is negative
 */
// @thales-expect-error TH0066
function makeUser(name: string, age: number): User {
  if (age < 0) throw new RangeError("age must be non-negative");
  return { name, age };
}

try {
  console.log(makeUser("Alice", 30).name);
} catch (e) {
  console.log("error");
}
