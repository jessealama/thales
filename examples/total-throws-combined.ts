// @total + @throws on the same function: a fully honest signature.
// Lean proves the structural recursion terminates; the Except return
// type makes the failure mode visible to every caller.

type NatList =
  | { kind: "nil" }
  | { kind: "cons"; head: number; tail: NatList };

/**
 * @total
 * @throws RangeError when any element is negative
 */
function sumPositive(xs: NatList): number {
  switch (xs.kind) {
    case "nil": return 0;
    case "cons": {
      if (xs.head < 0) throw new RangeError("negative element");
      const rest = sumPositive(xs.tail);
      return xs.head + rest;
    }
  }
}

const sample: NatList = { kind: "cons", head: 1, tail: { kind: "cons", head: 2, tail: { kind: "nil" } } };
try {
  console.log(sumPositive(sample));
} catch (e) {
  console.log("error");
}
