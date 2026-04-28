type NatList =
  | { kind: "nil" }
  | { kind: "cons"; head: bigint; tail: NatList };

/** @total */
function sum(xs: NatList): bigint {
  switch (xs.kind) {
    case "nil": return 0n;
    case "cons": return xs.head + sum(xs.tail);
  }
}

const myList: NatList = {
  kind: "cons", head: 1n,
  tail: { kind: "cons", head: 2n,
    tail: { kind: "cons", head: 3n,
      tail: { kind: "nil" } } }
};

console.log(sum(myList));
