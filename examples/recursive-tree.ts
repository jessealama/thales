type Tree =
  | { kind: "leaf" }
  | { kind: "node"; left: Tree; right: Tree; value: bigint };

function sum(t: Tree): bigint {
  switch (t.kind) {
    case "leaf": return 0n;
    case "node": return t.value + sum(t.left) + sum(t.right);
  }
}

const tree: Tree = {
  kind: "node",
  left: { kind: "node", left: { kind: "leaf" }, right: { kind: "leaf" }, value: 2n },
  right: { kind: "node", left: { kind: "leaf" }, right: { kind: "leaf" }, value: 3n },
  value: 1n
};

const main = (): bigint => sum(tree);
console.log(main());
