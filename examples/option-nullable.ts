function findName(id: string): string | null {
  if (id === "1") {
    return "Alice";
  }
  return null;
}

function describe(name: string | null): string {
  if (name === null) return "no name found";
  return "found a name";
}

const n1: string | null = findName("1");
const n2: string | null = findName("2");
console.log(describe(n1));
console.log(describe(n2));
