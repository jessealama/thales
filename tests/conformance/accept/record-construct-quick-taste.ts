type User = { name: string; age: bigint };
interface Point {
  x: bigint;
  y: bigint;
}

function makeUser(name: string, age: bigint): User {
  return { name, age };
}

function makePoint(x: bigint, y: bigint): Point {
  const p: Point = { x, y };
  return p;
}

const u = makeUser('ada', 36n);
const pt = makePoint(2n, 3n);
console.log(u.name);
console.log(u.age);
console.log(pt.x + pt.y);
