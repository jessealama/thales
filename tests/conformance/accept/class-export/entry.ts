import { Point, originPlus } from './geom';

const p = new Point(3n, -4n);
const q = originPlus(1n, 2n);
console.log(p.norm1());
console.log(p.translate(1n, 1n).x, q.x, q.y);
