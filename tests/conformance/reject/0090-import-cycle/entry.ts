// @thales-expect-error TH0090
import { a } from './a';
export function b(): bigint {
  return 1n;
}
console.log(a());
