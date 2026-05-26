import { Bit, Byte, isBit, isByte } from '@thales/prelude';
const x = 1;
if (isByte(x)) {
  const y: Byte = x;
  console.log(y === 1);
  if (isBit(x)) {
    const z: Bit = x;
    console.log(z === 1);
  }
}
