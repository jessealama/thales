// Subset-rejected example: type-level programming via conditional types (TH0024).
// @thales-expect-error TH0024
type IsNumber<T> = T extends number ? true : false;
const flag: IsNumber<number> = true;
console.log(flag);
