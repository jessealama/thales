/**
 * @thales/prelude — refinement types for Thales.
 *
 * Four refinement types as TS aliases of `number`. tsc treats them
 * as `number`; the Thales compiler enforces the refinements via
 * dedicated diagnostics (TH0080, TH0081). The Lean-side mirror in
 * `Thales/TS/Runtime.lean` represents them as Subtypes carrying a
 * proof of the predicate.
 *
 * **Naming note.** The predicate `isInteger` here corresponds to
 * `Number.isSafeInteger`, NOT `Number.isInteger`. Our `Integer` type
 * means *safe* integer (representable exactly in IEEE 754 doubles),
 * so `isInteger(2 ** 60)` returns `false` even though `2 ** 60` is
 * mathematically an integer. Use `Number.isInteger` if you want the
 * mathematical sense — it is NOT recognized as a refinement-narrowing
 * predicate by Thales.
 */

export type Integer = number;
export type Natural = number;
export type Byte = number;
export type Bit = number;

export const isInteger = (x: number): x is Integer => Number.isSafeInteger(x);

export const isNatural = (x: number): x is Natural =>
  Number.isSafeInteger(x) && x >= 0;

export const isByte = (x: number): x is Byte =>
  Number.isSafeInteger(x) && x >= 0 && x <= 255;

export const isBit = (x: number): x is Bit => x === 0 || x === 1;

/** @throws RangeError */
export function asInteger(x: number): Integer {
  if (!isInteger(x)) throw new RangeError(`not an integer: ${x}`);
  return x;
}

/** @throws RangeError */
export function asNatural(x: number): Natural {
  if (!isNatural(x)) throw new RangeError(`not a natural: ${x}`);
  return x;
}

/** @throws RangeError */
export function asByte(x: number): Byte {
  if (!isByte(x)) throw new RangeError(`not a byte: ${x}`);
  return x;
}

/** @throws RangeError */
export function asBit(x: number): Bit {
  if (!isBit(x)) throw new RangeError(`not a bit: ${x}`);
  return x;
}
