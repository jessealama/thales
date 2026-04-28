// Thales-TS v1 prelude. Types only; runtime comes from Thales.TS.Runtime.
// This file declares the surface types Thales-TS programs use. It is
// intentionally minimal: the full standard library is v6+.

export type Option<T> =
  | { readonly tag: "some"; readonly value: T }
  | { readonly tag: "none" };

export type Result<T, E> =
  | { readonly ok: true; readonly value: T }
  | { readonly ok: false; readonly error: E };

export declare function some<T>(value: T): Option<T>;
export declare function none<T>(): Option<T>;
export declare function ok<T, E>(value: T): Result<T, E>;
export declare function err<T, E>(error: E): Result<T, E>;
