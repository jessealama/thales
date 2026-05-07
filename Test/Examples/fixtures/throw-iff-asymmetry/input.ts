// Fixture: throw-iff-asymmetry
//
// Demonstrates the harness detecting throw asymmetry for @thales/prelude-importing
// programs. asInteger(3.14) throws in tsx (RangeError) but the emitted Lean
// does not yet propagate the throw to a non-zero exit (Parcel 5 will fix this).
//
// Expected outcome until Parcel 5 ships: fail:throw-asymmetry (tsx exits 1,
// Lean exits 0). Update to pass:both-throw once Parcel 5 emit is in place.
import { asInteger } from "@thales/prelude";
console.log("before");
asInteger(3.14);
console.log("after");
