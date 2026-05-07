// Fixture: throw-iff-asymmetry (post-Parcel-5)
//
// Validates the harness's relaxed throw-iff equivalence for @thales/prelude
// programs. `asInteger(3.14)` throws RangeError in tsx; Parcel 5's
// `asIntegerEffect` lowering makes the emitted Lean exit nonzero on the same
// input. Both sides throw → harness classifies as pass:both-throw.
//
// Note: the directory name predates Parcel 5, when this fixture demonstrated
// genuine asymmetry (Lean did not propagate the throw). Kept to preserve
// fixture-name stability across the v0.6 history.
import { asInteger } from "@thales/prelude";
console.log("before");
asInteger(3.14);
console.log("after");
