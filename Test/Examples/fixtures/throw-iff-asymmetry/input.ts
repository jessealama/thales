// Validates the harness's relaxed throw-iff equivalence for @thales/prelude
// programs. `asInteger(3.14)` throws RangeError in tsx; the emitted Lean
// exits nonzero on the same input. Both sides throw → pass:both-throw.
//
// The directory name is historical: an earlier version of this fixture
// demonstrated genuine throw asymmetry. Kept for fixture-name stability.
import { asInteger } from '@thales/prelude';
console.log('before');
asInteger(3.14);
console.log('after');
