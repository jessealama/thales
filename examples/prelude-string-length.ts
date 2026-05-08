// Demonstrates string.length typed as Natural — always non-negative.
import { Natural } from '@thales/prelude';

const greeting = 'hello';
const len: Natural = greeting.length; // Natural, not number
console.log(len);
