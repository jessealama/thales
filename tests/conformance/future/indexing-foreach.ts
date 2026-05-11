// PARKED: forEach callback indexing. Once the callback's `i` is typed
// `Natural`, `arr[i]` inside should lift from `T | undefined` to `T`.
// Today the index is plain `number` so the result stays optional.
const arr = [10, 20, 30];
arr.forEach((element, i) => {
  console.log(i, element, arr[i]);
});
