// PARKED: P3 forEach callback indexing — deferred to Parcel 6.
// When P3 ships, the callback's index parameter will be typed Natural,
// and arr[i] inside the callback will be lifted from T | undefined to T.
//
// Until Parcel 6: the callback's i is typed 'number', so arr[i] inside
// stays T | undefined (the P2 conservative baseline).
const arr = [10, 20, 30];
arr.forEach((element, i) => {
  console.log(i, element, arr[i]);
});
