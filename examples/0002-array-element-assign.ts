// Subset-rejected example: array element assignment (TH0002).
const arr = [1, 2, 3];
// @thales-expect-error TH0002
arr[0] = 99;
console.log(arr);
