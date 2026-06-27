// Subset-rejected example: regex literals are not supported (TH0091).
// @thales-expect-error TH0091
const re = /abc/g;
console.log(re.test('abc'));
