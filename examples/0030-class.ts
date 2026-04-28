// Subset-rejected example: class declaration (TH0030).
// @thales-expect-error TH0030
class Counter {
  count = 0;
}
console.log(new Counter().count);
