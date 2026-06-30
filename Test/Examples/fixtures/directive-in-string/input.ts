const warning = `
  // @thales-expect-error TH0003 (template literal; must not register)
`;
const o = { a: 0 };
// @thales-expect-error TH0003
o.a = 1;
console.log(warning);
