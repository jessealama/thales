const warning = `
  // @thales-expect-error TH0001 (template literal; must not register)
`;
let x = 0;
// @thales-expect-error TH0001
x = 1;
console.log(warning);
