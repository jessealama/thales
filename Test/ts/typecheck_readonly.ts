interface TestEdit {
  caption: string;
  args?: readonly string[];
}

declare const edit: TestEdit;
let c: string = edit.caption;
