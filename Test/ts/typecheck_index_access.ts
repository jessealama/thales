type Config = {
  [key: string]: boolean | { prop: string };
};

declare const config: Config;
// Index signature fallback: any property access returns the value type
let x = config.works;

// Direct property should still take precedence over index signature
type Named = {
  name: string;
  [key: string]: string;
};

declare const named: Named;
let n: string = named.name;       // direct property match
let other: string = named.other;  // index signature fallback
