// Var hoisting tests — this file should type-check cleanly (no errors)

// Basic: var used before declaration
function basicHoist(): void {
  console.log(x);
  var x = 1;
}

// Nested: var inside if block is visible at function level
function nestedHoist(): void {
  if (true) {
    var y = 2;
  }
  console.log(y);
}

// For loop: var in for init is hoisted
function forHoist(): void {
  for (var i = 0; i < 10; i = i + 1) {
    console.log(i);
  }
  console.log(i);
}

// Try-catch: var in try block is visible outside
function tryHoist(): void {
  try {
    var z = 3;
  } catch (err) {
    var w = 4;
  }
  console.log(z);
  console.log(w);
}

basicHoist();
nestedHoist();
forHoist();
tryHoist();
