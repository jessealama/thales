import Lake
open Lake DSL

package «thales» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
require Regex from git "https://github.com/pandaman64/lean-regex" @ "v4.29.0" / "regex"

lean_lib «Thales» where
  globs := #[.submodules `Thales]

-- The runtime library imported by emitted Lean code. Built as a default
-- target so a fresh `lake build` produces its `.olean` alongside the exe.
@[default_target]
lean_lib «ThalesRuntime» where
  roots := #[`Thales.TS.Runtime]

@[default_target]
lean_exe «thales» where
  root := `Thales.Main

lean_lib «ThalesTest» where
  globs := #[.submodules `Test]
