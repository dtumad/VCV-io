import Lake
open Lake DSL

package VCVio where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Qq from git "https://github.com/leanprover-community/quote4" @ "master"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"

@[default_target]
lean_lib VCVio

lean_lib ToMathlib

-- Unused import detection, copied from mathlib
lean_exe shake where
  root := `Shake.Main
  supportInterpreter := true
