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

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
require aesop from git "https://github.com/leanprover-community/aesop" @ "master"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"

-- Main folder for crypto-specific constructions and definitions
@[default_target] lean_lib VCVio

-- Seperate section of the project for things that should be ported
lean_lib ToMathlib

-- Unused import detection, copied from mathlib
lean_exe shake where
  root := `Shake.Main
  supportInterpreter := true
