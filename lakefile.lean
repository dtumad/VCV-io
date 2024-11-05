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

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"

@[default_target] lean_lib VCVio

/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib

/-- Example constructions of cryptographic primitives. -/
@[default_target] lean_lib Examples

/-- Access to external C++ implementations of crypto primitives. -/
lean_lib LibSodium

/-- Implementations of specific cryptographic algorithms.
Set `precompileModules` in order to allow execution of external code. -/
lean_lib Implementations where
  precompileModules := true

-- Compiling extenal C++ files
target libsodium.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "libsodium.o"
  let srcJob ← inputTextFile <| pkg.dir / "LibSodium" / "c" / "libsodium.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace
extern_lib libleanffi pkg := do
  let ffiO ← libsodium.o.fetch
  let name := nameToStaticLib "leanlibsodium"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

-- /-- Main function for testing -/
lean_exe test where root := `Test
