import Lake
open System Lake DSL

package libsodium where
  srcDir := "."

lean_lib LibSodium

@[default_target]
lean_exe test where
  root := `Main

target libsodium.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "libsodium.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "libsodium.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

extern_lib libleanffi pkg := do
  let ffiO ← libsodium.o.fetch
  let name := nameToStaticLib "leanlibsodium"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
