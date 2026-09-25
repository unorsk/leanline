import Lake
open System Lake DSL

package leanline where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-! The only native code: a small POSIX shim (termios, poll, signals). -/

input_file ffiSrc where
  path := "c" / "leanline_ffi.c"
  text := true

target ffiObj pkg : FilePath := do
  let src ← ffiSrc.fetch
  let oFile := pkg.buildDir / "c" / "leanline_ffi.o"
  let leanInclude ← getLeanIncludeDir
  -- The system C compiler is used because the toolchain's bundled clang ships
  -- without libc headers.
  buildO oFile src #["-I", leanInclude.toString] #["-fPIC", "-O2", "-Wall"] "cc"

target ffiLib pkg : FilePath := do
  let obj ← ffiObj.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanline_ffi") #[obj]

@[default_target]
lean_lib Leanline where
  moreLinkObjs := #[ffiLib]

/-- Theorems about the library. Building this target checks every proof. -/
@[default_target]
lean_lib LeanlineTests where
  globs := #[.submodules `LeanlineTests]

/-- Interactive demonstration of the library. -/
@[default_target]
lean_exe «leanline-demo» where
  root := `Examples.Demo
