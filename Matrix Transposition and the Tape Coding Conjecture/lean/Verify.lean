import Lean
import Transpose.Statement
import Transpose.Answer

/-!
# Final check — DO NOT MODIFY THIS FILE

Run from the `lean/` directory, after `lake build`:

    lake env lean Verify.lean

It succeeds only if `Transpose.answer` is a theorem whose type is *exactly*
`Transpose.LinearTimeTransposable` or `¬ Transpose.LinearTimeTransposable`
(as defined in the frozen `Transpose/Statement.lean`), and its proof uses no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`. In particular a
proof containing `sorry`, `native_decide` or a new `axiom` is rejected.

Every declaration that does not ship with the Lean toolchain (including all of
Mathlib, if it is a dependency) is re-checked by the kernel from scratch, so
declarations added without kernel checking (e.g. via `debug.skipKernelTC` or a
raw `addDecl`) are caught. With Mathlib this re-check can take a long time.
-/


open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some ci := env.find? `Transpose.answer
    | throwError "FAIL: `Transpose.answer` not found"
  unless ci matches .thmInfo _ do
    throwError "FAIL: `Transpose.answer` is not a theorem"
  let pos := mkConst ``Transpose.LinearTimeTransposable
  let neg := mkApp (mkConst ``Not) pos
  let verdict ←
    if ci.type == pos then
      pure "statement (T) is TRUE: linear-time transposition is possible"
    else if ci.type == neg then
      pure "statement (T) is FALSE: linear-time transposition is impossible"
    else
      throwError m!"FAIL: `Transpose.answer` has unexpected type {ci.type}"
  -- Re-check, with the kernel and from scratch, every declaration that does
  -- not come from the Lean toolchain itself (defeats `debug.skipKernelTC`
  -- and any other way of adding unchecked declarations to the environment).
  let libDir := (← findSysroot) / "lib" / "lean"
  let mods := env.header.moduleNames
  let mut tc : NameSet := {}
  for m in mods do
    if (← findOLean m).toString.startsWith (libDir.toString ++ "/") then tc := tc.insert m
  let isToolchain (m : Name) : Bool := tc.contains m
  let mods := env.header.moduleNames
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (n, c) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      unless isToolchain mods[idx.toNat]! do
        newConsts := newConsts.insert n c
  let base ← importModules (mods.filter isToolchain |>.map ({ module := · })) {}
  let kenv ← base.toKernelEnv.replay newConsts
  let some ci' := kenv.find? `Transpose.answer
    | throwError "FAIL: `Transpose.answer` was not replayed"
  unless ci'.type == ci.type do throwError "FAIL: replayed type differs"
  let axs ← collectAxioms `Transpose.answer
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError m!"FAIL: disallowed axioms used: {bad}"
  logInfo m!"VERIFIED: {verdict}. Axioms used: {axs}. Re-checked {newConsts.size} declarations."
