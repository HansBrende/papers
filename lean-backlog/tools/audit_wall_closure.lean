import MatrixCoding.Wall
import Lean

/-!
# Import and kernel audit of the conditional wall theorem

Run with `audit_wall_closure.py` in the pinned package environment. This
mirrors the imported-declaration selection and replay in the frozen
`Verify.lean`, but checks ONLY the conditional theorem already imported
from `Wall`. It does not define `Transpose.answer` or assert `Conjecture`.

The replay API skips unsafe and partial constants; both the selected count
and the eligible count are reported. The frozen checker's axiom whitelist
is target-transitive, not a blanket ban on unused imported axioms. This
optional `WALL_ALL_AXIOMS=1` diagnostic scans every selected declaration's
recorded axiom closure and reports exceptions without treating them as target uses.

Module paths are local runtime diagnostics: keep the raw output outside
public source files. `WALL_REPLAY=1` requests the fresh-kernel replay.
-/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let start ← IO.monoMsNow
  let progress := fun (stage : String) => do
    if let some path ← IO.getEnv "WALL_AUDIT_PROGRESS" then
      IO.FS.writeFile path s!"{stage} elapsed_ms={(← IO.monoMsNow)-start}"
  progress "inventory_start"
  let env ← getEnv
  let libDir := (← findSysroot) / "lib" / "lean"
  let mods := env.header.moduleNames
  let mut tc : NameSet := {}
  let mut paths : Array String := #[]
  for m in mods do
    let p ← findOLean m
    paths := paths.push p.toString
    if p.toString.startsWith (libDir.toString ++ "/") then tc := tc.insert m
  let isToolchain (m : Name) : Bool := tc.contains m
  let mut counts := Array.replicate mods.size (0 : Nat)
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut axNames : Array String := #[]
  for (n, c) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      counts := counts.modify idx.toNat (· + 1)
      unless isToolchain mods[idx.toNat]! do
        newConsts := newConsts.insert n c
        if c matches .axiomInfo _ then
          axNames := axNames.push n.toString
  for i in [:mods.size] do
    IO.println <| "MODULE " ++ (Json.mkObj [
      ("name", toJson mods[i]!.toString), ("olean", toJson paths[i]!),
      ("toolchain", toJson (isToolchain mods[i]!)),
      ("declarations", toJson counts[i]!)]).compress
  IO.println <| "AXIOMS " ++ (toJson axNames).compress
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let eligible := newConsts.toList.countP (fun (_, c) => !c.isUnsafe && !c.isPartial)
  progress s!"inventory_done selected={newConsts.size} eligible={eligible}"
  if (← IO.getEnv "WALL_ALL_AXIOMS") == some "1" then
    progress "all_axioms_start"
    let mut exceptions : Array Json := #[]
    for (n, _) in newConsts.toList do
      let axs ← collectAxioms n
      let bad := axs.filter (fun a => !allowed.contains a)
      unless bad.isEmpty do
        exceptions := exceptions.push <| Json.mkObj [
          ("name", toJson n.toString), ("axioms", toJson (bad.map toString))]
    IO.println <| "ALL_AXIOM_EXCEPTIONS " ++ (toJson exceptions).compress
    progress "all_axioms_done"
  let name := ``LeanBacklog.Wall.excludes_adaptive
  let some ci := env.find? name | throwError "conditional theorem missing"
  unless ci matches .thmInfo _ do throwError "conditional target is not a theorem"
  match ci.type with
  | .forallE _ a b _ =>
      unless a == mkConst ``LeanBacklog.Wall.Conjecture &&
          b == mkApp (mkConst ``Not) (mkConst ``Transpose.LinearTimeTransposable) do
        throwError "conditional target has unexpected type"
  | _ => throwError "conditional target has unexpected type"
  let axs ← collectAxioms name
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do throwError m!"disallowed target axioms {bad}"
  IO.println <| "TARGET_AXIOMS " ++ (toJson (axs.map toString)).compress
  IO.println <| "INVENTORY " ++ (Json.mkObj [
    ("modules", toJson mods.size), ("non_toolchain_declarations", toJson newConsts.size),
    ("eligible_declarations", toJson eligible),
    ("answer_present", toJson (env.find? `Transpose.answer).isSome),
    ("inventory_ms", toJson ((← IO.monoMsNow)-start))]).compress
  if (← IO.getEnv "WALL_REPLAY") == some "1" then
    let before ← IO.monoMsNow
    IO.println s!"REPLAY_START {newConsts.size}"
    progress "toolchain_base_start"
    let base ← importModules (mods.filter isToolchain |>.map ({ module := · })) {}
    progress "kernel_replay_start"
    let kenv ← base.toKernelEnv.replay newConsts
    progress "kernel_replay_done"
    let some ci' := kenv.find? name | throwError "conditional theorem was not replayed"
    unless ci'.type == ci.type do throwError "replayed type differs"
    IO.println <| "REPLAY_PASS " ++ (Json.mkObj [
      ("selected_declarations", toJson newConsts.size),
      ("eligible_declarations", toJson eligible),
      ("milliseconds", toJson ((← IO.monoMsNow)-before))]).compress
