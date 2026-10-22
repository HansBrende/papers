-- Generated verification tooling, not a mathematical proof source.
import Lean
import TransposeFollowup.DisjointFamilyCount
import TransposeFollowup.DistanceNumerics
import TransposeFollowup.SubmodularCover
import TransposeFollowup.XorComponentCount
import TransposeFollowup.XorDegreeBound
import TransposeFollowup.XorPathCycleBound

open Lean Elab Command

private def eraseContractBinderLabels : Expr → Expr
  | .forallE _ a b i => .forallE Name.anonymous (eraseContractBinderLabels a) (eraseContractBinderLabels b) i
  | .lam _ a b i => .lam Name.anonymous (eraseContractBinderLabels a) (eraseContractBinderLabels b) i
  | .letE _ t v b n => .letE Name.anonymous (eraseContractBinderLabels t) (eraseContractBinderLabels v) (eraseContractBinderLabels b) n
  | .app f a => .app (eraseContractBinderLabels f) (eraseContractBinderLabels a)
  | .mdata m e => .mdata m (eraseContractBinderLabels e)
  | .proj s i e => .proj s i (eraseContractBinderLabels e)
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[`TransposeFollowup.RecodedXorCode.broadcast_bound_of_ball_budget, `TransposeFollowup.RecodedXorCode.broadcast_bound_of_ball_budget_real, `TransposeFollowup.RecodedXorCode.broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.broadcast_lower_bound_scaled, `TransposeFollowup.RecodedXorCode.cycle_broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.cycle_embedding_broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.degree_broadcast_bound_scaled, `TransposeFollowup.RecodedXorCode.degree_broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.fixed_degree_broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.linear_ball_broadcast_bound_nat, `TransposeFollowup.RecodedXorCode.linear_ball_broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.linear_ball_error_le_sqrt, `TransposeFollowup.RecodedXorCode.path_broadcast_lower_bound, `TransposeFollowup.RecodedXorCode.small_component_count_le_near, `TransposeFollowup.RecodedXorCode.subcycle_broadcast_lower_bound, `TransposeFollowup.XorSystem.components_disjoint, `TransposeFollowup.XorSystem.mem_smallComponents, `TransposeFollowup.XorSystem.smallComponents, `TransposeFollowup.XorSystem.smallComponents_disjoint, `TransposeFollowup.XorSystem.unanchored_disjoint, `TransposeFollowup.XorSystem.unanchored_nonempty, `TransposeFollowup.XorSystem.unanchored_size_bound, `TransposeFollowup.disjoint_family_size_bound, `TransposeFollowup.half_log_power_budget, `TransposeFollowup.log_le_twice_half_log, `TransposeFollowup.submodular_cover]
  let modules : Array Name := #[`TransposeFollowup.DisjointFamilyCount, `TransposeFollowup.DistanceNumerics, `TransposeFollowup.SubmodularCover, `TransposeFollowup.XorComponentCount, `TransposeFollowup.XorDegreeBound, `TransposeFollowup.XorPathCycleBound]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut checked : Array String := #[]
  let mut actual : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx]! then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do throwError "Forbidden axiom {ax} in {name}"
          if !actual.contains ax then actual := actual.push ax
        checked := checked.push name.toString
  for name in names do
    let some info := env.find? name | throwError "Missing original declaration {name}"
    rows := rows.push (Json.mkObj [("name", toJson name.toString),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("type", toJson (reprStr (eraseContractBinderLabels info.type)))])
  if checked.isEmpty then throwError "Empty proof-refactor axiom audit"
  logInfo ("PROOF_REFACTOR_AUDIT " ++ (Json.mkObj [("types", Json.arr rows),
    ("axiom_declarations", toJson checked), ("axioms", toJson (actual.map Name.toString))]).compress)
