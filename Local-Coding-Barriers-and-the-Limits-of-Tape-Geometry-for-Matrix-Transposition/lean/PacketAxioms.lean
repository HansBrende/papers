-- Generated audit of every declaration in the additive packet modules.
-- This is verification tooling, not a mathematical axiom or proof source.
import Lean
import TransposeFollowup.ConditionalCoordinateEntropy
import TransposeFollowup.ConditionalEntropyFibers
import TransposeFollowup.ConditionalObservation
import TransposeFollowup.CoordinatePackets
import TransposeFollowup.DisjointFamilyCount
import TransposeFollowup.DistanceNumerics
import TransposeFollowup.FractionalIndependentCover
import TransposeFollowup.HelperPacketAveraging
import TransposeFollowup.HelperPacketDegreeBound
import TransposeFollowup.HelperRobustPacketBound
import TransposeFollowup.InverseLocalPackets
import TransposeFollowup.InverseRowBank
import TransposeFollowup.PacketCollisionCube
import TransposeFollowup.PacketComponentCount
import TransposeFollowup.PacketComponentViews
import TransposeFollowup.PacketDemandViews
import TransposeFollowup.PacketDistanceBound
import TransposeFollowup.PacketDistanceConsequences
import TransposeFollowup.PacketInformation
import TransposeFollowup.PacketRobustNumerics
import TransposeFollowup.RecodedPackets
import TransposeFollowup.RobustPacketBound
import TransposeFollowup.SharedDemandEntropy
import TransposeFollowup.TotalCorrelation
import TransposeFollowup.WeightedSubmodularCover

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`TransposeFollowup.ConditionalCoordinateEntropy, `TransposeFollowup.ConditionalEntropyFibers, `TransposeFollowup.ConditionalObservation, `TransposeFollowup.CoordinatePackets, `TransposeFollowup.DisjointFamilyCount, `TransposeFollowup.DistanceNumerics, `TransposeFollowup.FractionalIndependentCover, `TransposeFollowup.HelperPacketAveraging, `TransposeFollowup.HelperPacketDegreeBound, `TransposeFollowup.HelperRobustPacketBound, `TransposeFollowup.InverseLocalPackets, `TransposeFollowup.InverseRowBank, `TransposeFollowup.PacketCollisionCube, `TransposeFollowup.PacketComponentCount, `TransposeFollowup.PacketComponentViews, `TransposeFollowup.PacketDemandViews, `TransposeFollowup.PacketDistanceBound, `TransposeFollowup.PacketDistanceConsequences, `TransposeFollowup.PacketInformation, `TransposeFollowup.PacketRobustNumerics, `TransposeFollowup.RecodedPackets, `TransposeFollowup.RobustPacketBound, `TransposeFollowup.SharedDemandEntropy, `TransposeFollowup.TotalCorrelation, `TransposeFollowup.WeightedSubmodularCover]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut actual : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx]! then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Forbidden axiom {ax} in {name}"
          if !actual.contains ax then actual := actual.push ax
        count := count + 1
  if count == 0 then throwError "Empty packet declaration audit"
  logInfo m!"Packet declaration audit: {count} declarations; axioms {actual}"
