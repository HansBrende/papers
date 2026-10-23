-- Generated audit of every declaration in the additive proof modules.
-- This is verification tooling, not a mathematical axiom or proof source.
import Lean
import TransposeFollowup.AdaptiveBankHelper
import TransposeFollowup.AdaptiveBankNumerics
import TransposeFollowup.AdaptiveBankProtocol
import TransposeFollowup.AdaptiveBankRate
import TransposeFollowup.AdaptiveBankRateLimit
import TransposeFollowup.AdaptiveBankRefinement
import TransposeFollowup.AdaptiveBankStrategy
import TransposeFollowup.AdaptiveBankTranscript
import TransposeFollowup.AdaptiveForestAsymptotics
import TransposeFollowup.AdaptiveForestBound
import TransposeFollowup.AdaptiveForestCount
import TransposeFollowup.AdaptiveForestHelperBound
import TransposeFollowup.AdaptiveForestLaw
import TransposeFollowup.AdaptiveForestLeaf
import TransposeFollowup.AdaptiveForestLevels
import TransposeFollowup.AdaptiveForestPaths
import TransposeFollowup.AdaptiveForestRangeBound
import TransposeFollowup.AdaptiveForestRate
import TransposeFollowup.AdaptiveForestRefinement
import TransposeFollowup.AdaptiveForestRows
import TransposeFollowup.AdaptiveForestStrategyBound
import TransposeFollowup.ConditionalCoordinateEntropy
import TransposeFollowup.ConditionalEntropyFibers
import TransposeFollowup.ConditionalObservation
import TransposeFollowup.CoordinatePackets
import TransposeFollowup.DisjointFamilyCount
import TransposeFollowup.DistanceNumerics
import TransposeFollowup.ExpanderShear
import TransposeFollowup.ExpanderShearClock
import TransposeFollowup.ExpanderShearClockProduct
import TransposeFollowup.ExpanderShearCut
import TransposeFollowup.ExpanderShearEncoding
import TransposeFollowup.ExpanderShearFamily
import TransposeFollowup.ExpanderShearGraph
import TransposeFollowup.ExpanderShearLocal
import TransposeFollowup.ExpanderShearNativeBridge
import TransposeFollowup.ExpanderShearNativeFamily
import TransposeFollowup.ExpanderShearOpcodeBridge
import TransposeFollowup.ExpanderShearRank
import TransposeFollowup.ExpanderShearRationalBridge
import TransposeFollowup.ExpanderShearRowStream
import TransposeFollowup.ExpanderShearSupport
import TransposeFollowup.FractionalIndependentCover
import TransposeFollowup.FullFiberAveraging
import TransposeFollowup.FullFiberEntropy
import TransposeFollowup.GapBank
import TransposeFollowup.GapBankBucketEntropy
import TransposeFollowup.GapBankBuckets
import TransposeFollowup.GapBankGroupedGeometry
import TransposeFollowup.GapBankGroups
import TransposeFollowup.GapBankInformation
import TransposeFollowup.GapBankLeafEntropy
import TransposeFollowup.GapBankNear
import TransposeFollowup.GapBankStateRange
import TransposeFollowup.HelperPacketAveraging
import TransposeFollowup.HelperPacketDegreeBound
import TransposeFollowup.HelperRobustPacketBound
import TransposeFollowup.InverseLocalPackets
import TransposeFollowup.InverseRowBank
import TransposeFollowup.MatchingXorMasksSemantics
import TransposeFollowup.MatchingXorStream
import TransposeFollowup.NativeExpanderShear
import TransposeFollowup.NativeExpanderShearCalls
import TransposeFollowup.NativeExpanderShearFrames
import TransposeFollowup.NativeExpanderShearGenerate
import TransposeFollowup.NativeExpanderShearHalf
import TransposeFollowup.NativeExpanderShearLoad
import TransposeFollowup.NativeExpanderShearMachine
import TransposeFollowup.NativeExpanderShearMetadata
import TransposeFollowup.NativeExpanderShearMetadataInterface
import TransposeFollowup.NativeExpanderShearNumerics
import TransposeFollowup.NativeExpanderShearPrepare
import TransposeFollowup.NativeExpanderShearSemantics
import TransposeFollowup.NativeExpanderShearTagBank
import TransposeFollowup.NativeMatchingXorClose
import TransposeFollowup.NativeMatchingXorData
import TransposeFollowup.NativeMatchingXorMaskLayout
import TransposeFollowup.NativeMatchingXorMaskRow
import TransposeFollowup.NativeMatchingXorMasks
import TransposeFollowup.NativeMatchingXorOutput
import TransposeFollowup.NativeMatchingXorPage
import TransposeFollowup.NativeMatchingXorPageReset
import TransposeFollowup.NativeMatchingXorPages
import TransposeFollowup.NativeMatchingXorPayload
import TransposeFollowup.NativeMatchingXorPrefixRewind
import TransposeFollowup.NativeMatchingXorReset
import TransposeFollowup.NativeMatchingXorTagStream
import TransposeFollowup.NativeMatchingXorTags
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
import TransposeFollowup.ShearGap
import TransposeFollowup.ShearGapEntropy
import TransposeFollowup.ShearGapRecovery
import TransposeFollowup.ShearGapRecoveryRanges
import TransposeFollowup.TotalCorrelation
import TransposeFollowup.WeightedSubmodularCover

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`TransposeFollowup.AdaptiveBankHelper, `TransposeFollowup.AdaptiveBankNumerics, `TransposeFollowup.AdaptiveBankProtocol, `TransposeFollowup.AdaptiveBankRate, `TransposeFollowup.AdaptiveBankRateLimit, `TransposeFollowup.AdaptiveBankRefinement, `TransposeFollowup.AdaptiveBankStrategy, `TransposeFollowup.AdaptiveBankTranscript, `TransposeFollowup.AdaptiveForestAsymptotics, `TransposeFollowup.AdaptiveForestBound, `TransposeFollowup.AdaptiveForestCount, `TransposeFollowup.AdaptiveForestHelperBound, `TransposeFollowup.AdaptiveForestLaw, `TransposeFollowup.AdaptiveForestLeaf, `TransposeFollowup.AdaptiveForestLevels, `TransposeFollowup.AdaptiveForestPaths, `TransposeFollowup.AdaptiveForestRangeBound, `TransposeFollowup.AdaptiveForestRate, `TransposeFollowup.AdaptiveForestRefinement, `TransposeFollowup.AdaptiveForestRows, `TransposeFollowup.AdaptiveForestStrategyBound, `TransposeFollowup.ConditionalCoordinateEntropy, `TransposeFollowup.ConditionalEntropyFibers, `TransposeFollowup.ConditionalObservation, `TransposeFollowup.CoordinatePackets, `TransposeFollowup.DisjointFamilyCount, `TransposeFollowup.DistanceNumerics, `TransposeFollowup.ExpanderShear, `TransposeFollowup.ExpanderShearClock, `TransposeFollowup.ExpanderShearClockProduct, `TransposeFollowup.ExpanderShearCut, `TransposeFollowup.ExpanderShearEncoding, `TransposeFollowup.ExpanderShearFamily, `TransposeFollowup.ExpanderShearGraph, `TransposeFollowup.ExpanderShearLocal, `TransposeFollowup.ExpanderShearNativeBridge, `TransposeFollowup.ExpanderShearNativeFamily, `TransposeFollowup.ExpanderShearOpcodeBridge, `TransposeFollowup.ExpanderShearRank, `TransposeFollowup.ExpanderShearRationalBridge, `TransposeFollowup.ExpanderShearRowStream, `TransposeFollowup.ExpanderShearSupport, `TransposeFollowup.FractionalIndependentCover, `TransposeFollowup.FullFiberAveraging, `TransposeFollowup.FullFiberEntropy, `TransposeFollowup.GapBank, `TransposeFollowup.GapBankBucketEntropy, `TransposeFollowup.GapBankBuckets, `TransposeFollowup.GapBankGroupedGeometry, `TransposeFollowup.GapBankGroups, `TransposeFollowup.GapBankInformation, `TransposeFollowup.GapBankLeafEntropy, `TransposeFollowup.GapBankNear, `TransposeFollowup.GapBankStateRange, `TransposeFollowup.HelperPacketAveraging, `TransposeFollowup.HelperPacketDegreeBound, `TransposeFollowup.HelperRobustPacketBound, `TransposeFollowup.InverseLocalPackets, `TransposeFollowup.InverseRowBank, `TransposeFollowup.MatchingXorMasksSemantics, `TransposeFollowup.MatchingXorStream, `TransposeFollowup.NativeExpanderShear, `TransposeFollowup.NativeExpanderShearCalls, `TransposeFollowup.NativeExpanderShearFrames, `TransposeFollowup.NativeExpanderShearGenerate, `TransposeFollowup.NativeExpanderShearHalf, `TransposeFollowup.NativeExpanderShearLoad, `TransposeFollowup.NativeExpanderShearMachine, `TransposeFollowup.NativeExpanderShearMetadata, `TransposeFollowup.NativeExpanderShearMetadataInterface, `TransposeFollowup.NativeExpanderShearNumerics, `TransposeFollowup.NativeExpanderShearPrepare, `TransposeFollowup.NativeExpanderShearSemantics, `TransposeFollowup.NativeExpanderShearTagBank, `TransposeFollowup.NativeMatchingXorClose, `TransposeFollowup.NativeMatchingXorData, `TransposeFollowup.NativeMatchingXorMaskLayout, `TransposeFollowup.NativeMatchingXorMaskRow, `TransposeFollowup.NativeMatchingXorMasks, `TransposeFollowup.NativeMatchingXorOutput, `TransposeFollowup.NativeMatchingXorPage, `TransposeFollowup.NativeMatchingXorPageReset, `TransposeFollowup.NativeMatchingXorPages, `TransposeFollowup.NativeMatchingXorPayload, `TransposeFollowup.NativeMatchingXorPrefixRewind, `TransposeFollowup.NativeMatchingXorReset, `TransposeFollowup.NativeMatchingXorTagStream, `TransposeFollowup.NativeMatchingXorTags, `TransposeFollowup.PacketCollisionCube, `TransposeFollowup.PacketComponentCount, `TransposeFollowup.PacketComponentViews, `TransposeFollowup.PacketDemandViews, `TransposeFollowup.PacketDistanceBound, `TransposeFollowup.PacketDistanceConsequences, `TransposeFollowup.PacketInformation, `TransposeFollowup.PacketRobustNumerics, `TransposeFollowup.RecodedPackets, `TransposeFollowup.RobustPacketBound, `TransposeFollowup.SharedDemandEntropy, `TransposeFollowup.ShearGap, `TransposeFollowup.ShearGapEntropy, `TransposeFollowup.ShearGapRecovery, `TransposeFollowup.ShearGapRecoveryRanges, `TransposeFollowup.TotalCorrelation, `TransposeFollowup.WeightedSubmodularCover]
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
