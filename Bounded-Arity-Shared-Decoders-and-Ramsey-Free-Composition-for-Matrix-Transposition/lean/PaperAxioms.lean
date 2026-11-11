import BoundedArityDecoders

/-!
# Formal Specification & Axiom Audit (`PaperAxioms.lean`)

Typechecks and prints axiom dependencies of every formal specification declaration across all
six modules of `BoundedArityDecoders`.
-/

namespace BoundedArityDecoders

-- Part I: Bounded-Arity Arbitrary-Set Shared-Decoder Capacity
#check @SelfReferentialAndCleanCountSpec
#check @OneHopRecoverableInjectiveSpec
#check @ExistsRecoverableSubsetBoundSpec
#check @Theorem1_BoundedAritySetCapacitySpec
#check @BoundaryControl_DeficitVanishesAtDeltaEqDSpec
#check @GrowingClassesPositiveDeficitSpec
#check @OneClassBoundedArityHalfBarrierQuestion
#check @OneClassBoundedArityCodingGainAboveHalfQuestion

#print axioms SelfReferentialAndCleanCountSpec
#print axioms OneHopRecoverableInjectiveSpec
#print axioms ExistsRecoverableSubsetBoundSpec
#print axioms Theorem1_BoundedAritySetCapacitySpec
#print axioms BoundaryControl_DeficitVanishesAtDeltaEqDSpec
#print axioms GrowingClassesPositiveDeficitSpec
#print axioms OneClassBoundedArityHalfBarrierQuestion
#print axioms OneClassBoundedArityCodingGainAboveHalfQuestion

-- Part II.A: Affine k-Cube Growth & Hales-Jewett-Free Two-Stage Cutoff
#check @Lemma_AffineCubeCommonMessageGrowthSpec
#check @Control_D13TwoCubeAPFreeSharpnessSpec
#check @Control_D4SameIntervalCodedFactorizationSpec
#check @CauchySchwarzAffineCubeExtractionSpec
#check @Theorem2A_TwoStageRamseyFreeCutoffSpec

#print axioms Lemma_AffineCubeCommonMessageGrowthSpec
#print axioms Control_D13TwoCubeAPFreeSharpnessSpec
#print axioms Control_D4SameIntervalCodedFactorizationSpec
#print axioms CauchySchwarzAffineCubeExtractionSpec
#print axioms Theorem2A_TwoStageRamseyFreeCutoffSpec

-- Part II.B: Sumset Polynomial Recurrence & Log-Power Rank Deficit
#check @VandermondeArbitrarySubsetInjectiveSpec
#check @SumsetAnnihilatingPolynomialSpec
#check @SumsetTwoHopRankBoundSpec
#check @IteratedKovariSosTuranSumsetSpec
#check @Theorem2B_TwoStageLogPowerRankDeficitSpec
#check @Control_D12SingleClassAbstractBandSpec
#check @OpenTarget_MacroscopicTwoStageRankDeficitSpec

#print axioms VandermondeArbitrarySubsetInjectiveSpec
#print axioms SumsetAnnihilatingPolynomialSpec
#print axioms SumsetTwoHopRankBoundSpec
#print axioms IteratedKovariSosTuranSumsetSpec
#print axioms Theorem2B_TwoStageLogPowerRankDeficitSpec
#print axioms Control_D12SingleClassAbstractBandSpec
#print axioms OpenTarget_MacroscopicTwoStageRankDeficitSpec

-- Part III.A: Anti-Diagonal Untwisting & Operator Entanglement Duality
#check @PairwiseShiftCollisionCharacterizationSpec
#check @AntiDiagonalTensorSeparationSpec
#check @OperatorSchmidtRankSubmultiplicativeSpec
#check @OperatorSchmidtRankSwapSpec
#check @OperatorSchmidtRankStoneShuffleSpec
#check @StoneShufflePipelinePassLowerBoundSpec
#check @Control_RowShearAndRowDiagonalAlternationSpec
#check @Control_SkewOneTimePadInformationTrapSpec

#print axioms PairwiseShiftCollisionCharacterizationSpec
#print axioms AntiDiagonalTensorSeparationSpec
#print axioms OperatorSchmidtRankSubmultiplicativeSpec
#print axioms OperatorSchmidtRankSwapSpec
#print axioms OperatorSchmidtRankStoneShuffleSpec
#print axioms StoneShufflePipelinePassLowerBoundSpec
#print axioms Control_RowShearAndRowDiagonalAlternationSpec
#print axioms Control_SkewOneTimePadInformationTrapSpec

-- Bonus Answers to Paper 17
#check @Bonus1_ThreeTermBlockSwapCodeDimSpec
#check @Bonus1_ThreeTermPaddedSevenAndFiveSpec
#check @Bonus2_MultiscaleIntervalBothSidesSpec
#check @Bonus2_MultiscaleFullProfileAttainsFullSwapSpec
#check @OpenTarget_MultiscalePeriodicWalshSwapCodeSpec

#print axioms Bonus1_ThreeTermBlockSwapCodeDimSpec
#print axioms Bonus1_ThreeTermPaddedSevenAndFiveSpec
#print axioms Bonus2_MultiscaleIntervalBothSidesSpec
#print axioms Bonus2_MultiscaleFullProfileAttainsFullSwapSpec
#print axioms OpenTarget_MultiscalePeriodicWalshSwapCodeSpec

-- Part III.B: Native Sweep-Cone Interface to (T) & Problem 9.4
#check @TapeCodingConjectureNegationSpec
#check @PeriodicSweepInducesBoundedAritySharedCodeSpec
#check @PeriodicSweepNonlinearFibreDeficitSpec

#print axioms TapeCodingConjectureNegationSpec
#print axioms PeriodicSweepInducesBoundedAritySharedCodeSpec
#print axioms PeriodicSweepNonlinearFibreDeficitSpec

end BoundedArityDecoders
