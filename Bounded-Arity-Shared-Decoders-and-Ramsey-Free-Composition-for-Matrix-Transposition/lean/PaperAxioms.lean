import BoundedArityDecoders

/-!
# Formal Specification & Axiom Audit (`PaperAxioms.lean`)

Typechecks and prints axiom dependencies of every formal specification declaration (51 `: Prop`
declarations total) across all seven modules of `BoundedArityDecoders`.
-/

namespace BoundedArityDecoders

-- Module 1: Bounded-Arity Arbitrary-Set Shared-Decoder Capacity (10 specs)
#check @SelfReferentialAndCleanCountSpec
#check @OneHopRecoverableInjectiveSpec
#check @ExistsRecoverableSubsetBoundSpec
#check @Theorem1_BoundedAritySetCapacitySpec
#check @BoundaryControl_DeficitVanishesAtDeltaEqDSpec
#check @GrowingClassesPositiveDeficitSpec
#check @OneClassArityTwoHalfBarrierQuestion
#check @OneClassBoundedArityHalfBarrierQuestion
#check @OneClassBoundedArityCodingGainAboveHalfQuestion
#check @OneClassBoundedArityInverseArityScalingQuestion

#print axioms SelfReferentialAndCleanCountSpec
#print axioms OneHopRecoverableInjectiveSpec
#print axioms ExistsRecoverableSubsetBoundSpec
#print axioms Theorem1_BoundedAritySetCapacitySpec
#print axioms BoundaryControl_DeficitVanishesAtDeltaEqDSpec
#print axioms GrowingClassesPositiveDeficitSpec
#print axioms OneClassArityTwoHalfBarrierQuestion
#print axioms OneClassBoundedArityHalfBarrierQuestion
#print axioms OneClassBoundedArityCodingGainAboveHalfQuestion
#print axioms OneClassBoundedArityInverseArityScalingQuestion

-- Module 2: Affine k-Cube Growth & Hales-Jewett-Free Two-Stage Cutoff (5 specs)
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

-- Module 3: Sumset Polynomial Recurrence & Log-Power Rank Deficit (10 specs)
#check @UnshiftedToShiftedSumsetSpec
#check @VandermondeArbitrarySubsetInjectiveSpec
#check @StackedBandPullbackInjectiveSpec
#check @SumsetAnnihilatingPolynomialSpec
#check @SumsetTwoHopRankBoundSpec
#check @IteratedKovariSosTuranSumsetSpec
#check @Theorem2B_TwoStageLogPowerRankDeficitSpec
#check @Control_D12SingleClassAbstractBandSpec
#check @OpenTarget_MacroscopicTwoStageRankDeficitAdmissibleFieldSpec
#check @OpenTarget_MacroscopicTwoStageRankDeficitSpec

#print axioms UnshiftedToShiftedSumsetSpec
#print axioms VandermondeArbitrarySubsetInjectiveSpec
#print axioms StackedBandPullbackInjectiveSpec
#print axioms SumsetAnnihilatingPolynomialSpec
#print axioms SumsetTwoHopRankBoundSpec
#print axioms IteratedKovariSosTuranSumsetSpec
#print axioms Theorem2B_TwoStageLogPowerRankDeficitSpec
#print axioms Control_D12SingleClassAbstractBandSpec
#print axioms OpenTarget_MacroscopicTwoStageRankDeficitAdmissibleFieldSpec
#print axioms OpenTarget_MacroscopicTwoStageRankDeficitSpec

-- Module 4: Anti-Diagonal Untwisting & Operator Entanglement Duality (8 specs)
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

-- Module 5: Bonus Answers to Paper 17 (7 specs)
#check @Bonus1_ThreeTermBlockSwapCodeDimSpec
#check @Bonus1_ThreeTermPaddedSevenAndFiveSpec
#check @OpenQuestion_ThreeTermDimFiveExceedsPairingSpec
#check @Bonus2_MultiscaleIntervalBothSidesSpec
#check @Bonus2_MultiscaleFullProfileAttainsFullSwapSpec
#check @OpenTarget_MultiscalePeriodicWalshSwapCodeSpec
#check @OpenTarget_MultiscalePeriodicWalshProfileSpec

#print axioms Bonus1_ThreeTermBlockSwapCodeDimSpec
#print axioms Bonus1_ThreeTermPaddedSevenAndFiveSpec
#print axioms OpenQuestion_ThreeTermDimFiveExceedsPairingSpec
#print axioms Bonus2_MultiscaleIntervalBothSidesSpec
#print axioms Bonus2_MultiscaleFullProfileAttainsFullSwapSpec
#print axioms OpenTarget_MultiscalePeriodicWalshSwapCodeSpec
#print axioms OpenTarget_MultiscalePeriodicWalshProfileSpec

-- Module 6: Native Sweep-Cone Interface to (T) & Problem 9.4 (4 specs)
#check @TapeCodingConjectureNegationSpec
#check @TMTraceCutConeDeterminationSpec
#check @PeriodicSweepInducesBoundedAritySharedCodeSpec
#check @PeriodicSweepNonlinearFibreDeficitSpec

#print axioms TapeCodingConjectureNegationSpec
#print axioms TMTraceCutConeDeterminationSpec
#print axioms PeriodicSweepInducesBoundedAritySharedCodeSpec
#print axioms PeriodicSweepNonlinearFibreDeficitSpec

-- Module 7: Diagnosis, Prior Spine Benchmarks & Machine-Level Controls (7 specs)
#check @Diagnosis_TCPAndAdaptiveConeReductionSpec
#check @Diagnosis_AbstractSeparatedHighRateCodeSpec
#check @Diagnosis_ShiftAndRotationCodingGainBarrierSpec
#check @Diagnosis_LinearSharedDecoderBoundsAndMaskFloorsSpec
#check @Diagnosis_RamseyHalesJewettTwoStageSpec
#check @Diagnosis_BehrendAndRandomAPBoundSpec
#check @Diagnosis_StoneShuffleAndRowShearMachineComplexitySpec

#print axioms Diagnosis_TCPAndAdaptiveConeReductionSpec
#print axioms Diagnosis_AbstractSeparatedHighRateCodeSpec
#print axioms Diagnosis_ShiftAndRotationCodingGainBarrierSpec
#print axioms Diagnosis_LinearSharedDecoderBoundsAndMaskFloorsSpec
#print axioms Diagnosis_RamseyHalesJewettTwoStageSpec
#print axioms Diagnosis_BehrendAndRandomAPBoundSpec
#print axioms Diagnosis_StoneShuffleAndRowShearMachineComplexitySpec

end BoundedArityDecoders
