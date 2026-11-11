import BoundedArityDecoders

/-!
# Formal Specification & Axiom Audit (`PaperAxioms.lean`)

Typechecks and prints axiom dependencies of every formal specification declaration (51 `: Prop`
declarations total), every primary proof declaration (47 theorems), and every structural,
asymptotic, representation-bridge, and conditional consequence theorem across all 20 modules of
`BoundedArityDecoders`.
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

-- ============================================================================
-- Kernel-Verified Proof Declarations & Axiom Audits (All 7 Proof Modules)
-- ============================================================================

-- Module 1 Proofs (`BoundedAritySetCapacityProofs.lean`: 6 proved specs + 2 dichotomy bridges)
#check (selfReferentialAndCleanCount : SelfReferentialAndCleanCountSpec)
#check (oneHopRecoverableInjective : OneHopRecoverableInjectiveSpec)
#check (existsRecoverableSubsetBound : ExistsRecoverableSubsetBoundSpec)
#check (theorem1_BoundedAritySetCapacity : Theorem1_BoundedAritySetCapacitySpec)
#check (boundaryControl_DeficitVanishesAtDeltaEqD : BoundaryControl_DeficitVanishesAtDeltaEqDSpec)
#check (growingClassesPositiveDeficit : GrowingClassesPositiveDeficitSpec)
#check (oneClassBoundedArityCodingGainAboveHalf_iff_not_halfBarrier :
  OneClassBoundedArityCodingGainAboveHalfQuestion ↔ ¬ OneClassBoundedArityHalfBarrierQuestion)
#check (oneClassCodingGain_of_inverseArityScaling :
  OneClassBoundedArityInverseArityScalingQuestion → OneClassBoundedArityCodingGainAboveHalfQuestion)

#print axioms selfReferentialAndCleanCount
#print axioms oneHopRecoverableInjective
#print axioms existsRecoverableSubsetBound
#print axioms theorem1_BoundedAritySetCapacity
#print axioms boundaryControl_DeficitVanishesAtDeltaEqD
#print axioms growingClassesPositiveDeficit
#print axioms oneClassBoundedArityCodingGainAboveHalf_iff_not_halfBarrier
#print axioms oneClassCodingGain_of_inverseArityScaling

-- Module 2 Proofs (`AffineCubeCompositionProofs.lean`: all 5 specs proved)
#check (lemma_AffineCubeCommonMessageGrowth : Lemma_AffineCubeCommonMessageGrowthSpec)
#check (control_D13TwoCubeAPFreeSharpness : Control_D13TwoCubeAPFreeSharpnessSpec)
#check (control_D4SameIntervalCodedFactorization : Control_D4SameIntervalCodedFactorizationSpec)
#check (cauchySchwarzAffineCubeExtraction : CauchySchwarzAffineCubeExtractionSpec)
#check (theorem2A_TwoStageRamseyFreeCutoff : Theorem2A_TwoStageRamseyFreeCutoffSpec)

#print axioms lemma_AffineCubeCommonMessageGrowth
#print axioms control_D13TwoCubeAPFreeSharpness
#print axioms control_D4SameIntervalCodedFactorization
#print axioms cauchySchwarzAffineCubeExtraction
#print axioms theorem2A_TwoStageRamseyFreeCutoff

-- Module 3 Proofs (`SumsetRankDeficitProofs.lean`: 8 proved specs + 1 open-target bridge)
#check (unshiftedToShiftedSumset : UnshiftedToShiftedSumsetSpec)
#check (vandermondeArbitrarySubsetInjective : VandermondeArbitrarySubsetInjectiveSpec)
#check (stackedBandPullbackInjective : StackedBandPullbackInjectiveSpec)
#check (sumsetAnnihilatingPolynomial : SumsetAnnihilatingPolynomialSpec)
#check (sumsetTwoHopRankBound : SumsetTwoHopRankBoundSpec)
#check (iteratedKovariSosTuranSumset : IteratedKovariSosTuranSumsetSpec)
#check (theorem2B_TwoStageLogPowerRankDeficit : Theorem2B_TwoStageLogPowerRankDeficitSpec)
#check (control_D12SingleClassAbstractBand : Control_D12SingleClassAbstractBandSpec)
#check (openTarget_admissible_of_unrestricted :
  OpenTarget_MacroscopicTwoStageRankDeficitSpec →
    OpenTarget_MacroscopicTwoStageRankDeficitAdmissibleFieldSpec)

#print axioms unshiftedToShiftedSumset
#print axioms vandermondeArbitrarySubsetInjective
#print axioms stackedBandPullbackInjective
#print axioms sumsetAnnihilatingPolynomial
#print axioms sumsetTwoHopRankBound
#print axioms iteratedKovariSosTuranSumset
#print axioms theorem2B_TwoStageLogPowerRankDeficit
#print axioms control_D12SingleClassAbstractBand
#print axioms openTarget_admissible_of_unrestricted

-- Module 4 Proofs (`OperatorDualityProofs.lean`: all 8 specs proved)
#check (pairwiseShiftCollisionCharacterization : PairwiseShiftCollisionCharacterizationSpec)
#check (antiDiagonalTensorSeparation : AntiDiagonalTensorSeparationSpec)
#check (operatorSchmidtRankSubmultiplicative : OperatorSchmidtRankSubmultiplicativeSpec)
#check (operatorSchmidtRankSwap : OperatorSchmidtRankSwapSpec)
#check (operatorSchmidtRankStoneShuffle : OperatorSchmidtRankStoneShuffleSpec)
#check (stoneShufflePipelinePassLowerBound : StoneShufflePipelinePassLowerBoundSpec)
#check (control_RowShearAndRowDiagonalAlternation : Control_RowShearAndRowDiagonalAlternationSpec)
#check (control_SkewOneTimePadInformationTrap : Control_SkewOneTimePadInformationTrapSpec)

#print axioms pairwiseShiftCollisionCharacterization
#print axioms antiDiagonalTensorSeparation
#print axioms operatorSchmidtRankSubmultiplicative
#print axioms operatorSchmidtRankSwap
#print axioms operatorSchmidtRankStoneShuffle
#print axioms stoneShufflePipelinePassLowerBound
#print axioms control_RowShearAndRowDiagonalAlternation
#print axioms control_SkewOneTimePadInformationTrap

-- Module 5 Proofs (`SwapCodeAnswersProofs.lean`: 4 proved specs + 1 open-target bridge)
#check (bonus1_ThreeTermBlockSwapCodeDim : Bonus1_ThreeTermBlockSwapCodeDimSpec)
#check (bonus1_ThreeTermPaddedSevenAndFive : Bonus1_ThreeTermPaddedSevenAndFiveSpec)
#check (bonus2_MultiscaleIntervalBothSides : Bonus2_MultiscaleIntervalBothSidesSpec)
#check (bonus2_MultiscaleFullProfileAttainsFullSwap : Bonus2_MultiscaleFullProfileAttainsFullSwapSpec)
#check (openTarget_walsh_of_periodicProfile :
  OpenTarget_MultiscalePeriodicWalshProfileSpec →
    OpenTarget_MultiscalePeriodicWalshSwapCodeSpec)

#print axioms bonus1_ThreeTermBlockSwapCodeDim
#print axioms bonus1_ThreeTermPaddedSevenAndFive
#print axioms bonus2_MultiscaleIntervalBothSides
#print axioms bonus2_MultiscaleFullProfileAttainsFullSwap
#print axioms walshDigitMask_in_periodicDyadicSpan
#print axioms openTarget_walsh_of_periodicProfile

-- Module 6 Proofs (`NativeSweepInterfaceProofs.lean`: 3 proved specs + `entryBits` identity)
#check (entryBits_eq_clog : ∀ d : ℕ, 2 ≤ d → Transpose.entryBits d = Nat.clog 2 d)
#check (tmTraceCutConeDetermination : TMTraceCutConeDeterminationSpec)
#check (periodicSweepInducesBoundedAritySharedCode : PeriodicSweepInducesBoundedAritySharedCodeSpec)
#check (periodicSweepNonlinearFibreDeficit : PeriodicSweepNonlinearFibreDeficitSpec)

#print axioms entryBits_eq_clog
#print axioms tmTraceCutConeDetermination
#print axioms periodicSweepInducesBoundedAritySharedCode
#print axioms periodicSweepNonlinearFibreDeficit

-- Module 7 Proofs (`DiagnosisAndBarriersProofs.lean`: all 7 specs proved)
#check (diagnosis_TCPAndAdaptiveConeReduction : Diagnosis_TCPAndAdaptiveConeReductionSpec)
#check (diagnosis_AbstractSeparatedHighRateCode : Diagnosis_AbstractSeparatedHighRateCodeSpec)
#check (diagnosis_ShiftAndRotationCodingGainBarrier : Diagnosis_ShiftAndRotationCodingGainBarrierSpec)
#check (diagnosis_LinearSharedDecoderBoundsAndMaskFloors : Diagnosis_LinearSharedDecoderBoundsAndMaskFloorsSpec)
#check (diagnosis_RamseyHalesJewettTwoStage : Diagnosis_RamseyHalesJewettTwoStageSpec)
#check (diagnosis_BehrendAndRandomAPBound : Diagnosis_BehrendAndRandomAPBoundSpec)
#check (diagnosis_StoneShuffleAndRowShearMachineComplexity : Diagnosis_StoneShuffleAndRowShearMachineComplexitySpec)
#check @stoneUnshuffleTM_twoTape_linear

#print axioms diagnosis_TCPAndAdaptiveConeReduction
#print axioms diagnosis_AbstractSeparatedHighRateCode
#print axioms diagnosis_ShiftAndRotationCodingGainBarrier
#print axioms diagnosis_LinearSharedDecoderBoundsAndMaskFloors
#print axioms diagnosis_RamseyHalesJewettTwoStage
#print axioms diagnosis_BehrendAndRandomAPBound
#print axioms diagnosis_StoneShuffleAndRowShearMachineComplexity
#print axioms stoneUnshuffleTM_twoTape_linear

-- ============================================================================
-- Structural, Asymptotic, Bridge & Conditional Consequence Theorems (6 Modules)
-- ============================================================================

-- Consequence Module 1 (`SetCapacityConsequences.lean`)
#check @canonicalWordAlphabet_card_and_ge_two
#check @pMin_two_sided_theta_inv_arity
#check @theorem1_BoundedAritySetCapacity_unconditional
#check @theorem1_CanonicalWordSetCapacity
#check @growingClasses_strict_inv_exp_deficit
#check @corollary_OneClassArityOneThreeQuarters
#check @corollary_OneClassArityTwoTwentyThreeTwentySevenths
#check @oneClassCanonicalArityTwo_of_allAlphabetHalfBarrier
#check @wall1_UnrestrictedArityRateLowerBoundAndTendstoOne
#check @wall1_ExactLogarithmicAsymptoticAllDimensions
#check @asymptotic_SublinearClassesBrokenFractionRefutesRateOne

#print axioms canonicalWordAlphabet_card_and_ge_two
#print axioms pMin_two_sided_theta_inv_arity
#print axioms theorem1_BoundedAritySetCapacity_unconditional
#print axioms theorem1_CanonicalWordSetCapacity
#print axioms growingClasses_strict_inv_exp_deficit
#print axioms corollary_OneClassArityOneThreeQuarters
#print axioms corollary_OneClassArityTwoTwentyThreeTwentySevenths
#print axioms oneClassCanonicalArityTwo_of_allAlphabetHalfBarrier
#print axioms wall1_UnrestrictedArityRateLowerBoundAndTendstoOne
#print axioms wall1_ExactLogarithmicAsymptoticAllDimensions
#print axioms asymptotic_SublinearClassesBrokenFractionRefutesRateOne

-- Consequence Module 2 (`AffineCubeConsequences.lean`)
#check @singleSubset_CauchySchwarzAffineCubeExtraction
#check @denseSubset_AffineCubeCommonMessageBound
#check @theorem2A_GrowingClassesNonFactorization
#check @control_D13_GeneralFieldAndProgressionBridge
#check @control_D4_AllWidthsAndBinaryFields

#print axioms singleSubset_CauchySchwarzAffineCubeExtraction
#print axioms denseSubset_AffineCubeCommonMessageBound
#print axioms theorem2A_GrowingClassesNonFactorization
#print axioms control_D13_GeneralFieldAndProgressionBridge
#print axioms control_D4_AllWidthsAndBinaryFields

-- Consequence Module 3 (`SumsetRankConsequences.lean`)
#check @finsetNatDiam_shift_min
#check @unshiftedToShiftedSumset_intrinsicDiam
#check @sumsetAnnihilatingPolynomial_bandRowSpace
#check @theorem2B_OneSecondStage_OmegaLog
#check @theorem2BExplicitConst_pos
#check @theorem2B_ExplicitConstant
#check @exists_primitive_twelfth_root_complex
#check @d12AddChar_injective_and_primitive
#check @control_D12_UnconditionalExists
#check @control_D12_BandRowSpaceChannelEquiv

#print axioms finsetNatDiam_shift_min
#print axioms unshiftedToShiftedSumset_intrinsicDiam
#print axioms sumsetAnnihilatingPolynomial_bandRowSpace
#print axioms theorem2B_OneSecondStage_OmegaLog
#print axioms theorem2BExplicitConst_pos
#print axioms theorem2B_ExplicitConstant
#print axioms exists_primitive_twelfth_root_complex
#print axioms d12AddChar_injective_and_primitive
#print axioms control_D12_UnconditionalExists
#print axioms control_D12_BandRowSpaceChannelEquiv

-- Consequence Module 4 (`DualityAndSwapConsequences.lean`)
#check @antiDiagTensorEquiv_intertwines_rot
#check @shiftSetCovariance_tensor_finrank
#check @maskFloor_GenericSubspaceRealization
#check @isRowOrColUniform_rankLe_one
#check @boundedOSRPipelinePassLowerBound
#check @uniformShannonMI_eq_zero_of_indep
#check @skewOneTimePad_ShannonMutualInfoZero
#check @rowDiagonal_SourceArityGaugeInvariance
#check @bonus1_UnifiedThreeTermExceedsPairingBound
#check @bonus2_SublinearProfileAndTendstoHalf
#check @walshBitSet_cyclicBoundaryCount
#check @isCyclicInterval_cyclicBoundaryCount_le_two
#check @isPeriodicScaleDyadicMask_cyclicBoundaryCount
#check @walshBitSet_joint_separates_points
#check @walshDigitMaskRotSpan_finrank_le
#check @bonus2_WalshDichotomyStructuralProperties

#print axioms antiDiagTensorEquiv_intertwines_rot
#print axioms shiftSetCovariance_tensor_finrank
#print axioms maskFloor_GenericSubspaceRealization
#print axioms isRowOrColUniform_rankLe_one
#print axioms boundedOSRPipelinePassLowerBound
#print axioms uniformShannonMI_eq_zero_of_indep
#print axioms skewOneTimePad_ShannonMutualInfoZero
#print axioms rowDiagonal_SourceArityGaugeInvariance
#print axioms bonus1_UnifiedThreeTermExceedsPairingBound
#print axioms bonus2_SublinearProfileAndTendstoHalf
#print axioms walshBitSet_cyclicBoundaryCount
#print axioms isCyclicInterval_cyclicBoundaryCount_le_two
#print axioms isPeriodicScaleDyadicMask_cyclicBoundaryCount
#print axioms walshBitSet_joint_separates_points
#print axioms walshDigitMaskRotSpan_finrank_le
#print axioms bonus2_WalshDichotomyStructuralProperties

-- Consequence Module 5 (`MachineSweepConsequences.lean`)
#check @evalConeTree_traceConeTree_eq
#check @tmPeriodicSweepExtraction_cutAbsorbed
#check @tmPeriodicSweepExtraction_cutLabelRefined
#check @padDummyWorkTape_transposesWithin
#check @conditional_TapeCodingConjecture_of_PeriodicCellSweepHypothesis
#check @conditional_TapeCodingConjecture_of_HalfBarrierAndOneClassFibre
#check @conditional_NoLowErrorTwoStageLinear_of_MacroscopicTarget

#print axioms evalConeTree_traceConeTree_eq
#print axioms tmPeriodicSweepExtraction_cutAbsorbed
#print axioms tmPeriodicSweepExtraction_cutLabelRefined
#print axioms padDummyWorkTape_transposesWithin
#print axioms conditional_TapeCodingConjecture_of_PeriodicCellSweepHypothesis
#print axioms conditional_TapeCodingConjecture_of_HalfBarrierAndOneClassFibre
#print axioms conditional_NoLowErrorTwoStageLinear_of_MacroscopicTarget

-- Consequence Module 6 (`DiagnosisAndBridgesConsequences.lean`)
#check @tmWholeCellCutConeBound
#check @wordStepTrace_TCPCellConeReduction
#check @diagnosis_Paper18AdaptiveOriginalEntryPullback
#check @diagnosis2_HighRateTendstoOne
#check @diagnosis3_MultiBitBlockEdgeShiftBarrier
#check @diagnosis4_ExplicitSquareCoverAndMaskCertificateBridge
#check @diagnosis5_CombinatorialInvVdWTendstoAndRankBound
#check @diagnosis6_ModularBehrendAndRandomZModProgression
#check @tmMatrix_gridLinear_bridges

#print axioms tmWholeCellCutConeBound
#print axioms wordStepTrace_TCPCellConeReduction
#print axioms diagnosis_Paper18AdaptiveOriginalEntryPullback
#print axioms diagnosis2_HighRateTendstoOne
#print axioms diagnosis3_MultiBitBlockEdgeShiftBarrier
#print axioms diagnosis4_ExplicitSquareCoverAndMaskCertificateBridge
#print axioms diagnosis5_CombinatorialInvVdWTendstoAndRankBound
#print axioms diagnosis6_ModularBehrendAndRandomZModProgression
#print axioms tmMatrix_gridLinear_bridges

end BoundedArityDecoders
