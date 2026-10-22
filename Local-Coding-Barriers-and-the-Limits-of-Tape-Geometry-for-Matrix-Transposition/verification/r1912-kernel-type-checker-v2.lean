import Lean
import TransposeFollowup.TwoStageHelperEntropy
import TransposeFollowup.BufferedRowShiftApproximation
import TransposeFollowup.IntegerMatrixGeometry
import TransposeFollowup.IntegerMatrixPalette
import TransposeFollowup.MatrixPaletteLimits
import TransposeFollowup.MatrixPaletteObstructions
import TransposeFollowup.MatrixPermutationGeometry
import TransposeFollowup.MatrixPermutationPalette
import TransposeFollowup.RawSymbolWord
import TransposeFollowup.RawSymbolWordApproximation
import TransposeFollowup.RawSymbolWordObstruction
import TransposeFollowup.ScheduledWordApproximation
import TransposeFollowup.TernaryMatrixGeometry
import TransposeFollowup.TernaryMatrixPalette
import TransposeFollowup.BufferedSymbolMap
import TransposeFollowup.RawSymbolMap
import TransposeFollowup.RawSymbolMapApproximation
import TransposeFollowup.TernaryPhase
import TransposeFollowup.RawEntryShift
import TransposeFollowup.BufferedRowUpdate
import TransposeFollowup.RawTernaryMatrixHorizontal
import TransposeFollowup.RawTernaryMatrixHorizontalApproximation
import TransposeFollowup.RawTernaryVertical
import TransposeFollowup.TernaryBufferCoordinates
import TransposeFollowup.BufferedRowBank
import TransposeFollowup.BufferedRowBankFrame
import TransposeFollowup.BufferedRowBankInvariant
import TransposeFollowup.BufferedRowBankMotion
import TransposeFollowup.BufferedRowLoopMotion
import TransposeFollowup.BufferedRowRows
import TransposeFollowup.BufferedRowRule
import TransposeFollowup.TernaryBufferedRule
import TransposeFollowup.CoupledRowScanInvariant
import TransposeFollowup.TernaryBankData
import TransposeFollowup.BankSymbolRotationMotion
import TransposeFollowup.BankSymbolRotationApproximation
import TransposeFollowup.RawSymbolRotation
import TransposeFollowup.RawSymbolRotationApproximation
import TransposeFollowup.BankSymbolRotation
import TransposeFollowup.IndexedBankRows
import TransposeFollowup.IndexedBankRowsInvariant
import TransposeFollowup.IndexedBankRowsMotion
import TransposeFollowup.RawEntryRotation
import TransposeFollowup.RawEntryRotationApproximation
import TransposeFollowup.RawUnitArithmeticData
import TransposeFollowup.RawCarryBank
import TransposeFollowup.RawCarryBankMotion
import TransposeFollowup.RawCarryBankApproximation
import TransposeFollowup.RawUnitArithmeticNative
import TransposeFollowup.RawUnitArithmeticApproximation
import TransposeFollowup.RawRowXor
import TransposeFollowup.RawRowXorApproximation
import TransposeFollowup.ScheduledBankRows
import TransposeFollowup.ScheduledBankRowsInvariant
import TransposeFollowup.ScheduledBankRowsMotion
import TransposeFollowup.RawEntryReversal
import TransposeFollowup.RawEntryReversalApproximation
import TransposeFollowup.ScheduledMotionError
import TransposeFollowup.BankBlockReversalMotion
import TransposeFollowup.BankBlockReversalApproximation
import TransposeFollowup.RawBlockReversal
import TransposeFollowup.RawBlockReversalApproximation
import TransposeFollowup.BlockReverseTransfer
import TransposeFollowup.BankBlockReversal
import TransposeFollowup.BankBlockReversalInvariant
import TransposeFollowup.RawShellPosition
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawRowProgramApproximation
import TransposeFollowup.RawShellResources
import TransposeFollowup.TapeWindow
import TransposeFollowup.RawRowBankInvariant
import TransposeFollowup.RawProgramShell
import TransposeFollowup.RawRowProgram
import TransposeFollowup.NativeIOModeProduct
import TransposeFollowup.ScheduledModeRawIO
import TransposeFollowup.SharedRowBank
import TransposeFollowup.RepeatedScheduleMotion
import TransposeFollowup.CoupledRowMotion
import TransposeFollowup.RawRowLoopMotion
import TransposeFollowup.ScheduledCleanupMotion
import TransposeFollowup.RowBankCurve
import TransposeFollowup.RawRowBankMotion
import TransposeFollowup.RawRowBankApproximation
import TransposeFollowup.ScheduledBankCleanup
import TransposeFollowup.ZipperListCells
import TransposeFollowup.RawRowArithmeticBank
import TransposeFollowup.RawRowBankNative
import TransposeFollowup.CoupledRowCell
import TransposeFollowup.CoupledRowScan
import TransposeFollowup.CoupledRowMoves
import TransposeFollowup.RawRowArithmeticData
import TransposeFollowup.RawRowArithmeticRun
import TransposeFollowup.ScheduledHeadDisplacement
import TransposeFollowup.RawRowArithmeticNative
import TransposeFollowup.RawRowArithmeticRows
import TransposeFollowup.RowArithmeticUpdate
import TransposeFollowup.PaddedWorkSchedule
import TransposeFollowup.ModularRowWord
import TransposeFollowup.BinarySlotApproximation
import TransposeFollowup.ScheduledWordSlots
import TransposeFollowup.BinarySlotRegularity
import TransposeFollowup.BinarySlotFamilyRegularity
import TransposeFollowup.FiniteAffineSums
import TransposeFollowup.MixedBinaryWordRegularity
import TransposeFollowup.RawBankProgramApproximation
import TransposeFollowup.RawMixedBinaryWordRegularity
import TransposeFollowup.RawMixedBinaryWordObstruction
import TransposeFollowup.RawBankProgram
import TransposeFollowup.RawBankProgramMotion
import TransposeFollowup.RawBankProgramResources
import TransposeFollowup.RawMixedBinaryWord
import TransposeFollowup.RawMixedBinaryWordMotion
import TransposeFollowup.RawMixedBinaryWordResources
import TransposeFollowup.ScheduledWord
import TransposeFollowup.BankWordInvariant
import TransposeFollowup.BinaryBankOperation
import TransposeFollowup.MixedBinaryWord
import TransposeFollowup.MixedBinaryWordMotion
import TransposeFollowup.ScheduledAdvance
import TransposeFollowup.BankRotation
import TransposeFollowup.BankRotationMotion
import TransposeFollowup.BankRotationApproximation
import TransposeFollowup.BackwardMaskedStride
import TransposeFollowup.BackwardStrideMotion
import TransposeFollowup.BackwardStrideApproximation
import TransposeFollowup.ScheduledTransferCell
import TransposeFollowup.ScheduledTransfer
import TransposeFollowup.BankReversal
import TransposeFollowup.BankReversalMotion
import TransposeFollowup.BankReversalApproximation
import TransposeFollowup.MaskedStrideWord
import TransposeFollowup.RawMaskedStrideWord
import TransposeFollowup.LinearStateCount
import TransposeFollowup.RawStrideWordResources
import TransposeFollowup.MaskedStrideWordMotion
import TransposeFollowup.RawStrideWordMotion
import TransposeFollowup.StrideStageApproximation
import TransposeFollowup.PhysicalAffineApproximationObstruction
import TransposeFollowup.RawMaskedStrideObstruction
import TransposeFollowup.MaskedStrideBankStage
import TransposeFollowup.RawMaskedStrideRegularity
import TransposeFollowup.RawMaskedStrideAffineApproximation
import TransposeFollowup.RawMaskedStrideMotion
import TransposeFollowup.RawMaskedStrideCorrectness
import TransposeFollowup.MaskedStrideExecution
import TransposeFollowup.ScheduledNativeIO
import TransposeFollowup.MaskedStrideCell
import TransposeFollowup.MaskedStrideGroup
import TransposeFollowup.ExceptionalRecursiveLimits
import TransposeFollowup.NativeExceptionalRecursion
import TransposeFollowup.ExceptionalStageClock
import TransposeFollowup.StageFlagLimits
import TransposeFollowup.ExceptionalCoverageLimits
import TransposeFollowup.ContractingStageClock
import TransposeFollowup.NativeRecursiveLimit
import TransposeFollowup.NativeRegularRecursion
import TransposeFollowup.ActualStageRegularity
import TransposeFollowup.StageAffineAssembly
import TransposeFollowup.FrozenHaltLimits
import TransposeFollowup.RecursiveAffineLimits
import TransposeFollowup.FiniteStageLimits
import TransposeFollowup.LimitingStageCoverage
import TransposeFollowup.CommonStageLimits
import TransposeFollowup.UnitTickRegions
import TransposeFollowup.StageRealGeometry
import TransposeFollowup.PhysicalStageCoverage
import TransposeFollowup.ContractingTreeCharge
import TransposeFollowup.ContractingTickBudget
import TransposeFollowup.StageClockAccounting
import TransposeFollowup.FrozenLocalProfiles
import TransposeFollowup.NativeFrozenProfiles
import TransposeFollowup.FrozenProfileRegularity
import TransposeFollowup.PhysicalWalkNormalization
import TransposeFollowup.CanonicalTimeNormalization
import TransposeFollowup.NativePhysicalLimits
import TransposeFollowup.AffinePointwiseClosure
import TransposeFollowup.BoundedAffineCovers
import TransposeFollowup.AffineApproximationObstruction
import TransposeFollowup.AffineTimeScaling
import TransposeFollowup.NativeAffineMotion
import TransposeFollowup.CompactIntervalCover
import TransposeFollowup.CompactVisitMajorant
import TransposeFollowup.OmittedVisitBound
import TransposeFollowup.FiniteAffineTimeBound
import TransposeFollowup.CountableAffineTimeBound
import TransposeFollowup.OpenAffineTimeBound
import TransposeFollowup.CountableAffinePathLabels
import TransposeFollowup.FiniteAffineObstruction
import TransposeFollowup.AffineHeightPairs
import TransposeFollowup.ConsecutiveDeletion
import TransposeFollowup.AffineBranchCuts
import TransposeFollowup.WeightedAffinePriority
import TransposeFollowup.FiniteAffineLabels
import TransposeFollowup.CountableAffineLabels
import TransposeFollowup.AffineGridCollisions
import TransposeFollowup.PrioritySampleTransfer
import TransposeFollowup.AffineSampleBoundary
import TransposeFollowup.AffineGridIntervals
import TransposeFollowup.AffinePriorityLabels
import TransposeFollowup.CommutativeFiniteBoundary
import TransposeFollowup.AffineFiniteBoundary
import TransposeFollowup.FiniteMinimumCoupling
import TransposeFollowup.WeightedMinimumCoupling
import TransposeFollowup.AffineGridMass
import TransposeFollowup.InitialWalkFlattening
import TransposeFollowup.AutocorrelationEnergyDescent
import TransposeFollowup.InitialWalkDensityCap
import TransposeFollowup.RationalRestrictedGap
import TransposeFollowup.RationalContinuousExpander
import TransposeFollowup.UnconditionalPaidPadding
import TransposeFollowup.SpanningProfileExclusion
import TransposeFollowup.TraceSquareDyadicTraceGrowth
import TransposeFollowup.TraceSquareSampleApplication
import TransposeFollowup.TraceSquareReadoutParameters
import TransposeFollowup.TraceSquareConcentrationBudget
import TransposeFollowup.TraceSquareExponentMargins
import TransposeFollowup.TraceSquareTwoStageSample
import TransposeFollowup.ScalarSampleNormalization
import TransposeFollowup.TraceSquareSourceSample
import TransposeFollowup.MixedReadoutSourceTransfer
import TransposeFollowup.CentralizerScalarSumProduct
import TransposeFollowup.QuantitativeSpanningExtraction
import TransposeFollowup.NilpotentProfileExclusion
import TransposeFollowup.NilpotentExtractionParameters
import TransposeFollowup.ScalarDyadicBudgets
import TransposeFollowup.CubicSampleNormalization
import TransposeFollowup.CubicSourceWordLocality
import TransposeFollowup.PowerClusterConcentration
import TransposeFollowup.PopularRowIntersections
import TransposeFollowup.OverlappingRowRuzsa
import TransposeFollowup.RoundedDilateProjections
import TransposeFollowup.ScalarRingProjection
import TransposeFollowup.ActualTraceCoefficient
import TransposeFollowup.NilpotentScalarArithmetic
import TransposeFollowup.NilpotentArithmeticWords
import TransposeFollowup.TraceReextractionCubicBound
import TransposeFollowup.CommutingFamilyCubicBound
import TransposeFollowup.InverseFinalScalarIdentity
import TransposeFollowup.NormalizedCubicProductError
import TransposeFollowup.CubicSourceWordTransfer
import TransposeFollowup.ActualCentralizerSourcePacking
import TransposeFollowup.CoarsenedSourceSample
import TransposeFollowup.NormalizedCentralizerChart
import TransposeFollowup.CentralizerClusterSelection
import TransposeFollowup.LocalizedCentralizerSample
import TransposeFollowup.LocalizedCentralizerPacking
import TransposeFollowup.ActualCentralizerPacking
import TransposeFollowup.SL2AdjointVolume
import TransposeFollowup.SL2AdjointSpan
import TransposeFollowup.BilinearBracketSelection
import TransposeFollowup.SL2AdjointFrame
import TransposeFollowup.SL2NearIdentityAdjointFrame
import TransposeFollowup.SL2CentralizerChart
import TransposeFollowup.TripleProductLinearization
import TransposeFollowup.CentralizerProductInverse
import TransposeFollowup.CentralizerCubicPacking
import TransposeFollowup.SL2CentralizerTrace
import TransposeFollowup.SL2LocalConcentration
import TransposeFollowup.SeparatedMatrixSample
import TransposeFollowup.ScalarMetricBridge
import TransposeFollowup.FiniteTranslateCover
import TransposeFollowup.ApproximatePowerCover
import TransposeFollowup.LocalizedFixedProductEnvelope
import TransposeFollowup.SL2NearIdentityProducts
import TransposeFollowup.SpanningCommutingExtraction
import TransposeFollowup.FinitePieceCoverBounds
import TransposeFollowup.SL2TranslatedCluster
import TransposeFollowup.DyadicCenterTrimming
import TransposeFollowup.TraceBucketCover
import TransposeFollowup.SeparatedScalarCover
import TransposeFollowup.TraceCommutingExtraction
import TransposeFollowup.SL2ConjugacyFiber
import TransposeFollowup.FrobeniusCoverTransfer
import TransposeFollowup.ConjugacyFiberCovering
import TransposeFollowup.FiniteCoverSelection
import TransposeFollowup.LargeConjugacyFiber
import TransposeFollowup.ScalarCentralizerProjection
import TransposeFollowup.RealDeterminantNormalization
import TransposeFollowup.SL2CommutingApproximation
import TransposeFollowup.SL2SpanningTrace
import TransposeFollowup.MatrixFourBounds
import TransposeFollowup.SL2TraceProjection
import TransposeFollowup.SL2TraceCover
import TransposeFollowup.SL2GlobalTraceCover
import TransposeFollowup.FractionalDyadicIndex
import TransposeFollowup.EscapeExponentScales
import TransposeFollowup.HomFamilyComplexEscape
import TransposeFollowup.SmoothedIterateSmallEscape
import TransposeFollowup.SL2SpanCertificate
import TransposeFollowup.RationalSpanCertificate
import TransposeFollowup.SL2OffDiagonalBounds
import TransposeFollowup.SL2DiagonalRescale
import TransposeFollowup.ComplexMatrixProductError
import TransposeFollowup.SL2UpperApproximation
import TransposeFollowup.SL2BicommutatorError
import TransposeFollowup.SL2QuantitativeEscape
import TransposeFollowup.SL2ComplexConjugation
import TransposeFollowup.RationalComplexEscape
import TransposeFollowup.SL2TriangularBicommutator
import TransposeFollowup.SL2TraceCertificate
import TransposeFollowup.RationalTraceCertificate
import TransposeFollowup.FreeWordPowerNorm
import TransposeFollowup.FreeGroupCentralizer
import TransposeFollowup.ShortWordCounting
import TransposeFollowup.ShortWordBicommutator
import TransposeFollowup.ShortWordGrowthThreshold
import TransposeFollowup.RationalBicommutator
import TransposeFollowup.SmoothedWalkShortWords
import TransposeFollowup.NormalizedShortWords
import TransposeFollowup.SmoothedIterateShortWords
import TransposeFollowup.SmoothedIterateWordDistribution
import TransposeFollowup.SeparatedCardinalityPower
import TransposeFollowup.DyadicSeparationInterpolation
import TransposeFollowup.SeparatedPowerAbsorption
import TransposeFollowup.SmoothedIterateDistribution
import TransposeFollowup.InitialWalkDistribution
import TransposeFollowup.GeneratorWalkFiniteSupport
import TransposeFollowup.RationalCommonSmoothingSeparation
import TransposeFollowup.SmoothedWalkSeparatedSubset
import TransposeFollowup.DyadicWalkSeparatedSubset
import TransposeFollowup.SmoothedIterateSeparatedSubset
import TransposeFollowup.MobiusLocalizedProbability
import TransposeFollowup.ConvolutionTranslateMass
import TransposeFollowup.SmoothedIterateShortWalk
import TransposeFollowup.SmoothedIterateLocalizedMass
import TransposeFollowup.InitialWalkLocalizedMass
import TransposeFollowup.DyadicWalkSupportScale
import TransposeFollowup.DyadicWalkLengthThreshold
import TransposeFollowup.InitialWalkCoveringInterval
import TransposeFollowup.CoveringLevelScale
import TransposeFollowup.CoveringPolynomialLoss
import TransposeFollowup.CoveringPowerEnvelope
import TransposeFollowup.CoveringSizeInterval
import TransposeFollowup.MobiusCoveringPowerBounds
import TransposeFollowup.SmoothedIterateCoveringInterval
import TransposeFollowup.ExternalCoverAttainment
import TransposeFollowup.FrobeniusClosedRefinement
import TransposeFollowup.MobiusCoveringNumbers
import TransposeFollowup.SmoothedIterateCoveringProfile
import TransposeFollowup.MobiusNearIdentityLocalization
import TransposeFollowup.MobiusFrobeniusCoverVolume
import TransposeFollowup.SmoothedIterateLocalizedCover
import TransposeFollowup.CoordinateCoverRefinement
import TransposeFollowup.MobiusCoverRefinement
import TransposeFollowup.MobiusApproximateRefinement
import TransposeFollowup.SmoothedIterateFrobeniusCover
import TransposeFollowup.HaarFinitePacking
import TransposeFollowup.FiniteTranslateOverlap
import TransposeFollowup.HaarApproximateCore
import TransposeFollowup.MobiusApproximateFromEnergy
import TransposeFollowup.HaarRuzsaBounds
import TransposeFollowup.HaarInverseEnergy
import TransposeFollowup.HaarPopularOverlap
import TransposeFollowup.HaarSandwichRepresentations
import TransposeFollowup.HaarSandwichBounds
import TransposeFollowup.MobiusPopularCore
import TransposeFollowup.MobiusCoreFromEnergy
import TransposeFollowup.StrictDegreeTrimming
import TransposeFollowup.OpenRelationDegrees
import TransposeFollowup.ProductNeighborOverlap
import TransposeFollowup.MobiusHighDegreeRows
import TransposeFollowup.MobiusProductTrimming
import TransposeFollowup.MobiusSmallProductBSG
import TransposeFollowup.WeightedFiberSelection
import TransposeFollowup.IncidenceFiberMoments
import TransposeFollowup.IncidenceFiberSelection
import TransposeFollowup.ProductFiberSelection
import TransposeFollowup.ProductQuotientControl
import TransposeFollowup.MobiusWeakBSG
import TransposeFollowup.OpenProductDensity
import TransposeFollowup.ProductDensityPairs
import TransposeFollowup.PopularProductEnergy
import TransposeFollowup.MobiusPopularProducts
import TransposeFollowup.DensityEnergyCongruence
import TransposeFollowup.SymmetricOpenSuperset
import TransposeFollowup.MobiusOpenEntryBox
import TransposeFollowup.MobiusSetEnergyRegularization
import TransposeFollowup.LevelEnergyNormalization
import TransposeFollowup.HaarSetEnergyBounds
import TransposeFollowup.RelativeNonflatteningEnergy
import TransposeFollowup.DensityConvolutionTrace
import TransposeFollowup.HaarSelfEnergyExtraction
import TransposeFollowup.SmoothedIterateSelfEnergy
import TransposeFollowup.ContinuousDensityConvolution
import TransposeFollowup.FiniteEnergyExtraction
import TransposeFollowup.DyadicDensityLevels
import TransposeFollowup.DensityTailEnergy
import TransposeFollowup.DensityLevelEnergy
import TransposeFollowup.NonflatteningLevelPair
import TransposeFollowup.SmoothedIterateLevelEnergy
import TransposeFollowup.AutocorrelationSupport
import TransposeFollowup.AutocorrelationCoefficient
import TransposeFollowup.ProbabilityConvolutionPowers
import TransposeFollowup.AutocorrelationPowerAction
import TransposeFollowup.AutocorrelationIterates
import TransposeFollowup.AutocorrelationIterateCoefficient
import TransposeFollowup.AutocorrelationFlatnessBarrier
import TransposeFollowup.RestrictedGapFromAutocorrelation
import TransposeFollowup.MobiusUnimodular
import TransposeFollowup.MeasureAutocorrelation
import TransposeFollowup.GeneratorWalkSymmetry
import TransposeFollowup.SmoothedWalkAutocorrelation
import TransposeFollowup.SmoothedAutocorrelationEnergy
import TransposeFollowup.AutocorrelationAction
import TransposeFollowup.InitialWalkScales
import TransposeFollowup.SmoothedDensityPropagation
import TransposeFollowup.InitialWalkRadiusGain
import TransposeFollowup.InitialWalkNormalization
import TransposeFollowup.InitialWalkFamily
import TransposeFollowup.RationalWordArithmetic
import TransposeFollowup.FreeWalkPotential
import TransposeFollowup.FreeWalkAtom
import TransposeFollowup.RationalWalkIsolation
import TransposeFollowup.GeneratorWalkAtoms
import TransposeFollowup.IsolatedHaarDensity
import TransposeFollowup.RationalWalkNonconcentration
import TransposeFollowup.RationalWalkInitialL2
import TransposeFollowup.BoundedCoordinatePacking
import TransposeFollowup.RationalPackedFamily
import TransposeFollowup.DyadicFreeFamilyScales
import TransposeFollowup.DyadicFreeFamily
import TransposeFollowup.RationalNearIdentityFamily
import TransposeFollowup.FreeWordPrefix
import TransposeFollowup.FreeWordSquares
import TransposeFollowup.PositiveWordSquares
import TransposeFollowup.RationalSquareFamily
import TransposeFollowup.FreeBasisRebase
import TransposeFollowup.RationalRecenteredFamily
import TransposeFollowup.RationalFreePair
import TransposeFollowup.RationalNearIdentityFreePair
import TransposeFollowup.RationalSeedWords
import TransposeFollowup.MobiusIdentityCoordinates
import TransposeFollowup.MobiusSmallBallVolume
import TransposeFollowup.MobiusHaarKernelBounds
import TransposeFollowup.MobiusProbabilityCoefficient
import TransposeFollowup.MobiusDensityAverage
import TransposeFollowup.MobiusWalkEntrySupport
import TransposeFollowup.DyadicDensityBarrier
import TransposeFollowup.MobiusComplexInner
import TransposeFollowup.PositiveAffineMeasure
import TransposeFollowup.MobiusPolarCoefficient
import TransposeFollowup.MobiusBoxCoefficient
import TransposeFollowup.MobiusColumnCoordinates
import TransposeFollowup.MobiusColumnChart
import TransposeFollowup.MobiusColumnHaar
import TransposeFollowup.MobiusPolarHaar
import TransposeFollowup.MobiusHaarEntryBox
import TransposeFollowup.SchwartzAffineFourier
import TransposeFollowup.WaveletScaleKernel
import TransposeFollowup.SchwartzWaveletEstimate
import TransposeFollowup.L2WaveletCoefficient
import TransposeFollowup.L2WaveletEstimate
import TransposeFollowup.MobiusAffineWavelet
import TransposeFollowup.LeftConvolutionDensity
import TransposeFollowup.MobiusSmoothedDensity
import TransposeFollowup.DyadicSmoothingScale
import TransposeFollowup.UniformSmoothedBandWitness
import TransposeFollowup.SymmetricDyadicPowers
import TransposeFollowup.SymmetricGeneratorMeasure
import TransposeFollowup.GeneratorConvolutionWalk
import TransposeFollowup.MobiusHaarKernel
import TransposeFollowup.MobiusActionContinuity
import TransposeFollowup.MobiusGroupAverage
import TransposeFollowup.MobiusGroupSmoothing
import TransposeFollowup.MobiusPairwiseComparison
import TransposeFollowup.ComplexMobiusComposition
import TransposeFollowup.MobiusLocalFactorization
import TransposeFollowup.MobiusNearIdentity
import TransposeFollowup.MobiusUnipotentEnergy
import TransposeFollowup.MobiusUnipotentMatrices
import TransposeFollowup.NormalizedRegularBandWitness
import TransposeFollowup.SchwartzDyadicRegularity
import TransposeFollowup.SchwartzL2Normalization
import TransposeFollowup.TranslationDerivativeEnergy
import TransposeFollowup.DyadicBandOverlapEnergy
import TransposeFollowup.DyadicBandRegularityCost
import TransposeFollowup.DyadicMaskedCorrelation
import TransposeFollowup.DyadicRegularityDiscard
import TransposeFollowup.DyadicTailReconstruction
import TransposeFollowup.FiniteSymmetricCorrelation
import TransposeFollowup.GridDyadicTail
import TransposeFollowup.RetainedCorrelationLimit
import TransposeFollowup.UniformRegularBandIsolation
import TransposeFollowup.UniformRetainedBandIsolation
import TransposeFollowup.ComplexAverageActionSum
import TransposeFollowup.UniformDyadicConstants
import TransposeFollowup.DyadicAverageFarCorrelation
import TransposeFollowup.DyadicNearCorrelation
import TransposeFollowup.SymmetricOffsetSum
import TransposeFollowup.DyadicSmallRatioCorrelation
import TransposeFollowup.UniformBandIsolation
import TransposeFollowup.SmoothBandLinearIdentities
import TransposeFollowup.DyadicLowL2Convergence
import TransposeFollowup.DyadicL2Reconstruction
import TransposeFollowup.SmoothHighFrequencyBounds
import TransposeFollowup.GridSmoothHighFrequency
import TransposeFollowup.DyadicOffsetCorrelation
import TransposeFollowup.DyadicFarCorrelation
import TransposeFollowup.DyadicSchwartzDilation
import TransposeFollowup.DyadicSmoothCutoff
import TransposeFollowup.DyadicAnnulusOverlap
import TransposeFollowup.DyadicCoefficientBounds
import TransposeFollowup.ConcreteDyadicTransport
import TransposeFollowup.SchwartzFourierMoments
import TransposeFollowup.SmoothBandSpatialMoments
import TransposeFollowup.FiniteBandTransportEnergy
import TransposeFollowup.UnitSupportedMoments
import TransposeFollowup.UnitSupportedFourierDerivatives
import TransposeFollowup.SmoothFrequencyBand
import TransposeFollowup.FiniteMultiplierEnergy
import TransposeFollowup.SmoothBandSpectrumDerivatives
import TransposeFollowup.SmoothBandDerivativeEnergy
import TransposeFollowup.FiniteBandDerivativeEnergy
import TransposeFollowup.SchwartzL2Derivative
import TransposeFollowup.SchwartzFourierDerivativeTest
import TransposeFollowup.L2FourierDerivative
import TransposeFollowup.L2DerivativeFrequencyTail
import TransposeFollowup.MobiusSchwartzL2Derivative
import TransposeFollowup.MobiusSchwartzFrequencyTail
import TransposeFollowup.FrequencySeparatedCorrelation
import TransposeFollowup.MobiusWeightDerivative
import TransposeFollowup.MobiusDifferentialTransport
import TransposeFollowup.MobiusTransportMoments
import TransposeFollowup.SchwartzSpatialMoments
import TransposeFollowup.MobiusSchwartzDerivative
import TransposeFollowup.MobiusPoleDecay
import TransposeFollowup.MobiusSchwartzRegularity
import TransposeFollowup.FourierL2Bridge
import TransposeFollowup.FrequencyCutoff
import TransposeFollowup.ComplexL2Parts
import TransposeFollowup.ComplexifiedL2Operator
import TransposeFollowup.GridHighFrequency
import TransposeFollowup.GridCancellation
import TransposeFollowup.GridFourierCancellation
import TransposeFollowup.UnitSupportedL1
import TransposeFollowup.NormalizedGridFourier
import TransposeFollowup.ContractionCorrelation
import TransposeFollowup.RealMobiusAlgebra
import TransposeFollowup.RealMobiusJacobian
import TransposeFollowup.RealMobiusWeighted
import TransposeFollowup.RealMobiusL2
import TransposeFollowup.RationalMobiusAction
import TransposeFollowup.RealMobiusAverage
import TransposeFollowup.SpectralGapInterface
import TransposeFollowup.ExpansionParameters
import TransposeFollowup.NormalizedCellCorrelation
import TransposeFollowup.ConditionalSpectralExpansion
import TransposeFollowup.WeightedEnergyTransfer
import TransposeFollowup.UnitBoundaryError
import TransposeFollowup.CellCenteredAlmostInvariant
import TransposeFollowup.CellCenteredRelativeError
import TransposeFollowup.SmallExpansionSymmDiff
import TransposeFollowup.IndicatorPullbackError
import TransposeFollowup.WeightedIndicatorError
import TransposeFollowup.MobiusCalculus
import TransposeFollowup.NearIdentityMobius
import TransposeFollowup.CellCenteredVariance
import TransposeFollowup.CellCenteredSpectralInput
import TransposeFollowup.GridTrimming
import TransposeFollowup.GridProjectionError
import TransposeFollowup.TranslationExpansion
import TransposeFollowup.TranslationUniformity
import TransposeFollowup.RationalUnitRestriction
import TransposeFollowup.ClosedRationalExpansion
import TransposeFollowup.ClosedNativePadding
import TransposeFollowup.HalfGridExpansion
import TransposeFollowup.AllSizeOverlapExpansion
import TransposeFollowup.ContinuousNativePadding
import TransposeFollowup.PaidPaddingLimits
import TransposeFollowup.GeneratorCleanupCost
import TransposeFollowup.NativeSpanErase
import TransposeFollowup.NativeSpanEraseInterface
import TransposeFollowup.StationaryTapes
import TransposeFollowup.StationaryTapesRun
import TransposeFollowup.NativeRunLimits
import TransposeFollowup.SequentialFiveMachine
import TransposeFollowup.SequentialFiveSteps
import TransposeFollowup.SequentialFiveRun
import TransposeFollowup.SequentialFiveCompletion
import TransposeFollowup.BitPlaneAlphabet
import TransposeFollowup.BitPlaneMachine
import TransposeFollowup.BitPlaneRun
import TransposeFollowup.NativeInputRewind
import TransposeFollowup.NativeInputRewindCalls
import TransposeFollowup.NativeIOFusionEmbedding
import TransposeFollowup.NativeIOFusionRecover
import TransposeFollowup.RadiusClockRun
import TransposeFollowup.StoredWordLength
import TransposeFollowup.NativeNonemptyWord
import TransposeFollowup.EntryBitsRun
import TransposeFollowup.NativeDivideThreeData
import TransposeFollowup.NativeDivideThreeMachine
import TransposeFollowup.NativeDivideThreeRun
import TransposeFollowup.ExcursionIntervalTransfer
import TransposeFollowup.NativeTimedWalk
import TransposeFollowup.TimedMatchingLayout
import TransposeFollowup.TimedMatchingSchedule
import TransposeFollowup.TimedRowCoverage
import TransposeFollowup.TimedRowWalk
import TransposeFollowup.GeneratorRowsPreparedGeometry
import TransposeFollowup.NativeIOOnlyWork
import TransposeFollowup.ExactZipperTrace
import TransposeFollowup.NativeIOUnselectedWork
import TransposeFollowup.FusedPageClockIO
import TransposeFollowup.NativeIOFusion
import TransposeFollowup.NativeIOFusionCalls
import TransposeFollowup.NativeIOFusionPrefixes
import TransposeFollowup.NativeIOFusionRun
import TransposeFollowup.NativeReadFusionEmbedding
import TransposeFollowup.FusedPageClock
import TransposeFollowup.FusedPageClockRewind
import TransposeFollowup.FusedPageClockRun
import TransposeFollowup.FusedPageClockScan
import TransposeFollowup.FusedPageClockTrajectory
import TransposeFollowup.NativeReadFusion
import TransposeFollowup.NativeReadFusionBehavior
import TransposeFollowup.NativeClosedStreamExact
import TransposeFollowup.PageClockMachine
import TransposeFollowup.PageClockTrace
import TransposeFollowup.ReusablePageClockMachine
import TransposeFollowup.ReusablePageClockRun
import TransposeFollowup.ReusablePageClockTrajectory
import TransposeFollowup.SevenPhaseClock
import TransposeFollowup.TracePrefix
import TransposeFollowup.OpcodeGeneratorMeaning
import TransposeFollowup.SchedulerSeedRun
import TransposeFollowup.NativeBatchSkipMachine
import TransposeFollowup.NativeBatchSkipRun
import TransposeFollowup.PageEventBatchCanonical
import TransposeFollowup.FamilySelectorMeaning
import TransposeFollowup.PortBindingFrame
import TransposeFollowup.PortBindingValues
import TransposeFollowup.BatchMembershipCalls
import TransposeFollowup.BatchMembershipLoop
import TransposeFollowup.BatchMembershipMachine
import TransposeFollowup.BatchMembershipRecord
import TransposeFollowup.BatchMembershipRun
import TransposeFollowup.NativePairEqualMachine
import TransposeFollowup.NativePairEqualRun
import TransposeFollowup.NativePrefixRewind
import TransposeFollowup.PrefixMembershipLoop
import TransposeFollowup.PrefixMembershipMachine
import TransposeFollowup.PrefixMembershipRun
import TransposeFollowup.RawNormalizationMeaning
import TransposeFollowup.NormalizedRecordsSize
import TransposeFollowup.PreparedPairCalls
import TransposeFollowup.NormalizedBatchBudget
import TransposeFollowup.NormalizedBatchCalls
import TransposeFollowup.NormalizedBatchLoop
import TransposeFollowup.NormalizedBatchMachine
import TransposeFollowup.NormalizedBatchRecord
import TransposeFollowup.NormalizedBatchRun
import TransposeFollowup.FamilyReaderRun
import TransposeFollowup.NativeHeadDisplacement
import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.RawDimensionLoader
import TransposeFollowup.DimensionLoaderRun
import TransposeFollowup.DimensionCandidateSearch
import TransposeFollowup.DimensionCandidateData
import TransposeFollowup.CompactInputMeasure
import TransposeFollowup.NativeTrimRun
import TransposeFollowup.NativeTrimMachine
import TransposeFollowup.NativeTrimData
import TransposeFollowup.InputMeasureRun
import TransposeFollowup.InputMeasureCalls
import TransposeFollowup.InputMeasureMachine
import TransposeFollowup.NativeIOEmbedding
import TransposeFollowup.MeasuredScan
import TransposeFollowup.MeasuredWord
import TransposeFollowup.RawInputCopy
import TransposeFollowup.NativeIOZipper
import TransposeFollowup.NativeIO
import TransposeFollowup.RecordedRowResources
import TransposeFollowup.RowConsumerMeaning
import TransposeFollowup.RowConsumerRun
import TransposeFollowup.RowConsumerLoop
import TransposeFollowup.RowConsumerCalls
import TransposeFollowup.RowConsumerMachine
import TransposeFollowup.RowConsumerData
import TransposeFollowup.NativeClosedStream
import TransposeFollowup.DimensionScaleMeaning
import TransposeFollowup.SignedLinearFormMeaning
import TransposeFollowup.SignedLinearFormRun
import TransposeFollowup.SourceEndpointsMeaning
import TransposeFollowup.NativeErase
import TransposeFollowup.SeedMultipleMeaning
import TransposeFollowup.RowCode
import TransposeFollowup.TranscriptEntropy
import TransposeFollowup.SeparatorCount
import TransposeFollowup.EntropyFibers
import TransposeFollowup.AdaptiveSeparator
import TransposeFollowup.StrategySeparator
import TransposeFollowup.SeparatorSharpness
import TransposeFollowup.AdaptiveTreewidth
import TransposeFollowup.XorDegreeBound
import TransposeFollowup.XorPathCycleBound
import TransposeFollowup.TwoStageHelper
import TransposeFollowup.ExcursionChordCount
import TransposeFollowup.GadgetLabels
import TransposeFollowup.PaddingCutInequality
import TransposeFollowup.MonotoneOverlapGraph
import TransposeFollowup.RationalSymmetricGraph
import TransposeFollowup.RationalOpcodeWalk
import TransposeFollowup.IntegerNeighbors
import TransposeFollowup.RelativeMachine
import TransposeFollowup.FiniteProgramEncoding
import TransposeFollowup.BinaryCompareRun
import TransposeFollowup.AdditiveNeighbors
import TransposeFollowup.LinearGenerationBudget
import TransposeFollowup.NativeArithmeticCalls
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.NativeBuffer
import TransposeFollowup.RepeatedAddBudget
import TransposeFollowup.DenseOverlapScan
import TransposeFollowup.SignedPairBudget
import TransposeFollowup.SignedOverlapData
import TransposeFollowup.InPlaceAdd
import TransposeFollowup.RowStreamBudget
import TransposeFollowup.NativeMappedCopy
import TransposeFollowup.MeasureOverlapTransfer
import TransposeFollowup.MobiusMeasurableApproximate
import TransposeFollowup.SmoothedIterateApproximate
import TransposeFollowup.SmoothedIterateEndpoint
import TransposeFollowup.HaarSmoothingOverlap
import TransposeFollowup.HaarLocalPacking
import TransposeFollowup.MobiusLocalCoverGeometry
import TransposeFollowup.MobiusSmoothingScaleCover
import TransposeFollowup.SmoothedIterateScaleCover

namespace TransposeFollowup.NativePaddedField
open FixedTapeCompiler CopyMachine
open NativeFieldCopy (targetBinding allBinding)
set_option autoImplicit false

theorem R1912_original_header_tail_trace (C : ℕ) (source : Tape Bool) (field : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*field.length+3*C+6, PaddedWord.Trace C id t
      (PaddedWord.cfg (.fill ⟨C,by omega⟩) source (NativeSealBack.openWord field) pos)
      (PaddedWord.cfg (.seal .done) source (Counter.marked (padded C field)) (Function.update pos 1 (pos 1-field.length))) := by
  exact tail_trace C source field pos

end TransposeFollowup.NativePaddedField

namespace TransposeFollowup.CountedFill
open FixedTapeCompiler
open CopyMachine (Tape Sym symbols)
set_option autoImplicit false

theorem R1912_original_header_emit_step (m : ℕ) (bit : Bool) (i : Fin (m+1)) (hi : i.val < m)
    (fuel acc : List Bool) (origin : Fin 2 → ℤ) :
    NativeZipper.step (program m bit) (cfg (.emit i) fuel acc origin)=
      cfg (.emit ⟨i.val+1,by omega⟩) fuel (acc++[bit]) origin := by
  exact emit_step m bit i hi fuel acc origin

end TransposeFollowup.CountedFill

open Lean Elab Command
namespace R1912TypeConversionAudit

def requireArity (j : Json) (n : Nat) : Except String Unit := do
  let a ← j.getArr?
  unless a.size == n do throw s!"AST arity {a.size}, expected {n}"

def tag (j : Json) : Except String String := do
  (← j.getArrVal? 0).getStr?

def decodeName : Nat → Json → Except String Name
  | 0, _ => throw "Name AST depth exceeded"
  | fuel + 1, j => do
    match ← tag j with
    | "anonymous" => requireArity j 1; pure .anonymous
    | "str" =>
      requireArity j 3
      pure (.str (← decodeName fuel (← j.getArrVal? 1)) (← (← j.getArrVal? 2).getStr?))
    | "num" =>
      requireArity j 3
      pure (.num (← decodeName fuel (← j.getArrVal? 1)) (← (← j.getArrVal? 2).getNat?))
    | t => throw s!"Unsupported Name AST tag: {t}"

def decodeLevel : Nat → Json → Except String Level
  | 0, _ => throw "Level AST depth exceeded"
  | fuel + 1, j => do
    match ← tag j with
    | "zero" => requireArity j 1; pure .zero
    | "succ" =>
      requireArity j 2
      pure (.succ (← decodeLevel fuel (← j.getArrVal? 1)))
    | "max" =>
      requireArity j 3
      pure (.max (← decodeLevel fuel (← j.getArrVal? 1)) (← decodeLevel fuel (← j.getArrVal? 2)))
    | "imax" =>
      requireArity j 3
      pure (.imax (← decodeLevel fuel (← j.getArrVal? 1)) (← decodeLevel fuel (← j.getArrVal? 2)))
    | "param" =>
      requireArity j 2
      pure (.param (← decodeName 512 (← j.getArrVal? 1)))
    | t => throw s!"Unsupported Level AST tag: {t}"

def decodeBinderInfo (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | t => throw s!"Unsupported binder info: {t}"

def decodeExpr : Nat → Json → Except String Expr
  | 0, _ => throw "Expr AST depth exceeded"
  | fuel + 1, j => do
    match ← tag j with
    | "bvar" =>
      requireArity j 2
      pure (.bvar (← (← j.getArrVal? 1).getNat?))
    | "sort" =>
      requireArity j 2
      pure (.sort (← decodeLevel 512 (← j.getArrVal? 1)))
    | "const" =>
      requireArity j 3
      let levels ← (← (← j.getArrVal? 2).getArr?).mapM (decodeLevel 512)
      pure (.const (← decodeName 512 (← j.getArrVal? 1)) levels.toList)
    | "app" =>
      requireArity j 3
      pure (.app (← decodeExpr fuel (← j.getArrVal? 1)) (← decodeExpr fuel (← j.getArrVal? 2)))
    | "lam" =>
      requireArity j 5
      pure (.lam (← decodeName 512 (← j.getArrVal? 1))
        (← decodeExpr fuel (← j.getArrVal? 2)) (← decodeExpr fuel (← j.getArrVal? 3))
        (← decodeBinderInfo (← j.getArrVal? 4)))
    | "forallE" =>
      requireArity j 5
      pure (.forallE (← decodeName 512 (← j.getArrVal? 1))
        (← decodeExpr fuel (← j.getArrVal? 2)) (← decodeExpr fuel (← j.getArrVal? 3))
        (← decodeBinderInfo (← j.getArrVal? 4)))
    | "letE" =>
      requireArity j 6
      pure (.letE (← decodeName 512 (← j.getArrVal? 1))
        (← decodeExpr fuel (← j.getArrVal? 2)) (← decodeExpr fuel (← j.getArrVal? 3))
        (← decodeExpr fuel (← j.getArrVal? 4)) (← (← j.getArrVal? 5).getBool?))
    | "lit" =>
      requireArity j 2
      let literal ← j.getArrVal? 1
      requireArity literal 2
      unless (← tag literal) == "natVal" do throw "Unsupported literal"
      pure (.lit (.natVal (← (← literal.getArrVal? 1).getNat?)))
    | t => throw s!"Unsupported Expr AST tag: {t}"

def unwrap {α : Type} (r : Except String α) : CommandElabM α :=
  match r with
  | .ok x => pure x
  | .error msg => throwError "{msg}"

def checkControls : CommandElabM Unit := do
  let env ← getEnv
  let positive := Expr.app (Expr.lam `h (.const ``Nat []) (.bvar 0) .default)
    (.const ``Nat.zero [])
  match Kernel.check env {} positive with
  | .ok _ => pure ()
  | .error ex => throwError "Kernel positive control failed: {ex.toMessageData (← getOptions)}"
  let negative := Expr.app (Expr.lam `h (.const ``Nat []) (.bvar 0) .default)
    (.const ``True.intro [])
  match Kernel.check env {} negative with
  | .error _ => pure ()
  | .ok _ => throwError "Kernel accepted deliberately ill-typed negative control"

def checkRecord (row : Json) : CommandElabM Json := do
  let nameText ← unwrap (row.getObjValAs? String "name")
  let name ← unwrap (do decodeName 512 (← row.getObjVal? "nameAST"))
  unless name.toString == nameText do throwError "Declaration name transport mismatch: {nameText}"
  let levels ← unwrap (do
    let a ← (← row.getObjVal? "levelParamsAST").getArr?
    a.mapM (decodeName 512))
  let baselineLevels ← unwrap (row.getObjValAs? (Array String) "levelParams")
  let finalLevels ← unwrap (row.getObjValAs? (Array String) "currentLevelParams")
  unless levels.map Name.toString == baselineLevels && baselineLevels == finalLevels do
    throwError "Universe parameter transport mismatch: {nameText}"
  let oldType ← unwrap (do decodeExpr 512 (← row.getObjVal? "baselineTypeAST"))
  let baselineRepr ← unwrap (row.getObjValAs? String "baselineRepr")
  unless reprStr oldType == baselineRepr do throwError "Original Expr repr roundtrip failed: {nameText}"
  if oldType.hasMVar || oldType.hasFVar || oldType.hasLooseBVars then
    throwError "Original Expr is not closed: {nameText}"
  unless (collectLevelParams {} oldType).params.all (levels.contains ·) do
    throwError "Original Expr has undeclared universe parameters: {nameText}"
  let env ← getEnv
  let some info := env.find? name | throwError "Missing current declaration: {nameText}"
  unless info.levelParams == levels.toList do throwError "Current universe parameters differ: {nameText}"
  let currentRepr ← unwrap (row.getObjValAs? String "currentRepr")
  unless reprStr info.type == currentRepr do throwError "Current Expr differs from final captured manifest: {nameText}"
  unless baselineRepr != currentRepr do throwError "Unexpected raw-identical record in conversion set: {nameText}"
  let current := Expr.const name (levels.toList.map Level.param)
  let headerAuditor : Option Name :=
    if nameText == "TransposeFollowup.NativePaddedField.tail_trace" then
      some ``TransposeFollowup.NativePaddedField.R1912_original_header_tail_trace
    else if nameText == "TransposeFollowup.CountedFill.emit_step" then
      some ``TransposeFollowup.CountedFill.R1912_original_header_emit_step
    else none
  let checkedType ← match headerAuditor with
    | none => pure oldType
    | some auditor => do
      let some headerInfo := env.find? auditor | throwError "Missing kernel-checked original header: {nameText}"
      unless headerInfo.levelParams == levels.toList do throwError "Header universe parameters differ: {nameText}"
      pure headerInfo.type
  -- The two exceptional records use the exact archived source-header statement,
  -- because their old Expr references contain retired generated proof constants.
  -- They are never reported as exact old-Expr conversions.
  let checkedType := ShareCommon.shareCommon checkedType
  if headerAuditor.isNone then
    unless reprStr checkedType == baselineRepr do throwError "Sharing changed Expr repr: {nameText}"
  let application := Expr.app (Expr.lam `r1912_original_type checkedType (.bvar 0) .default) current
  match Kernel.check env {} application with
  | .error ex => throwError "Preserved statement kernel check failed for {nameText}: {ex.toMessageData (← getOptions)}"
  | .ok _ => pure ()
  pure (Json.mkObj [
    ("name", toJson nameText),
    ("levelParams", toJson baselineLevels),
    ("original_repr_roundtrip_exact", toJson true),
    ("current_repr_matches_final_capture", toJson true),
    ("ordered_universe_parameters_exact", toJson true),
    ("validation_route", toJson (if headerAuditor.isNone then "original_expr_kernel" else "archived_source_header_kernel")),
    ("kernel_identity_application_checked", toJson headerAuditor.isNone),
    ("original_source_header_kernel_checked", toJson headerAuditor.isSome),
    ("auditor_declaration", toJson (headerAuditor.map Name.toString)),
    ("baselineReprSHA256", ← unwrap (row.getObjVal? "baselineReprSHA256")),
    ("currentReprSHA256", ← unwrap (row.getObjVal? "currentReprSHA256"))])

def runChunk (input output : String) : CommandElabM Unit := do
  if ← liftIO (System.FilePath.pathExists output) then
    throwError "Refusing to overwrite existing check result: {output}"
  let json ← unwrap (Json.parse (← liftIO (IO.FS.readFile input)))
  let rows ← unwrap (do (← json.getObjVal? "declarations").getArr?)
  let expected ← unwrap (json.getObjValAs? Nat "expectedDeclarations")
  unless rows.size == expected && expected > 0 && expected ≤ 8 do
    throwError "Unexpected conversion chunk cardinality"
  checkControls
  let results ← rows.mapM checkRecord
  let outputJson := Json.mkObj [
    ("format", toJson "r1912-kernel-type-conversion-chunk-v1"),
    ("status", toJson "passed"),
    ("input", toJson input),
    ("checked_declarations", toJson results.size),
    ("kernel_positive_and_negative_controls", toJson true),
    ("comparisonSHA256", ← unwrap (json.getObjVal? "comparisonSHA256")),
    ("decoderSHA256", ← unwrap (json.getObjVal? "decoderSHA256")),
    ("results", toJson results)]
  liftIO (IO.FS.writeFile output outputJson.compress)
  logInfo m!"R1912 kernel conversion chunk passed: {input} ({results.size} declarations)"

end R1912TypeConversionAudit

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/000.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-000.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/001.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-001.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/002.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-002.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/003.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-003.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/004.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-004.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/005.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-005.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/006.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-006.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/007.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-007.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/008.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-008.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/009.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-009.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/010.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-010.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/011.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-011.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/012.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-012.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/013.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-013.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/014.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-014.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/015.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-015.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/016.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-016.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/017.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-017.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/018.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-018.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/019.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-019.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/020.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-020.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/021.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-021.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/022.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-022.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/023.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-023.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/024.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-024.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/025.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-025.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/026.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-026.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/027.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-027.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/028.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-028.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/029.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-029.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/030.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-030.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/031.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-031.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/032.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-032.json"

run_cmd R1912TypeConversionAudit.runChunk "external/temporary/r1912-original-types-ast-chunks/033.json" "external/temporary/r1912-kernel-type-conversion-v2/r1912-kernel-type-conversion-033.json"
