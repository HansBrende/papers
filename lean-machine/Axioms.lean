import LeanMachine

/-! Run `lake env lean Axioms.lean`: every exported theorem of lean-machine should depend at most on
`propext`, `Classical.choice` and `Quot.sound`. Add each new exported theorem here. -/

-- TutteBerge/Berge.lean (external, jtraverso/berge-matching)
#print axioms BergeMatching.isMaximum_iff_not_exists_augmenting
#print axioms BergeMatching.two_mul_card_add_le
#print axioms BergeMatching.exists_tutte_berge

-- TutteBerge/MatchingNumber.lean
#print axioms SimpleGraph.le_matchingNumber
#print axioms SimpleGraph.exists_isMatching_ncard_eq_matchingNumber
#print axioms SimpleGraph.two_mul_matchingNumber_add_oddCount_le
#print axioms SimpleGraph.exists_two_mul_matchingNumber_add_oddCount_eq
#print axioms SimpleGraph.biUnion_componentBlocks
#print axioms SimpleGraph.pairwiseDisjoint_componentBlocks
#print axioms SimpleGraph.not_adj_of_mem_componentBlocks
#print axioms SimpleGraph.two_mul_sum_card_div_two_add_oddCount
#print axioms SimpleGraph.matchingNumber_le_card_add_sum_card_div_two
#print axioms SimpleGraph.exists_card_add_sum_card_div_two_eq_matchingNumber
#print axioms SimpleGraph.Subgraph.IsMatching.exists_fin_enum

-- RankCertificate.lean
#print axioms LeanMachine.RankCertificate.rank_identity
#print axioms LeanMachine.RankCertificate.rank_identity_int

-- ColorOrder.lean
#print axioms LeanMachine.ColorOrder.eq_of_agree_on_record
#print axioms LeanMachine.ColorOrder.card_le_pow_record
#print axioms LeanMachine.ColorOrder.card_le_pow_half

-- IncidenceTrimming.lean
#print axioms LeanMachine.IncidenceTrimming.sum_leftDegree_eq_sum_rightDegree
#print axioms LeanMachine.IncidenceTrimming.sum_leftDegree_le
#print axioms LeanMachine.IncidenceTrimming.heavy_card_mul_succ_le
#print axioms LeanMachine.IncidenceTrimming.heavy_card_le
#print axioms LeanMachine.IncidenceTrimming.retained_card_add_heavy_card
#print axioms LeanMachine.IncidenceTrimming.leftDegreeOn_le
#print axioms LeanMachine.IncidenceTrimming.rightDegreeOn_le
#print axioms LeanMachine.IncidenceTrimming.retained_leftDegree_le
#print axioms LeanMachine.IncidenceTrimming.degree_trimming

-- MatrixRankCertificate.lean
#print axioms LeanMachine.MatrixRankCertificate.finrank_range_tensorProduct_map
#print axioms LeanMachine.MatrixRankCertificate.rank_kronecker
#print axioms LeanMachine.MatrixRankCertificate.finrank_range_piMap
#print axioms LeanMachine.MatrixRankCertificate.rank_add_le
#print axioms LeanMachine.MatrixRankCertificate.rank_sum_le
#print axioms LeanMachine.MatrixRankCertificate.rank_diagonalBlocks
#print axioms LeanMachine.MatrixRankCertificate.rank_blocks_le
#print axioms LeanMachine.MatrixRankCertificate.matrix_rank_identity
#print axioms LeanMachine.MatrixRankCertificate.rank_amplify
#print axioms LeanMachine.MatrixRankCertificate.matrix_label_certificate
#print axioms LeanMachine.MatrixRankCertificate.supported_matrix_label_certificate
#print axioms LeanMachine.MatrixRankCertificate.rank_map_field
#print axioms LeanMachine.MatrixRankCertificate.supported_matrix_label_certificate_extension

-- LinearRecovery.lean
#print axioms LeanMachine.LinearRecovery.IsRecoverable.exists_coeffs
#print axioms LeanMachine.LinearRecovery.IsRecoverable.exists_recovery_matrix
#print axioms LeanMachine.LinearRecovery.finrank_add_rank_le
#print axioms LeanMachine.LinearRecovery.isBlockRecoverable_of_decoder
#print axioms LeanMachine.LinearRecovery.IsBlockRecoverable.exists_recovery_matrix
#print axioms LeanMachine.LinearRecovery.IsBlockRecoverable.finrank_bound_of_matrix_labels

-- BucketChains.lean
#print axioms LeanMachine.BucketChains.card_le_of_comparable
#print axioms LeanMachine.BucketChains.card_le_of_oppositely_comparable
#print axioms LeanMachine.BucketChains.card_image_mono
#print axioms LeanMachine.BucketChains.card_image_antitone

-- ThresholdCuts.lean and ThresholdPullback.lean
#print axioms LeanMachine.ThresholdPullback.Cut.monotone_holds
#print axioms LeanMachine.ThresholdPullback.Cut.antitone_holds
#print axioms LeanMachine.ThresholdPullback.exists_upper_cut
#print axioms LeanMachine.ThresholdPullback.exists_lower_cut
#print axioms LeanMachine.ThresholdPullback.PartialMap.injective
#print axioms LeanMachine.ThresholdPullback.exists_pullback_cut
#print axioms LeanMachine.ThresholdPullback.band_single_card
#print axioms LeanMachine.ThresholdPullback.bandPreimage_card
#print axioms LeanMachine.ThresholdPullback.bandAmbiguity_card
#print axioms LeanMachine.ThresholdPullback.band_threshold_iff
#print axioms LeanMachine.ThresholdPullback.band_cut_iff
#print axioms LeanMachine.ThresholdPullback.mem_mapPreimage
#print axioms LeanMachine.ThresholdPullback.mapPreimage_card
#print axioms LeanMachine.ThresholdPullback.word_threshold_pullback

-- CanonicalBuckets.lean
#print axioms LeanMachine.CanonicalBuckets.bucket_monotone
#print axioms LeanMachine.CanonicalBuckets.bucket_fibre_card

-- GraphBall.lean
#print axioms LeanMachine.GraphBall.closedBall_zero
#print axioms LeanMachine.GraphBall.closedBall_succ_subset
#print axioms LeanMachine.GraphBall.card_closedBall_le
#print axioms LeanMachine.GraphBall.card_edist_le

-- FinitePacking.lean
#print axioms LeanMachine.FinitePacking.exists_disjoint_subfamily
#print axioms LeanMachine.FinitePacking.card_le_of_disjoint_bound

-- PathPacking.lean
#print axioms LeanMachine.PathPacking.edist_start_le_of_mem_support
#print axioms LeanMachine.PathPacking.support_multiplicity_le_ball
#print axioms LeanMachine.PathPacking.fixed_length_count
#print axioms LeanMachine.PathPacking.odd_length_count

-- SmithRankLoss.lean
#print axioms LeanMachine.SmithRankLoss.rank_map_of_diagonalization
#print axioms LeanMachine.SmithRankLoss.rank_loss_eq
#print axioms LeanMachine.SmithRankLoss.rank_mod_le_rank_rat
#print axioms LeanMachine.SmithRankLoss.loss_count_lower_bound

-- KernelRangeBound.lean
#print axioms LeanMachine.finrank_add_le_of_ker_range
#print axioms LeanMachine.twice_finrank_le_quotient_add_of_ker_range
#print axioms LeanMachine.finrank_add_span_le_of_split_generators

-- HomogeneousInflation.lean
#print axioms LeanMachine.HomogeneousInflation.sheetCheck
#print axioms LeanMachine.HomogeneousInflation.inflatedCheck
#print axioms LeanMachine.HomogeneousInflation.sheetReindex
#print axioms LeanMachine.HomogeneousInflation.reindex_inflated
#print axioms LeanMachine.HomogeneousInflation.kernelEquiv
#print axioms LeanMachine.HomogeneousInflation.finrank_kernel_inflated
#print axioms LeanMachine.HomogeneousInflation.rate_cross_product

-- FiniteProjection.lean
#print axioms LeanMachine.FiniteProjection.mem_vanishing
#print axioms LeanMachine.FiniteProjection.vanishing_antitone
#print axioms LeanMachine.FiniteProjection.vanishing_univ
#print axioms LeanMachine.FiniteProjection.dimension_le
#print axioms LeanMachine.FiniteProjection.step_bound

-- SubspaceDefect.lean
#print axioms LeanMachine.SubspaceDefect.defect_bot
#print axioms LeanMachine.SubspaceDefect.defect_top
#print axioms LeanMachine.SubspaceDefect.intersection_supermodular
#print axioms LeanMachine.SubspaceDefect.submodular
#print axioms LeanMachine.SubspaceDefect.tight_inf_sup
#print axioms LeanMachine.SubspaceDefect.exact_join_of_equality
#print axioms LeanMachine.SubspaceDefect.tight_exact_join
#print axioms LeanMachine.SubspaceDefect.quotient_image_dimension
#print axioms LeanMachine.SubspaceDefect.deficit_of_quotient_half
#print axioms LeanMachine.SubspaceDefect.pairwise_disjoint_of_positive
#print axioms LeanMachine.SubspaceDefect.exact_intersections
#print axioms LeanMachine.SubspaceDefect.tight_spanned
#print axioms LeanMachine.SubspaceDefect.restriction_dimension
#print axioms LeanMachine.SubspaceDefect.restricted_span
#print axioms LeanMachine.SubspaceDefect.image_span

-- SubspaceRecovery.lean
#print axioms LeanMachine.SubspaceRecovery.Recovery.reconstruct
#print axioms LeanMachine.SubspaceRecovery.Recovery.row_le
#print axioms LeanMachine.SubspaceRecovery.Recovery.partial_sum_mem
#print axioms LeanMachine.SubspaceRecovery.Recovery.component_range_le_of_rest
#print axioms LeanMachine.SubspaceRecovery.imageMap_val
#print axioms LeanMachine.SubspaceRecovery.imageMap_surjective
#print axioms LeanMachine.SubspaceRecovery.Recovery.image
#print axioms LeanMachine.SubspaceRecovery.Recovery.restrict
#print axioms LeanMachine.SubspaceRecovery.finrank_finset_sup_le
#print axioms LeanMachine.SubspaceRecovery.Recovery.le_row_span
#print axioms LeanMachine.SubspaceRecovery.Recovery.strict_row_span
#print axioms LeanMachine.SubspaceRecovery.Recovery.strict_row_dimension

-- LinearCodeRecovery.lean
#print axioms LeanMachine.SubspaceRecovery.recovery_of_generators
#print axioms LeanMachine.SubspaceRecovery.coordinate_apply
#print axioms LeanMachine.SubspaceRecovery.coordinate_duals_span
#print axioms LeanMachine.SubspaceRecovery.code_dual_recovery
#print axioms LeanMachine.SubspaceRecovery.blockOperator_apply
#print axioms LeanMachine.SubspaceRecovery.blockOperator_single
#print axioms LeanMachine.SubspaceRecovery.block_kernel_recovery

-- SubspaceFamilies.lean
#print axioms LeanMachine.SubspaceDefect.family_mass_le
#print axioms LeanMachine.SubspaceDefect.exact_finite_family
#print axioms LeanMachine.SubspaceDefect.line_le_or_disjoint

-- SubspaceGrowth.lean
#print axioms LeanMachine.SubspaceDefect.line_extension_dimension
#print axioms LeanMachine.SubspaceDefect.line_coordinate_gain
#print axioms LeanMachine.SubspaceDefect.plane_gain_forces_intersection

-- SubspaceGains.lean
#print axioms LeanMachine.SubspaceDefect.coordinate_gain_count
#print axioms LeanMachine.SubspaceDefect.tight_growth_gain_budget

-- SparseProjection.lean and BlockRankSparsity.lean
#print axioms LeanMachine.SparseProjection.projection_rank_le_support
#print axioms LeanMachine.SparseProjection.sum_projection_ranks_le
#print axioms LeanMachine.SparseProjection.rowFamily_span
#print axioms LeanMachine.SparseProjection.sum_column_ranks_le

-- CoordinateSplitting.lean and ProjectionFamilies.lean
#print axioms LeanMachine.CoordinateSplitting.range_split
#print axioms LeanMachine.CoordinateSplitting.range_split_disjoint
#print axioms LeanMachine.CoordinateSplitting.coordinate_rank_split
#print axioms LeanMachine.CoordinateSplitting.rank_factor_eq
#print axioms LeanMachine.CoordinateSplitting.rank_sum_of_extraction
#print axioms LeanMachine.CoordinateSplitting.projection_sum_rank
#print axioms LeanMachine.CoordinateSplitting.observed_projection_sum_rank
#print axioms LeanMachine.CoordinateSplitting.projection_sum_extract
#print axioms LeanMachine.CoordinateSplitting.projection_sum_idempotent
#print axioms LeanMachine.CoordinateSplitting.projection_sum_ker
#print axioms LeanMachine.CoordinateSplitting.half_of_residual

-- InvariantKernel.lean
#print axioms LeanMachine.InvariantKernel.finrank_ker_eq

-- IntervalCover.lean
#print axioms LeanMachine.IntervalCover.exists_cover_packing
#print axioms LeanMachine.IntervalCover.packing_le_fractional_cover
#print axioms LeanMachine.IntervalCover.exists_subcover_le_weight

-- FiniteIncidence.lean
#print axioms LeanMachine.FiniteIncidence.sum_eq_sum_multiplicity
#print axioms LeanMachine.FiniteIncidence.multiplicity_le_of_coloring

-- MonotonePatches.lean
#print axioms LeanMachine.MonotonePatches.mem_jumpEdges
#print axioms LeanMachine.MonotonePatches.crossings_le_twice_down_add_one
#print axioms LeanMachine.MonotonePatches.downcrossings_le_one
#print axioms LeanMachine.MonotonePatches.crossings_le_three
#print axioms LeanMachine.MonotonePatches.variation_comp_le_crossings
#print axioms LeanMachine.MonotonePatches.variation_comp_le
#print axioms LeanMachine.MonotonePatches.variation_patch_le_three
#print axioms LeanMachine.MonotonePatches.Action.apply_eq
#print axioms LeanMachine.MonotonePatches.Action.apply_eq_self
#print axioms LeanMachine.MonotonePatches.Action.apply_ne_self_iff
#print axioms LeanMachine.MonotonePatches.Action.apply_le
#print axioms LeanMachine.MonotonePatches.Action.apply_monotone
#print axioms LeanMachine.MonotonePatches.Action.success_cons_iff
#print axioms LeanMachine.MonotonePatches.Action.success_structure
#print axioms LeanMachine.MonotonePatches.Action.endpoint_le
#print axioms LeanMachine.MonotonePatches.Action.variation_successfulMap
#print axioms LeanMachine.MonotonePatches.Patch.apply_eq_self
#print axioms LeanMachine.MonotonePatches.Patch.apply_mem
#print axioms LeanMachine.MonotonePatches.Patch.threshold_iff
#print axioms LeanMachine.MonotonePatches.Patch.Separated.unique_time
#print axioms LeanMachine.MonotonePatches.Patch.pack_eq_on
#print axioms LeanMachine.MonotonePatches.Patch.pack_cases
#print axioms LeanMachine.MonotonePatches.Patch.pack_le
#print axioms LeanMachine.MonotonePatches.Patch.pack_threshold
#print axioms LeanMachine.MonotonePatches.Patch.pack_threshold_outside
#print axioms LeanMachine.MonotonePatches.crossings_congr
#print axioms LeanMachine.MonotonePatches.variation_pack
#print axioms LeanMachine.MonotonePatches.exists_sharp_patch

-- PeriodicPhases.lean
#print axioms LeanMachine.PeriodicPhases.unit_chain_card_lt
#print axioms LeanMachine.PeriodicPhases.available_card
#print axioms LeanMachine.PeriodicPhases.protected_not_deleted
#print axioms LeanMachine.PeriodicPhases.sum_payment_le
#print axioms LeanMachine.PeriodicPhases.sum_available_payment_le

-- ThinIntervals.lean
#print axioms LeanMachine.ThinIntervals.Model.isAcyclic
#print axioms LeanMachine.ThinIntervals.Model.eq_container_of_adj
#print axioms LeanMachine.ThinIntervals.Model.not_nonleaf_of_contained
#print axioms LeanMachine.ThinIntervals.Model.nonleaf_left_injective
#print axioms LeanMachine.ThinIntervals.Model.nonleaf_right_strict
#print axioms LeanMachine.ThinIntervals.Model.no_nonleaf_between
#print axioms LeanMachine.ThinIntervals.Model.nonleaf_or_endpoint
#print axioms LeanMachine.ThinIntervals.Model.nonleaf_getVert
#print axioms LeanMachine.ThinIntervals.Model.nonleaf_reachable
#print axioms LeanMachine.ThinIntervals.Model.spineRank_pos
#print axioms LeanMachine.ThinIntervals.Model.spineRank_strict
#print axioms LeanMachine.ThinIntervals.Model.spineRank_injective
#print axioms LeanMachine.ThinIntervals.Model.spineRank_step
#print axioms LeanMachine.ThinIntervals.Model.spineRank_adj
#print axioms LeanMachine.ThinIntervals.Model.nonleaf_neighbors_card_le_two
#print axioms LeanMachine.ThinIntervals.Model.path_card_le_of_avoids

-- FiniteOrbits.lean
#print axioms LeanMachine.FiniteOrbits.mem_cloud_self
#print axioms LeanMachine.FiniteOrbits.cloud_mono
#print axioms LeanMachine.FiniteOrbits.cloud_card_le_chain
#print axioms LeanMachine.FiniteOrbits.cloud_card_le
#print axioms LeanMachine.FiniteOrbits.wordOrbit_image
#print axioms LeanMachine.FiniteOrbits.reduce_word
#print axioms LeanMachine.FiniteOrbits.endpoint_mem_cloud
#print axioms LeanMachine.FiniteOrbits.cloud_subset_orbit
#print axioms LeanMachine.FiniteOrbits.orbit_eq_cloud

-- Exact packed source banks
#print axioms LeanMachine.MonotonePatches.Action.endpoint_append
#print axioms LeanMachine.MonotonePatches.Action.success_append
#print axioms LeanMachine.MonotonePatches.Action.successfulAction_apply
#print axioms LeanMachine.PeriodicPhases.unit_chain_window
#print axioms LeanMachine.PeriodicPhases.unit_chain_mod_injective
#print axioms LeanMachine.FiniteOrbits.wordOrbit_mono
#print axioms LeanMachine.FiniteOrbits.wordOrbit_trans
#print axioms LeanMachine.ThinIntervals.Model.component_span_contains
#print axioms LeanMachine.ThinIntervals.Model.component_span_exact
#print axioms LeanMachine.ThinIntervals.Model.component_spans_disjoint
#print axioms LeanMachine.SourceBank.bounded_mono
#print axioms LeanMachine.SourceBank.Bounded.unit_variation
#print axioms LeanMachine.SourceBank.bounded_compose
#print axioms LeanMachine.SourceBank.ordered_length
#print axioms LeanMachine.SourceBank.bounded_ordered
#print axioms LeanMachine.PackedWords.System.success_owner
#print axioms LeanMachine.PackedWords.System.success_pairwise
#print axioms LeanMachine.PackedWords.System.success_nodup
#print axioms LeanMachine.PackedWords.System.success_chain
#print axioms LeanMachine.PackedWords.System.word_unique
#print axioms LeanMachine.PackedWords.System.wordAt_unique
#print axioms LeanMachine.PackedWords.System.chosenWord_eq
#print axioms LeanMachine.PackedWords.System.endpoint_component
#print axioms LeanMachine.PackedWords.System.wordPatches_separated
#print axioms LeanMachine.PackedWords.System.bank_length
#print axioms LeanMachine.PackedWords.System.bank_bounded
#print axioms LeanMachine.PackedWords.System.bank_exact

-- Supporting public declarations of the packed source-bank modules
#print axioms LeanMachine.ThinIntervals.Model.mem_componentVertices
#print axioms LeanMachine.ThinIntervals.Model.componentVertices_nonempty
#print axioms LeanMachine.PackedWords.System.active_owner
#print axioms LeanMachine.PackedWords.System.head_last_order
#print axioms LeanMachine.PackedWords.System.success_component
#print axioms LeanMachine.PackedWords.System.chosenWord_spec
#print axioms LeanMachine.PackedWords.System.chosenWord_members
#print axioms LeanMachine.PackedWords.System.packedMap_sound
#print axioms LeanMachine.SourceBank.mem_values
#print axioms LeanMachine.SourceBank.cost_append
#print axioms LeanMachine.SourceBank.bounded_append
#print axioms LeanMachine.SourceBank.bounded_identity
#print axioms LeanMachine.SourceBank.compose_length
#print axioms LeanMachine.SourceBank.mem_compose
#print axioms LeanMachine.SourceBank.bounded_action

-- ShiftedGrid.lean
#print axioms LeanMachine.ShiftedGrid.label
#print axioms LeanMachine.ShiftedGrid.separatingShifts
#print axioms LeanMachine.ShiftedGrid.label_mono
#print axioms LeanMachine.ShiftedGrid.label_ne_iff
#print axioms LeanMachine.ShiftedGrid.separatingShifts_card
#print axioms LeanMachine.ShiftedGrid.separatingShifts_card_le
#print axioms LeanMachine.ShiftedGrid.constant_iff_extrema_eq
#print axioms LeanMachine.ShiftedGrid.nonconstant_iff_extrema_ne
#print axioms LeanMachine.ShiftedGrid.nonconstantShifts
#print axioms LeanMachine.ShiftedGrid.nonconstantShifts_card
#print axioms LeanMachine.ShiftedGrid.nonconstantShifts_card_le
#print axioms LeanMachine.ShiftedGrid.sub_lt_of_label_eq
#print axioms LeanMachine.ShiftedGrid.card_le_of_constant

-- IntervalOscillation.lean
#print axioms LeanMachine.IntervalOscillation.times
#print axioms LeanMachine.IntervalOscillation.times_nonempty
#print axioms LeanMachine.IntervalOscillation.lower
#print axioms LeanMachine.IntervalOscillation.upper
#print axioms LeanMachine.IntervalOscillation.oscillation
#print axioms LeanMachine.IntervalOscillation.lower_attained
#print axioms LeanMachine.IntervalOscillation.upper_attained
#print axioms LeanMachine.IntervalOscillation.lower_le
#print axioms LeanMachine.IntervalOscillation.le_upper
#print axioms LeanMachine.IntervalOscillation.lower_le_upper
#print axioms LeanMachine.IntervalOscillation.mem_times
#print axioms LeanMachine.IntervalOscillation.dist_le_interval_variation
#print axioms LeanMachine.IntervalOscillation.oscillation_le_interval_variation
#print axioms LeanMachine.IntervalOscillation.multiplicity
#print axioms LeanMachine.IntervalOscillation.sum_oscillation_le_profile
#print axioms LeanMachine.IntervalOscillation.sum_oscillation_le_mul_variation

-- GridPayment.lean
#print axioms LeanMachine.GridPayment.cut
#print axioms LeanMachine.GridPayment.cut_subset
#print axioms LeanMachine.GridPayment.labels_eq_of_not_mem_cut
#print axioms LeanMachine.GridPayment.sum_cut_card_le_capped
#print axioms LeanMachine.GridPayment.sum_cut_card_le_oscillation
#print axioms LeanMachine.GridPayment.average_cut_card_le_capped
#print axioms LeanMachine.GridPayment.average_cut_card_le_oscillation
#print axioms LeanMachine.GridPayment.average_cut_card_le_profile
#print axioms LeanMachine.GridPayment.average_cut_card_le_mul_variation
#print axioms LeanMachine.GridPayment.exists_cut_card_le

-- CausalRecovery.lean
#print axioms LeanMachine.CausalRecovery.Ancestor
#print axioms LeanMachine.CausalRecovery.sourceCone
#print axioms LeanMachine.CausalRecovery.Ancestor.trans
#print axioms LeanMachine.CausalRecovery.Ancestor.le
#print axioms LeanMachine.CausalRecovery.reads_subset_sourceCone
#print axioms LeanMachine.CausalRecovery.sourceCone_subset_of_ancestor
#print axioms LeanMachine.CausalRecovery.sourceCone_subset
#print axioms LeanMachine.CausalRecovery.LocallyDetermined
#print axioms LeanMachine.CausalRecovery.record_eq_of_sourceCone
#print axioms LeanMachine.CausalRecovery.record_eq_of_closed_sources
#print axioms LeanMachine.CausalRecovery.observation
#print axioms LeanMachine.CausalRecovery.exists_decoder

-- OrderedRecovery.lean
#print axioms LeanMachine.OrderedRecovery.eq_of_wellFounded
#print axioms LeanMachine.OrderedRecovery.eq_of_rank

-- FrozenBank.lean
#print axioms LeanMachine.FrozenBank.dist_le_oscillation
#print axioms LeanMachine.FrozenBank.radius
#print axioms LeanMachine.FrozenBank.oscillation_le_radius
#print axioms LeanMachine.FrozenBank.radius_le_sum
#print axioms LeanMachine.FrozenBank.label_dist_le
#print axioms LeanMachine.FrozenBank.block_dist_le
#print axioms LeanMachine.FrozenBank.sum_radius_le_profile
#print axioms LeanMachine.FrozenBank.sum_radius_le_variation

-- GapErosion.lean
#print axioms LeanMachine.GapErosion.remaining
#print axioms LeanMachine.GapErosion.loss_le
#print axioms LeanMachine.GapErosion.pointArea
#print axioms LeanMachine.GapErosion.erodedArea
#print axioms LeanMachine.GapErosion.area_loss
#print axioms LeanMachine.GapErosion.weight_sum_le_half

-- CyclicSelection.lean
#print axioms LeanMachine.CyclicSelection.arc
#print axioms LeanMachine.CyclicSelection.rank
#print axioms LeanMachine.CyclicSelection.rank_rotate
#print axioms LeanMachine.CyclicSelection.rank_lt
#print axioms LeanMachine.CyclicSelection.rank_nonneg
#print axioms LeanMachine.CyclicSelection.forward
#print axioms LeanMachine.CyclicSelection.forward_of_le
#print axioms LeanMachine.CyclicSelection.forward_of_gt
#print axioms LeanMachine.CyclicSelection.rank_eq_forward
#print axioms LeanMachine.CyclicSelection.forward_lt
#print axioms LeanMachine.CyclicSelection.mod_add_forward
#print axioms LeanMachine.CyclicSelection.forward_rotate
#print axioms LeanMachine.CyclicSelection.covered
#print axioms LeanMachine.CyclicSelection.overcover
#print axioms LeanMachine.CyclicSelection.mem_overcover
#print axioms LeanMachine.CyclicSelection.overcover_subset
#print axioms LeanMachine.CyclicSelection.anchors_subset_overcover
#print axioms LeanMachine.CyclicSelection.overcover_nonempty
#print axioms LeanMachine.CyclicSelection.covered_of_dist_le
#print axioms LeanMachine.CyclicSelection.arc_subset
#print axioms LeanMachine.CyclicSelection.arc_card
#print axioms LeanMachine.CyclicSelection.point
#print axioms LeanMachine.CyclicSelection.gap
#print axioms LeanMachine.CyclicSelection.point_mem
#print axioms LeanMachine.CyclicSelection.point_zero
#print axioms LeanMachine.CyclicSelection.point_card
#print axioms LeanMachine.CyclicSelection.point_mono
#print axioms LeanMachine.CyclicSelection.point_strict
#print axioms LeanMachine.CyclicSelection.gap_pos
#print axioms LeanMachine.CyclicSelection.sum_gap
#print axioms LeanMachine.CyclicSelection.gap_le
#print axioms LeanMachine.CyclicSelection.exists_point_eq
#print axioms LeanMachine.CyclicSelection.anchor_offset_zero_or_gap_le
#print axioms LeanMachine.CyclicSelection.erodedArc
#print axioms LeanMachine.CyclicSelection.erodedArc_uncovered
#print axioms LeanMachine.CyclicSelection.erodedArc_card
#print axioms LeanMachine.CyclicSelection.erodedArc_disjoint_overcover
#print axioms LeanMachine.CyclicSelection.erodedArc_lift
#print axioms LeanMachine.CyclicSelection.erodedArc_pairwiseDisjoint
#print axioms LeanMachine.CyclicSelection.activeGaps
#print axioms LeanMachine.CyclicSelection.sum_active_lengths_add_one_le

-- CyclicArcSelection.lean
#print axioms LeanMachine.CyclicSelection.orientedRank
#print axioms LeanMachine.CyclicSelection.orientedRankNat
#print axioms LeanMachine.CyclicSelection.orientedRank_lt_iff_nat
#print axioms LeanMachine.CyclicSelection.selectingOrders
#print axioms LeanMachine.CyclicSelection.mem_selectingOrders_iff_nat
#print axioms LeanMachine.CyclicSelection.arc_selection_card_lower
#print axioms LeanMachine.CyclicSelection.arc_selection_card_lower_of_mem

-- PeriodicStripe.lean
#print axioms LeanMachine.PeriodicStripe.occupied
#print axioms LeanMachine.PeriodicStripe.occupied_periodic
#print axioms LeanMachine.PeriodicStripe.occupied_iff_column
#print axioms LeanMachine.PeriodicStripe.count_prefix_short
#print axioms LeanMachine.PeriodicStripe.count_period
#print axioms LeanMachine.PeriodicStripe.count_add_period
#print axioms LeanMachine.PeriodicStripe.count_mul_period
#print axioms LeanMachine.PeriodicStripe.count_prefix
#print axioms LeanMachine.PeriodicStripe.centered
#print axioms LeanMachine.PeriodicStripe.centered_eq_remainder
#print axioms LeanMachine.PeriodicStripe.centered_bounds
#print axioms LeanMachine.PeriodicStripe.arcCount
#print axioms LeanMachine.PeriodicStripe.scaled_arcCount_eq_centered_sub
#print axioms LeanMachine.PeriodicStripe.abs_scaled_arcCount_sub_le
#print axioms LeanMachine.PeriodicStripe.stripe
#print axioms LeanMachine.PeriodicStripe.mem_stripe_iff
#print axioms LeanMachine.PeriodicStripe.occupied_mod_circle
#print axioms LeanMachine.PeriodicStripe.pairwiseDisjoint_stripe
#print axioms LeanMachine.PeriodicStripe.biUnion_stripe
#print axioms LeanMachine.PeriodicStripe.sum_stripe_inter_card
#print axioms LeanMachine.PeriodicStripe.stripe_inter_arc_card
#print axioms LeanMachine.PeriodicStripe.abs_arcCount_sub_density_le
#print axioms LeanMachine.PeriodicStripe.abs_stripe_inter_arc_sub_density_le
#print axioms LeanMachine.PeriodicStripe.weighted_arcCount_lower_bound

-- SelectionAverage.lean
#print axioms LeanMachine.SelectionAverage.pointCount
#print axioms LeanMachine.SelectionAverage.sum_card_inter_eq_sum_pointCount
#print axioms LeanMachine.SelectionAverage.sum_credit_mul_card_inter_le

-- PeriodicStripeSum.lean
#print axioms LeanMachine.PeriodicStripe.sum_stripe_eq_sum_coordinates
#print axioms LeanMachine.PeriodicStripe.sum_fin_stripe_eq_sum_coordinates
#print axioms LeanMachine.PeriodicStripe.sum_fin_stripe_eq_sum_coordinates_of_pos

-- CyclicStripeAverage.lean
#print axioms LeanMachine.CyclicStripeAverage.sum_credit_le_selectingOrders
#print axioms LeanMachine.CyclicStripeAverage.erodedArea_lower
#print axioms LeanMachine.CyclicStripeAverage.pointArea_lower

-- FractionalCover.lean
#print axioms LeanMachine.FractionalCover.Covers
#print axioms LeanMachine.FractionalCover.cost
#print axioms LeanMachine.FractionalCover.cost_nonneg
#print axioms LeanMachine.FractionalCover.one_le_cost
#print axioms LeanMachine.FractionalCover.cap_covers
#print axioms LeanMachine.FractionalCover.cap_cost_le
#print axioms LeanMachine.FractionalCover.covers_closed
#print axioms LeanMachine.FractionalCover.exists_minimum
#print axioms LeanMachine.FractionalCover.value
#print axioms LeanMachine.FractionalCover.exists_optimal
#print axioms LeanMachine.FractionalCover.value_nonneg
#print axioms LeanMachine.FractionalCover.one_le_value
#print axioms LeanMachine.FractionalCover.number
#print axioms LeanMachine.FractionalCover.number_ne_top_iff
#print axioms LeanMachine.FractionalCover.number_toReal

-- FractionalCoverBounds.lean
#print axioms LeanMachine.FractionalCover.value_le_cost
#print axioms LeanMachine.FractionalCover.number_toReal_le_cost
#print axioms LeanMachine.FractionalCover.unit_covers
#print axioms LeanMachine.FractionalCover.number_le_card

-- IntervalGapArea.lean
#print axioms LeanMachine.IntervalGapArea.containsGap
#print axioms LeanMachine.IntervalGapArea.exposed
#print axioms LeanMachine.IntervalGapArea.contained
#print axioms LeanMachine.IntervalGapArea.exposed_left_card_le_one
#print axioms LeanMachine.IntervalGapArea.exposed_card_le
#print axioms LeanMachine.IntervalGapArea.gapEdges_pairwiseDisjoint
#print axioms LeanMachine.IntervalGapArea.sum_contained_gap_le
#print axioms LeanMachine.IntervalGapArea.sum_contained_add_exposed
#print axioms LeanMachine.IntervalGapArea.exposed_mass_lower
#print axioms LeanMachine.IntervalGapArea.exposed_mass_sq_le_energy
#print axioms LeanMachine.IntervalGapArea.point_energy_lower
#print axioms LeanMachine.IntervalGapArea.point_area_lower
#print axioms LeanMachine.IntervalGapArea.point_area_lower_of_budgets

-- TimeComponents.lean
#print axioms LeanMachine.TimeComponents.label
#print axioms LeanMachine.TimeComponents.label_mono
#print axioms LeanMachine.TimeComponents.label_eq_of_Ico_subset
#print axioms LeanMachine.TimeComponents.Ico_subset_of_label_eq
#print axioms LeanMachine.TimeComponents.label_eq_iff_Ico_subset
#print axioms LeanMachine.TimeComponents.label_eq_of_between
#print axioms LeanMachine.TimeComponents.components
#print axioms LeanMachine.TimeComponents.label_mem_components
#print axioms LeanMachine.TimeComponents.ofTime
#print axioms LeanMachine.TimeComponents.times
#print axioms LeanMachine.TimeComponents.mem_times
#print axioms LeanMachine.TimeComponents.times_nonempty
#print axioms LeanMachine.TimeComponents.first
#print axioms LeanMachine.TimeComponents.last
#print axioms LeanMachine.TimeComponents.first_mem
#print axioms LeanMachine.TimeComponents.last_mem
#print axioms LeanMachine.TimeComponents.first_le_last
#print axioms LeanMachine.TimeComponents.last_le
#print axioms LeanMachine.TimeComponents.times_eq_Icc
#print axioms LeanMachine.TimeComponents.edges
#print axioms LeanMachine.TimeComponents.edges_subset
#print axioms LeanMachine.TimeComponents.edges_subset_range
#print axioms LeanMachine.TimeComponents.edges_pairwiseDisjoint
#print axioms LeanMachine.TimeComponents.biUnion_edges
#print axioms LeanMachine.TimeComponents.sum_edge_cost_le
#print axioms LeanMachine.TimeComponents.times_eq_intervalTimes
#print axioms LeanMachine.TimeComponents.rawLower
#print axioms LeanMachine.TimeComponents.rawUpper
#print axioms LeanMachine.TimeComponents.rawWidth
#print axioms LeanMachine.TimeComponents.rawInterval
#print axioms LeanMachine.TimeComponents.rawLower_le_rawUpper
#print axioms LeanMachine.TimeComponents.rawLower_attained
#print axioms LeanMachine.TimeComponents.rawUpper_attained
#print axioms LeanMachine.TimeComponents.mem_rawInterval_of_mem_times
#print axioms LeanMachine.TimeComponents.mem_rawInterval_ofTime
#print axioms LeanMachine.TimeComponents.rawInterval_card
#print axioms LeanMachine.TimeComponents.rawUpper_lt
#print axioms LeanMachine.TimeComponents.rawInterval_subset_range
#print axioms LeanMachine.TimeComponents.sum_rawWidth_le

-- OrbitLabelBudget.lean
#print axioms LeanMachine.OrbitLabelBudget.StepBudget
#print axioms LeanMachine.OrbitLabelBudget.image_cloud_card_le_chain
#print axioms LeanMachine.OrbitLabelBudget.image_cloud_card_le
#print axioms LeanMachine.OrbitLabelBudget.mem_cloud_le

-- FractionalIntervalGap.lean
#print axioms LeanMachine.FractionalIntervalGap.componentWeight
#print axioms LeanMachine.FractionalIntervalGap.componentWeight_nonneg
#print axioms LeanMachine.FractionalIntervalGap.componentWeight_cost
#print axioms LeanMachine.FractionalIntervalGap.componentWeight_covers
#print axioms LeanMachine.FractionalIntervalGap.exists_subcover
#print axioms LeanMachine.FractionalIntervalGap.point_area_lower_of_incidence_budget
#print axioms LeanMachine.FractionalIntervalGap.incidence_le_uniform_cost
#print axioms LeanMachine.FractionalIntervalGap.point_area_lower_of_uniform_bound
#print axioms LeanMachine.FractionalIntervalGap.point_area_lower_of_finite_number

-- PartitionEnergy.lean
#print axioms LeanMachine.PartitionEnergy.energy
#print axioms LeanMachine.PartitionEnergy.energy_eq_sum_fibers
#print axioms LeanMachine.PartitionEnergy.energy_nonneg
#print axioms LeanMachine.PartitionEnergy.energy_mono
#print axioms LeanMachine.PartitionEnergy.energy_mono_finset
#print axioms LeanMachine.PartitionEnergy.energy_loss_le_retained
#print axioms LeanMachine.PartitionEnergy.energy_loss_le
#print axioms LeanMachine.PartitionEnergy.energy_loss_le_paid_mass

-- WeightedCircularGap.lean
#print axioms LeanMachine.WeightedCircularGap.edges
#print axioms LeanMachine.WeightedCircularGap.weightedGap
#print axioms LeanMachine.WeightedCircularGap.circumference
#print axioms LeanMachine.WeightedCircularGap.energy
#print axioms LeanMachine.WeightedCircularGap.area
#print axioms LeanMachine.WeightedCircularGap.cycle_pos
#print axioms LeanMachine.WeightedCircularGap.edges_subset
#print axioms LeanMachine.WeightedCircularGap.edges_card
#print axioms LeanMachine.WeightedCircularGap.edges_lift
#print axioms LeanMachine.WeightedCircularGap.edges_pairwiseDisjoint
#print axioms LeanMachine.WeightedCircularGap.biUnion_edges
#print axioms LeanMachine.WeightedCircularGap.edgeLabel
#print axioms LeanMachine.WeightedCircularGap.edgeLabel_spec
#print axioms LeanMachine.WeightedCircularGap.edgeLabel_lt
#print axioms LeanMachine.WeightedCircularGap.edgeLabel_eq_of_mem
#print axioms LeanMachine.WeightedCircularGap.mem_edges_iff_label
#print axioms LeanMachine.WeightedCircularGap.edges_eq_filter
#print axioms LeanMachine.WeightedCircularGap.label_image
#print axioms LeanMachine.WeightedCircularGap.next_anchor_mem
#print axioms LeanMachine.WeightedCircularGap.forward_mod_add
#print axioms LeanMachine.WeightedCircularGap.edgeLabel_eq_of_no_target_between
#print axioms LeanMachine.WeightedCircularGap.sum_weightedGap
#print axioms LeanMachine.WeightedCircularGap.energy_eq_partitionEnergy
#print axioms LeanMachine.WeightedCircularGap.energy_eq_pairSum
#print axioms LeanMachine.WeightedCircularGap.weightedGap_nonneg
#print axioms LeanMachine.WeightedCircularGap.circumference_nonneg
#print axioms LeanMachine.WeightedCircularGap.energy_nonneg
#print axioms LeanMachine.WeightedCircularGap.area_nonneg
#print axioms LeanMachine.WeightedCircularGap.energy_le_circumference_sq
#print axioms LeanMachine.WeightedCircularGap.area_le_half
#print axioms LeanMachine.WeightedCircularGap.weightedGap_one
#print axioms LeanMachine.WeightedCircularGap.area_one

-- AnchoredCircularCover.lean
#print axioms LeanMachine.AnchoredCircularCover.coveredEdges
#print axioms LeanMachine.AnchoredCircularCover.coveredVertices
#print axioms LeanMachine.AnchoredCircularCover.coveredEdges_subset
#print axioms LeanMachine.AnchoredCircularCover.mem_arc_iff_forward_lt
#print axioms LeanMachine.AnchoredCircularCover.mem_closedArc_iff_forward_le
#print axioms LeanMachine.AnchoredCircularCover.arc_crosses_boundary
#print axioms LeanMachine.AnchoredCircularCover.forward_relative
#print axioms LeanMachine.AnchoredCircularCover.forward_between_iff
#print axioms LeanMachine.AnchoredCircularCover.no_target_between
#print axioms LeanMachine.AnchoredCircularCover.uncovered_pair_labels

-- CircularSubdivision.lean
#print axioms LeanMachine.CircularSubdivision.lift
#print axioms LeanMachine.CircularSubdivision.lift_eq
#print axioms LeanMachine.CircularSubdivision.lift_period
#print axioms LeanMachine.CircularSubdivision.lift_eq_of_le
#print axioms LeanMachine.CircularSubdivision.edgeLength
#print axioms LeanMachine.CircularSubdivision.edgeLength_lift_nonneg
#print axioms LeanMachine.CircularSubdivision.edgeLength_periodic
#print axioms LeanMachine.CircularSubdivision.sum_arc
#print axioms LeanMachine.CircularSubdivision.arc_length
#print axioms LeanMachine.CircularSubdivision.total_length
#print axioms LeanMachine.CircularSubdivision.weightedGap_eq_displacement
#print axioms LeanMachine.CircularSubdivision.area_eq_displacements

-- AnchoredGapErosion.lean
#print axioms LeanMachine.AnchoredGapErosion.penalty
#print axioms LeanMachine.AnchoredGapErosion.penalty_mono
#print axioms LeanMachine.AnchoredGapErosion.penalty_le_self
#print axioms LeanMachine.AnchoredGapErosion.penalty_nonneg
#print axioms LeanMachine.AnchoredGapErosion.penalty_le_half
#print axioms LeanMachine.AnchoredGapErosion.coveredLength
#print axioms LeanMachine.AnchoredGapErosion.coveredLength_nonneg
#print axioms LeanMachine.AnchoredGapErosion.coveredLength_le
#print axioms LeanMachine.AnchoredGapErosion.normalized_loss
#print axioms LeanMachine.AnchoredGapErosion.energy_loss_le
#print axioms LeanMachine.AnchoredGapErosion.area_lower_bound
#print axioms LeanMachine.AnchoredGapErosion.area_lower_bound_linear

-- CircularRefinement.lean
#print axioms LeanMachine.CircularRefinement.image_subset_range
#print axioms LeanMachine.CircularRefinement.point_image
#print axioms LeanMachine.CircularRefinement.min_image
#print axioms LeanMachine.CircularRefinement.coordinate_point_image
#print axioms LeanMachine.CircularRefinement.area_image_eq_pointArea

-- IndexedSourceBank.lean
#print axioms LeanMachine.SourceBank.indexed
#print axioms LeanMachine.SourceBank.indexed_values
#print axioms LeanMachine.SourceBank.indexed_cost
#print axioms LeanMachine.SourceBank.indexed_nonempty

-- PaidAveraging.lean
#print axioms LeanMachine.PaidAveraging.mean_signed_eq
#print axioms LeanMachine.PaidAveraging.mean_signed_le
#print axioms LeanMachine.PaidAveraging.mean_credit_sub_cost_le

-- ProfileCompactness.lean
#print axioms LeanMachine.ProfileCompactness.exists_bounded_subsequence
#print axioms LeanMachine.ProfileCompactness.limit_mass_of_finite_sums
#print axioms LeanMachine.ProfileCompactness.exists_profile_subsequence
#print axioms LeanMachine.ProfileCompactness.exists_joint_subsequence
#print axioms LeanMachine.ProfileCompactness.finite_tail_tendsto

-- PrefixError.lean
#print axioms LeanMachine.PrefixError.finite_error_le
#print axioms LeanMachine.PrefixError.ceil_scaled_tendsto
#print axioms LeanMachine.PrefixError.max_ceil_scaled_tendsto

-- TailMoments.lean
#print axioms LeanMachine.TailMoments.rank_mul_tendsto_zero
#print axioms LeanMachine.TailMoments.scaled_tail_tendsto_zero
#print axioms LeanMachine.TailMoments.polynomial_tail_tendsto_zero
#print axioms LeanMachine.TailMoments.not_summable_moment_of_tail_floor

-- UniformGap.lean
#print axioms LeanMachine.UniformGap.exists_gap

-- TailLiminf.lean
#print axioms LeanMachine.TailLiminf.liminf_ofReal_eq_zero_iff
#print axioms LeanMachine.TailLiminf.liminf_ofReal_eq_zero_of_tendsto
#print axioms LeanMachine.TailLiminf.liminf_ofReal_const_mul_eq_zero

-- PowerEnvelope.lean
#print axioms LeanMachine.PowerEnvelope.summable_moment
#print axioms LeanMachine.PowerEnvelope.summable
#print axioms LeanMachine.PowerEnvelope.polynomial_tail_tendsto_zero
#print axioms LeanMachine.PowerEnvelope.exists_balanced_exponent
#print axioms LeanMachine.PowerEnvelope.balanced_scale_limits

-- BoundedLimsup.lean
#print axioms LeanMachine.BoundedLimsup.le_limsup
#print axioms LeanMachine.BoundedLimsup.limsup_nonneg
#print axioms LeanMachine.BoundedLimsup.limsup_le_one
#print axioms LeanMachine.BoundedLimsup.mul_limsup_le_of_tendsto
#print axioms LeanMachine.BoundedLimsup.limsup_le_mul_limsup

-- InverseSquareTail.lean
#print axioms LeanMachine.InverseSquareTail.summable
#print axioms LeanMachine.InverseSquareTail.tsum_tail_le
#print axioms LeanMachine.InverseSquareTail.summable_of_le
#print axioms LeanMachine.InverseSquareTail.tail_le

-- PowerTail.lean
#print axioms LeanMachine.PowerTail.tsum_tail_le
#print axioms LeanMachine.PowerTail.summable_of_le
#print axioms LeanMachine.PowerTail.tail_le
#print axioms LeanMachine.PowerTail.scaled_tail_tendsto_zero

-- CausalClosure.lean
#print axioms LeanMachine.CausalClosure
#print axioms LeanMachine.CausalClosure.hull
#print axioms LeanMachine.CausalClosure.maximal
#print axioms LeanMachine.CausalClosure.maximal_subset
#print axioms LeanMachine.CausalClosure.exists_maximal
#print axioms LeanMachine.CausalClosure.hull_maximal
#print axioms LeanMachine.CausalClosure.root_mem_maximal
#print axioms LeanMachine.CausalClosure.closed_union_hull_maximal_diff

-- ContinuationSuppliers.lean
#print axioms LeanMachine.CausalClosure.landings
#print axioms LeanMachine.CausalClosure.extend
#print axioms LeanMachine.CausalClosure.suppliers
#print axioms LeanMachine.CausalClosure.extend_eq_hull_suppliers
#print axioms LeanMachine.CausalClosure.supplier_past
#print axioms LeanMachine.CausalClosure.root_mem_suppliers
#print axioms LeanMachine.CausalClosure.hull_extension_core_cover
#print axioms LeanMachine.CausalClosure.hull_extension_core_cover_uniform
#print axioms LeanMachine.CausalClosure.two_extension_eq
#print axioms LeanMachine.CausalClosure.landing_diff_eq
#print axioms LeanMachine.CausalClosure.two_extension_maximal_landings

-- IntervalClusterErosion.lean
#print axioms LeanMachine.IntervalClusterErosion.mem_closed_arc_of_between
#print axioms LeanMachine.IntervalClusterErosion.area_lower_bound

-- FiniteHullVariation.lean
#print axioms LeanMachine.FiniteHullVariation.endpoints
#print axioms LeanMachine.FiniteHullVariation.endpoints_empty
#print axioms LeanMachine.FiniteHullVariation.endpoints_singleton
#print axioms LeanMachine.FiniteHullVariation.endpoints_bounds
#print axioms LeanMachine.FiniteHullVariation.mem_endpoints
#print axioms LeanMachine.FiniteHullVariation.movement
#print axioms LeanMachine.FiniteHullVariation.movement_nonneg
#print axioms LeanMachine.FiniteHullVariation.movement_empty
#print axioms LeanMachine.FiniteHullVariation.movement_singleton
#print axioms LeanMachine.FiniteHullVariation.movement_le_cost

-- BoundedLiminf.lean
#print axioms LeanMachine.BoundedLiminf.bounds
#print axioms LeanMachine.BoundedLiminf.le_of_tendsto
#print axioms LeanMachine.BoundedLiminf.mono

-- ShiftedGridUnion.lean
#print axioms LeanMachine.ShiftedGrid.blockUnion
#print axioms LeanMachine.ShiftedGrid.mem_blockUnion
#print axioms LeanMachine.ShiftedGrid.blockUnion_empty
#print axioms LeanMachine.ShiftedGrid.blockUnion_card_le

-- VanishingTradeoff.lean
#print axioms LeanMachine.VanishingTradeoff.sq_le
#print axioms LeanMachine.VanishingTradeoff.limit_le_zero

-- ExtendedTradeoff.lean
#print axioms LeanMachine.ExtendedTradeoff.ofReal_le_liminf
#print axioms LeanMachine.ExtendedTradeoff.finite_sq_le
#print axioms LeanMachine.ExtendedTradeoff.eq_top_of_zero_cost
#print axioms LeanMachine.ExtendedTradeoff.density_lower
#print axioms LeanMachine.ExtendedTradeoff.density_liminf
#print axioms LeanMachine.ExtendedTradeoff.normalize_rate
#print axioms LeanMachine.ExtendedTradeoff.eq_top_of_div_le

-- RawIntervalCover.lean
#print axioms LeanMachine.ShiftedGrid.blockUnion_card_le_of_span
#print axioms LeanMachine.RawIntervalCover.Covers
#print axioms LeanMachine.RawIntervalCover.Covers.mono_radius
#print axioms LeanMachine.RawIntervalCover.exists_cover
#print axioms LeanMachine.RawIntervalCover.number
#print axioms LeanMachine.RawIntervalCover.number_le
#print axioms LeanMachine.RawIntervalCover.exists_min_cover
#print axioms LeanMachine.RawIntervalCover.number_empty
#print axioms LeanMachine.RawIntervalCover.blockUnion_card_le_of_cover
#print axioms LeanMachine.RawIntervalCover.blockUnion_card_le
#print axioms LeanMachine.RawIntervalCover.two_block_factor_sharp

-- ScheduledExcursion.lean
#print axioms LeanMachine.ScheduledExcursion.Schedule
#print axioms LeanMachine.ScheduledExcursion.Schedule.active
#print axioms LeanMachine.ScheduledExcursion.Schedule.height
#print axioms LeanMachine.ScheduledExcursion.Schedule.mem_active
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_le
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_zero
#print axioms LeanMachine.ScheduledExcursion.Schedule.active_downward
#print axioms LeanMachine.ScheduledExcursion.Schedule.lt_height_iff
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_depart
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_arrive
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_step
#print axioms LeanMachine.ScheduledExcursion.Schedule.min_height_le
#print axioms LeanMachine.ScheduledExcursion.Schedule.return_iff
#print axioms LeanMachine.ScheduledExcursion.Schedule.peak
#print axioms LeanMachine.ScheduledExcursion.Schedule.depart_lt_peak
#print axioms LeanMachine.ScheduledExcursion.Schedule.peak_lt_arrive
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_peak
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_lt_peak
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_mono_before
#print axioms LeanMachine.ScheduledExcursion.Schedule.height_anti_after
#print axioms LeanMachine.ScheduledExcursion.Schedule.plateau
#print axioms LeanMachine.ScheduledExcursion.Schedule.plateau_peak

-- CyclicGapUpper.lean
#print axioms LeanMachine.CyclicSelection.gap_le_of_next
#print axioms LeanMachine.CyclicSelection.pointArea_le_of_gap_le
#print axioms LeanMachine.floor_step_le_ceilDiv
#print axioms LeanMachine.ceilDiv_cast_le_div_add_one

-- QueryMovement.lean
#print axioms LeanMachine.QueryMovement.covered
#print axioms LeanMachine.QueryMovement.mem_covered
#print axioms LeanMachine.QueryMovement.abs_sub_lt_of_floor_eq
#print axioms LeanMachine.QueryMovement.card_types_le
#print axioms LeanMachine.QueryMovement.elapsed
#print axioms LeanMachine.QueryMovement.elapsed_nonneg
#print axioms LeanMachine.QueryMovement.elapsed_mono
#print axioms LeanMachine.QueryMovement.dist_le_elapsed_sub
#print axioms LeanMachine.QueryMovement.dist_le_elapsed_abs
#print axioms LeanMachine.QueryMovement.card_types_le_charge
#print axioms LeanMachine.QueryMovement.variation
#print axioms LeanMachine.QueryMovement.maxStep
#print axioms LeanMachine.QueryMovement.step_le_maxStep
#print axioms LeanMachine.QueryMovement.maxStep_nonneg
#print axioms LeanMachine.QueryMovement.elapsed_maxStep_le_variation
#print axioms LeanMachine.QueryMovement.real_bounds

-- CircleGridCapacity.lean
#print axioms LeanMachine.CircleGridCapacity.card_le_floor_diameter
#print axioms LeanMachine.CircleGridCapacity.centre
#print axioms LeanMachine.CircleGridCapacity.card_ball_le
#print axioms LeanMachine.CircleGridCapacity.dist_coe_le
#print axioms LeanMachine.CircleGridCapacity.card_covered_le

-- IntervalQueries.lean
#print axioms LeanMachine.QueryMovement.card_image_le_retained
#print axioms LeanMachine.QueryMovement.edges_disjoint_of_intervals
#print axioms LeanMachine.QueryMovement.sum_interval_charge_le
#print axioms LeanMachine.QueryMovement.frozen_interval_cover
#print axioms LeanMachine.QueryMovement.card_interval_types_le
#print axioms LeanMachine.QueryMovement.interval_real_bounds

-- DisjointSums.lean
#print axioms LeanMachine.card_fiber_mul_card
#print axioms LeanMachine.DisjointSums
#print axioms LeanMachine.DisjointSums.representative
#print axioms LeanMachine.DisjointSums.representative_mem
#print axioms LeanMachine.DisjointSums.representative_mem_iff
#print axioms LeanMachine.DisjointSums.representative_injective
#print axioms LeanMachine.DisjointSums.card_le
#print axioms LeanMachine.DisjointSums.encode
#print axioms LeanMachine.DisjointSums.encode_apply
#print axioms LeanMachine.DisjointSums.encode_surjective
#print axioms LeanMachine.DisjointSums.fiber_card
#print axioms LeanMachine.DisjointSums.recover
#print axioms LeanMachine.DisjointSums.encode_update
#print axioms LeanMachine.coordinateFiberEquiv
#print axioms LeanMachine.card_coordinate_fiber
#print axioms LeanMachine.card_independent_coordinate

-- SubsetPlacement.lean
#print axioms LeanMachine.SubsetPlacement.Subset
#print axioms LeanMachine.SubsetPlacement.Entry
#print axioms LeanMachine.SubsetPlacement.Packet
#print axioms LeanMachine.SubsetPlacement.support
#print axioms LeanMachine.SubsetPlacement.mem_support
#print axioms LeanMachine.SubsetPlacement.owner
#print axioms LeanMachine.SubsetPlacement.mem_owner
#print axioms LeanMachine.SubsetPlacement.support_nonempty
#print axioms LeanMachine.SubsetPlacement.support_disjoint
#print axioms LeanMachine.SubsetPlacement.code
#print axioms LeanMachine.SubsetPlacement.queried_absent
#print axioms LeanMachine.SubsetPlacement.eq_of_same_bin
#print axioms LeanMachine.SubsetPlacement.summand
#print axioms LeanMachine.SubsetPlacement.summand_mem
#print axioms LeanMachine.SubsetPlacement.summand_injective
#print axioms LeanMachine.SubsetPlacement.support_eq_image
#print axioms LeanMachine.SubsetPlacement.encode_eq
#print axioms LeanMachine.SubsetPlacement.other_bin_queried
#print axioms LeanMachine.SubsetPlacement.entry_recovery
#print axioms LeanMachine.SubsetPlacement.card_entry
#print axioms LeanMachine.SubsetPlacement.card_packet

-- CyclicGapTails.lean
#print axioms LeanMachine.CyclicSelection.self_not_mem_forward_arc
#print axioms LeanMachine.CyclicSelection.next_anchor
#print axioms LeanMachine.CyclicSelection.gap_tail_iff
#print axioms LeanMachine.CyclicSelection.sum_odd
#print axioms LeanMachine.CyclicSelection.sum_points
#print axioms LeanMachine.CyclicSelection.sum_gap_sq_eq_tails
#print axioms LeanMachine.CyclicSelection.squareGapSum
#print axioms LeanMachine.CyclicSelection.squareGapSum_eq_tails
#print axioms LeanMachine.CyclicSelection.pointGapArea
#print axioms LeanMachine.CyclicSelection.pointGapArea_eq

-- SubsetGapCounting.lean
#print axioms LeanMachine.CyclicSelection.card_subsets_containing_avoiding
#print axioms LeanMachine.CyclicSelection.card_gap_tails
#print axioms LeanMachine.CyclicSelection.sum_range_choose_fixed
#print axioms LeanMachine.CyclicSelection.sum_odd_choose
#print axioms LeanMachine.CyclicSelection.sum_squareGapSum
#print axioms LeanMachine.CyclicSelection.mean_pointGapArea

-- CyclicGapScaling.lean
#print axioms LeanMachine.CyclicSelection.scaleEmbedding
#print axioms LeanMachine.CyclicSelection.point_scaled
#print axioms LeanMachine.CyclicSelection.gap_scaled
#print axioms LeanMachine.CyclicSelection.pointGapArea_scaled

-- Independent interval widths and fixed-subset limits.
#print axioms LeanMachine.QueryMovement.interval_real_bounds_general
#print axioms LeanMachine.FixedSubsetLimits.atTop_of_ratio
#print axioms LeanMachine.FixedSubsetLimits.choose_ratio
#print axioms LeanMachine.FixedSubsetLimits.floor_successor_ratio
#print axioms LeanMachine.FixedSubsetLimits.capped_capacity_ratio
#print axioms LeanMachine.FixedSubsetLimits.inverse_power_diverges

-- CausalFields.lean
#print axioms LeanMachine.CausalFields.Layout
#print axioms LeanMachine.CausalFields.Observation
#print axioms LeanMachine.CausalFields.observe
#print axioms LeanMachine.CausalFields.observe_eq_iff
#print axioms LeanMachine.CausalFields.Evaluation
#print axioms LeanMachine.CausalFields.Evaluation.ofRules
#print axioms LeanMachine.CausalFields.Evaluation.edge_eq
#print axioms LeanMachine.CausalFields.Evaluation.output_eq
#print axioms LeanMachine.CausalFields.Evaluation.exists_edge_rule
#print axioms LeanMachine.CausalFields.Evaluation.exists_output_rule
#print axioms LeanMachine.CausalFields.Evaluation.value_eq_of_cut
#print axioms LeanMachine.CausalFields.Evaluation.output_eq_of_cut
#print axioms LeanMachine.CausalFields.Evaluation.value_factorsThrough_raw
#print axioms LeanMachine.CausalFields.Evaluation.cutObservation
#print axioms LeanMachine.CausalFields.Evaluation.raw_factorsThrough_cut
#print axioms LeanMachine.CausalFields.Evaluation.comap
#print axioms LeanMachine.CausalFields.Evaluation.projected
#print axioms LeanMachine.CausalFields.Evaluation.projected_agrees

-- CausalCutCapacity.lean
#print axioms LeanMachine.CausalFields.card_range_le_of_factorsThrough
#print axioms LeanMachine.CausalFields.Evaluation.card_raw_range_le
#print axioms LeanMachine.CausalFields.Evaluation.log_support_le_cut
