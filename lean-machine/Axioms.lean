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
