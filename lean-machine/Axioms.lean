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
