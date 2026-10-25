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
