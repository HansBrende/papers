import LeanMachine.IntervalCover

/-! Lemma 3.2 of *Source Covers and Barriers to Tape Transposition*.
Re-export the shared interval-cover theorems without duplicating their proofs. -/

namespace SourceCovers

export LeanMachine.IntervalCover (exists_cover_packing exists_subcover_le_weight)

end SourceCovers
