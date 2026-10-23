import BitWord.GeometryPartition
import BitWord.GeometryOperationInverse

namespace BitWord.Geometry

/-- Operation/interval data alone: no endpoint, inverse, fanout, or bad-volume
certificate is supplied. `toStage` constructs all of those endpoint laws. -/
structure PartitionData (P : ℕ) where
  count : ℕ
  intervals : IntervalFamily (Fin count)
  operation : Fin count → BlockOperation
  length_eq : ∀ i, intervals.length i = (operation i).length
  admissible : ∀ i, (operation i).Admissible
  bounded : ∀ i, intervals.start i + intervals.length i ≤ P

namespace PartitionData
variable {P : ℕ} (D : PartitionData P)

 noncomputable def raw (back : Bool) (x : ℕ) : ℕ :=
   if h : ∃ i, D.intervals.contains i x then
     D.intervals.start h.choose + (D.operation h.choose).act back (x - D.intervals.start h.choose)
   else x

 theorem raw_inside (back : Bool) {i : Fin D.count} {x : ℕ}
     (hx : D.intervals.contains i x) :
     D.raw back x = D.intervals.start i + (D.operation i).act back (x - D.intervals.start i) := by
   classical
   have he : ∃ i, D.intervals.contains i x := ⟨i, hx⟩
   have hu : he.choose = i := D.intervals.contains_unique he.choose_spec hx
   simp only [raw, dite_eq_left he]
   rw [hu]

 theorem raw_outside (back : Bool) {x : ℕ} (hx : ∀ i, ¬ D.intervals.contains i x) :
     D.raw back x = x := by
   classical
   have he : ¬ ∃ i, D.intervals.contains i x := by simpa using hx
   simp [raw, he]

 theorem raw_stays (back : Bool) {i : Fin D.count} {x : ℕ}
     (hx : D.intervals.contains i x) : D.intervals.contains i (D.raw back x) := by
   have hs := Nat.sub_add_cancel hx.1
   have hlocal : x - D.intervals.start i < (D.operation i).length := by
     rw [← D.length_eq]
     have := hx.2
     omega
   have ho := (D.operation i).act_lt back hlocal
   rw [D.raw_inside back hx]
   constructor
   · omega
   · rw [D.length_eq]
     omega

 theorem raw_inverse (back : Bool) (x : ℕ) : D.raw (!back) (D.raw back x) = x := by
   classical
   by_cases he : ∃ i, D.intervals.contains i x
   · obtain ⟨i, hi⟩ := he
     rw [D.raw_inside (!back) (D.raw_stays back hi), D.raw_inside back hi]
     rw [Nat.add_sub_cancel_left]
     have hlocal : x - D.intervals.start i < (D.operation i).length := by
       have hs := Nat.sub_add_cancel hi.1
       rw [← D.length_eq]
       have := hi.2
       omega
     rw [(D.operation i).act_inverse back hlocal]
     exact Nat.add_sub_of_le hi.1
   · have hn : ∀ i, ¬ D.intervals.contains i x := by simpa using he
     rw [D.raw_outside back hn, D.raw_outside (!back) hn]

 theorem raw_lt (back : Bool) {x : ℕ} (hx : x < P) : D.raw back x < P := by
   classical
   by_cases he : ∃ i, D.intervals.contains i x
   · obtain ⟨i, hi⟩ := he
     exact lt_of_lt_of_le (D.raw_stays back hi).2 (D.bounded i)
   · rw [D.raw_outside back (by simpa using he)]
     exact hx

 noncomputable def endpoint : Equiv.Perm (Fin P) where
   toFun x := ⟨D.raw false x.val, D.raw_lt false x.isLt⟩
   invFun x := ⟨D.raw true x.val, D.raw_lt true x.isLt⟩
   left_inv x := Fin.ext (D.raw_inverse false x.val)
   right_inv x := Fin.ext (D.raw_inverse true x.val)

 theorem finiteAct_endpoint (back : Bool) {x : ℕ} (hx : x < P) :
     finiteAct (oriented D.endpoint back) x = D.raw back x := by
   cases back <;> simp [finiteAct, oriented, endpoint, hx]

 /-- Every permitted disjoint layout has its actual permutation endpoint. -/
 noncomputable def toStage : PartitionStage P where
   count := D.count
   intervals := D.intervals
   operation := D.operation
   length_eq := D.length_eq
   admissible := D.admissible
   bounded := D.bounded
   endpoint := D.endpoint
   action back i x hx := by
     rw [D.finiteAct_endpoint back (lt_of_lt_of_le hx.2 (D.bounded i))]
     exact D.raw_inside back hx
   outside back x hx := by
     by_cases hxp : x < P
     · rw [D.finiteAct_endpoint back hxp]
       exact D.raw_outside back hx
     · simp [finiteAct, hxp]

end PartitionData
end BitWord.Geometry
