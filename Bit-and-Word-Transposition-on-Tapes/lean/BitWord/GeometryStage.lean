import BitWord.GeometryPartition
import BitWord.GeometryParity

namespace BitWord.Geometry

/-- Public endpoint grammar: heterogeneous disjoint whole-entry operations
(including disjoint rotations/reversals), or full-bank stable split/interleave. -/
inductive Stage (P : ℕ) where
  | partition (data : PartitionStage P)
  | parity (even : P % 2 = 0) (back : Bool)

namespace Stage
variable {P : ℕ}

def endpoint : Stage P → Equiv.Perm (Fin P)
  | .partition T => T.endpoint
  | .parity he back => oriented (splitEquiv P he) back

def act (T : Stage P) (back : Bool) : ℕ → ℕ := finiteAct (oriented T.endpoint back)
def bad (T : Stage P) (B : ℕ) : Finset ℕ :=
  match T with
  | .partition S => S.bad B
  | .parity _ _ => ∅

 theorem good_image_bins_le (T : Stage P) (back : Bool) {B j : ℕ}
     (hB : 0 < B) (S : Finset ℕ)
     (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
     (hP : ∀ x ∈ S, x < P) (hgood : ∀ x ∈ S, x ∉ T.bad B) :
     (bins B (S.image (T.act back))).card ≤ 11 := by
   cases T with
   | partition T => exact T.good_image_bins_le back hB S hS hgood
   | parity he dir =>
     cases dir <;> cases back
     · have hh : S.image ((Stage.parity he false).act false) = S.image (split P) := by
         apply Finset.image_congr
         intro x hx
         exact finiteAct_splitEquiv he (hP x hx)
       rw [hh]
       exact split_image_bins_le hB S hS
     · have hh : S.image ((Stage.parity he false).act true) = S.image (interleave P) := by
         apply Finset.image_congr
         intro x hx
         exact finiteAct_splitEquiv_symm he (hP x hx)
       rw [hh]
       exact interleave_image_bins_le hB S hS
     · have hh : S.image ((Stage.parity he true).act false) = S.image (interleave P) := by
         apply Finset.image_congr
         intro x hx
         exact finiteAct_splitEquiv_symm he (hP x hx)
       rw [hh]
       exact interleave_image_bins_le hB S hS
     · have hh : S.image ((Stage.parity he true).act true) = S.image (split P) := by
         apply Finset.image_congr
         intro x hx
         exact finiteAct_splitEquiv he (hP x hx)
       rw [hh]
       exact split_image_bins_le hB S hS

 theorem bad_invariant (T : Stage P) (back : Bool) {B x : ℕ} :
     T.act back x ∈ T.bad B ↔ x ∈ T.bad B := by
   cases T with
   | partition T => exact T.bad_invariant back
   | parity he dir => simp [bad]

 /-- Public predecessor bins; clipped to actual raw bank positions. -/
 def predecessors (T : Stage P) (B j : ℕ) : Finset ℕ :=
   bins B (((Finset.range P).filter
     (fun x => x / B = j ∧ x ∉ T.bad B)).image (T.act true))

 theorem predecessors_card_le (T : Stage P) {B : ℕ} (hB : 0 < B) (j : ℕ) :
     (T.predecessors B j).card ≤ 11 := by
   apply T.good_image_bins_le (j := j) true hB
   · intro x hx
     have he := (Finset.mem_filter.mp hx).2.1
     rw [← he]
     exact ⟨Nat.div_mul_le_self x B,
       (Nat.div_lt_iff_lt_mul hB).1 (Nat.lt_succ_self _)⟩
   · intro x hx
     exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
   · intro x hx
     exact (Finset.mem_filter.mp hx).2.2

 theorem predecessor_mem (T : Stage P) {B x : ℕ} (hxP : x < P)
     (hx : T.act true x ∉ T.bad B) :
     T.act true x / B ∈ T.predecessors B (x / B) := by
   apply mem_bins.mpr
   refine ⟨T.act true x, Finset.mem_image.mpr ⟨x, ?_, rfl⟩, rfl⟩
   exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxP, rfl,
     fun hb => hx ((T.bad_invariant true).2 hb)⟩

 theorem bad_subset_range (T : Stage P) (B : ℕ) : T.bad B ⊆ Finset.range P := by
   cases T with
   | partition T => exact T.bad_subset_range B
   | parity he dir => simp [bad]

end Stage
end BitWord.Geometry
