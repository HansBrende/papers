import BitWord.GeometryBins

namespace BitWord.Geometry

/-- Public disjoint half-open intervals. The family may have arbitrary starts
and heterogeneous positive lengths. -/
structure IntervalFamily (ι : Type*) where
  start : ι → ℕ
  length : ι → ℕ
  positive : ∀ i, 0 < length i
  separated : ∀ i k, i ≠ k →
    start i + length i ≤ start k ∨ start k + length k ≤ start i

namespace IntervalFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : IntervalFamily ι)

 def contains (i : ι) (x : ℕ) : Prop := F.start i ≤ x ∧ x < F.start i + F.length i
 instance (i : ι) (x : ℕ) : Decidable (F.contains i x) := inferInstanceAs (Decidable (_ ∧ _))
 def points (i : ι) : Finset ℕ := Finset.Ico (F.start i) (F.start i + F.length i)
 omit [Fintype ι] [DecidableEq ι] in
 @[simp] theorem mem_points (i : ι) (x : ℕ) : x ∈ F.points i ↔ F.contains i x := by
   simp [points, contains]
 omit [Fintype ι] in
 theorem contains_unique {i k : ι} {x : ℕ} (hi : F.contains i x)
     (hk : F.contains k x) : i = k := by
   by_contra hn
   have hd := F.separated i k hn
   simp only [contains] at hi hk
   rcases hd with hd | hd <;> omega

 /-- Generic geometric assembly: small blocks stay in a three-bin neighborhood;
 only two larger disjoint blocks can meet the source bin, and each has at most
 four image bins. The hypotheses on each block are discharged by the concrete
 entry-permutation and rotation/reversal constructors. -/
 theorem good_image_bins_le (f : ℕ → ℕ) (bad : ι → Prop) [DecidablePred bad]
     {B j : ℕ} (hB : 0 < B) (S : Finset ℕ)
     (hS : ∀ x ∈ S, j * B ≤ x ∧ x < (j + 1) * B)
     (hgood : ∀ x ∈ S, ∀ i, F.contains i x → ¬ bad i)
     (hinside : ∀ i x, F.contains i x → F.contains i (f x))
     (houtside : ∀ x, (∀ i, ¬ F.contains i x) → f x = x)
     (hlarge : ∀ i, ¬ bad i → B < F.length i →
       (bins B ((S.filter (F.contains i)).image f)).card ≤ 4) :
     (bins B (S.image f)).card ≤ 11 := by
   classical
   let I := Finset.univ.filter (fun i => ¬ bad i ∧ B < F.length i ∧
     ∃ x ∈ S, F.contains i x)
   let N := (S.image f).filter (fun y => j * B < y + B ∧ y < (j + 2) * B)
   let T := I.biUnion (fun i => (S.filter (F.contains i)).image f)
   have hI : I.card ≤ 2 := by
     apply large_meeting_card_le_two I F.start F.length hB
     · intro i hi k hk hne
       exact F.separated i k hne
     · intro i hi
       exact Nat.le_of_lt (Finset.mem_filter.mp hi).2.2.1
     · intro i hi
       obtain ⟨x, hx, hi⟩ := (Finset.mem_filter.mp hi).2.2.2
       exact ⟨x, (hS x hx).1, (hS x hx).2, hi.1, hi.2⟩
   have hN : (bins B N).card ≤ 3 := by
     apply bins_card_le_three hB
     intro x hx
     exact (Finset.mem_filter.mp hx).2
   have hT : (bins B T).card ≤ 8 := by
     apply (bins_biUnion_card_le B 4 I _ ?_).trans
     · omega
     · intro i hi
       have h := (Finset.mem_filter.mp hi).2
       exact hlarge i h.1 h.2.1
   have hcover : S.image f ⊆ N ∪ T := by
     intro y hy
     obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
     by_cases hi : ∃ i, F.contains i x
     · obtain ⟨i, hi⟩ := hi
       by_cases hl : F.length i ≤ B
       · apply Finset.mem_union_left
         apply Finset.mem_filter.mpr
         refine ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
         have hfx := hinside i x hi
         have hxs := hS x hx
         simp only [contains] at hi hfx
         constructor <;> nlinarith
       · apply Finset.mem_union_right
         apply Finset.mem_biUnion.mpr
         refine ⟨i, ?_, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
         · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood x hx i hi,
             Nat.lt_of_not_ge hl, x, hx, hi⟩
         · exact Finset.mem_filter.mpr ⟨hx, hi⟩
     · have he : f x = x := houtside x (by simpa using hi)
       apply Finset.mem_union_left
       apply Finset.mem_filter.mpr
       refine ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
       rw [he]
       have hxs := hS x hx
       constructor <;> nlinarith
   have hc := Finset.card_le_card (bins_mono (B := B) hcover)
   rw [bins_union] at hc
   have hu := Finset.card_union_le (bins B N) (bins B T)
   omega

end IntervalFamily
end BitWord.Geometry
