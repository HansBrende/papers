import TransposeFollowup.GapBank
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Div

/-! Consecutive row buckets and the nonempty gaps between any chosen buckets.
Unused bucket labels are permitted; they do not create extra gap records. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

structure RowBuckets (d M : ℕ) where
  bucket : Fin d → Fin M
  monotone : Monotone bucket
  intermediate : ∀ i j : Fin d, ∀ a : Fin M,
    i ≤ j → bucket i ≤ a → a ≤ bucket j →
      ∃ k, i ≤ k ∧ k ≤ j ∧ bucket k = a

namespace RowBuckets

variable {d M : ℕ} (B : RowBuckets d M)

def rankBefore (_B : RowBuckets d M) (U : Finset (Fin M)) (a : Fin M) : ℕ :=
  (U.filter (fun u => u < a)).card

theorem rankBefore_le (U : Finset (Fin M)) (a : Fin M) :
    B.rankBefore U a ≤ U.card := Finset.card_filter_le _ _

theorem rankBefore_mono (U : Finset (Fin M)) {a b : Fin M} (hab : a ≤ b) :
    B.rankBefore U a ≤ B.rankBefore U b := by
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
    lt_of_lt_of_le (Finset.mem_filter.mp hu).2 hab⟩

theorem rankBefore_lt (U : Finset (Fin M)) {a b : Fin M}
    (ha : a ∈ U) (hab : a < b) : B.rankBefore U a < B.rankBefore U b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro u hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
      lt_trans (Finset.mem_filter.mp hu).2 hab⟩
  · intro h
    have hb : a ∈ U.filter (fun u => u < b) := Finset.mem_filter.mpr ⟨ha,hab⟩
    rw [← h] at hb
    exact (lt_irrefl a) (Finset.mem_filter.mp hb).2

def gapRows (U : Finset (Fin M)) (k : Fin (U.card + 1)) : Finset (Fin d) :=
  Finset.univ.filter (fun i => B.bucket i ∉ U ∧ B.rankBefore U (B.bucket i) = k.val)

@[simp] theorem mem_gapRows (U : Finset (Fin M)) (k : Fin (U.card + 1)) (i : Fin d) :
    i ∈ B.gapRows U k ↔ B.bucket i ∉ U ∧ B.rankBefore U (B.bucket i) = k.val := by
  simp [gapRows]

abbrev GapIndex (U : Finset (Fin M)) := {k : Fin (U.card + 1) // (B.gapRows U k).Nonempty}

def gap (U : Finset (Fin M)) (k : B.GapIndex U) : Finset (Fin d) := B.gapRows U k.val

theorem gap_count (U : Finset (Fin M)) : Fintype.card (B.GapIndex U) ≤ U.card + 1 := by
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)

theorem gap_interval (U : Finset (Fin M)) (k : B.GapIndex U) : IsRowInterval (B.gap U k) := by
  refine ⟨k.property, ?_⟩
  intro i hi j hj v hiv hvj
  have hi' := (B.mem_gapRows U k.val i).mp hi
  have hj' := (B.mem_gapRows U k.val j).mp hj
  have hil := B.monotone hiv
  have hlj := B.monotone hvj
  have h1 := B.rankBefore_mono U hil
  have h2 := B.rankBefore_mono U hlj
  apply (B.mem_gapRows U k.val v).mpr
  refine ⟨?_, by omega⟩
  intro hv
  have hne : B.bucket v ≠ B.bucket j := by
    intro heq
    exact hj'.1 (heq ▸ hv)
  have hstrict := B.rankBefore_lt U hv (lt_of_le_of_ne hlj hne)
  omega

theorem gap_avoids (U : Finset (Fin M)) (k : B.GapIndex U) {i : Fin d}
    (hi : i ∈ B.gap U k) : B.bucket i ∉ U :=
  ((B.mem_gapRows U k.val i).mp hi).1

theorem rankBefore_eq_of_interval_avoids (U : Finset (Fin M))
    (I : Finset (Fin d)) (hI : IsRowInterval I)
    (havoid : ∀ i ∈ I, B.bucket i ∉ U) {i j : Fin d} (hi : i ∈ I) (hj : j ∈ I) :
    B.rankBefore U (B.bucket i) = B.rankBefore U (B.bucket j) := by
  suffices h : ∀ i ∈ I, ∀ j ∈ I, i ≤ j →
      U.filter (fun u => u < B.bucket i) = U.filter (fun u => u < B.bucket j) by
    rcases le_total i j with hij | hji
    · exact congrArg Finset.card (h i hi j hj hij)
    · exact (congrArg Finset.card (h j hj i hi hji)).symm
  intro i hi j hj hij
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, hai⟩
    exact ⟨ha, lt_of_lt_of_le hai (B.monotone hij)⟩
  · rintro ⟨ha, haj⟩
    refine ⟨ha, ?_⟩
    by_contra hn
    obtain ⟨v, hiv, hvj, heq⟩ := B.intermediate i j a hij (le_of_not_gt hn) haj.le
    exact havoid v (hI.2 i hi j hj v hiv hvj) (heq ▸ ha)

theorem interval_in_gap (U : Finset (Fin M)) (I : Finset (Fin d))
    (hI : IsRowInterval I) (havoid : ∀ i ∈ I, B.bucket i ∉ U) :
    ∃ k : B.GapIndex U, I ⊆ B.gap U k := by
  obtain ⟨i, hi⟩ := hI.1
  let r : Fin (U.card + 1) := ⟨B.rankBefore U (B.bucket i), Nat.lt_succ_of_le (B.rankBefore_le U _)⟩
  have hir : i ∈ B.gapRows U r := (B.mem_gapRows U r i).mpr ⟨havoid i hi, rfl⟩
  refine ⟨⟨r, ⟨i,hir⟩⟩, ?_⟩
  intro j hj
  apply (B.mem_gapRows U r j).mpr
  exact ⟨havoid j hj, B.rankBefore_eq_of_interval_avoids U I hI havoid hj hi⟩

/-- Equal-length consecutive buckets; the final bucket may be short and trailing
labels may be unused. These harmless empty labels preserve the requested cap. -/
def quotient (d M L : ℕ) (hL : 0 < L) (hcover : d ≤ M * L) : RowBuckets d M where
  bucket i := ⟨i.val / L, (Nat.div_lt_iff_lt_mul hL).mpr (i.isLt.trans_le hcover)⟩
  monotone := by
    intro i j hij
    exact Nat.div_le_div_right hij
  intermediate := by
    intro i j a hij hia haj
    change i.val / L ≤ a.val at hia
    change a.val ≤ j.val / L at haj
    by_cases heq : i.val / L = a.val
    · exact ⟨i, le_rfl, hij, Fin.ext heq⟩
    · have hlt : i.val / L < a.val := lt_of_le_of_ne hia heq
      have hil : i.val < a.val * L := (Nat.div_lt_iff_lt_mul hL).mp hlt
      have hlj : a.val * L ≤ j.val := (Nat.le_div_iff_mul_le hL).mp haj
      let k : Fin d := ⟨a.val * L, hlj.trans_lt j.isLt⟩
      refine ⟨k, hil.le, hlj, ?_⟩
      exact Fin.ext (Nat.mul_div_cancel a.val hL)

@[simp] theorem quotient_bucket_val (d M L : ℕ) (hL : 0 < L) (hc : d ≤ M * L)
    (i : Fin d) : ((quotient d M L hL hc).bucket i).val = i.val / L := rfl

theorem quotient_fiber_card (d M L : ℕ) (hL : 0 < L) (hc : d ≤ M * L)
    (a : Fin M) :
    (Finset.univ.filter (fun i => (quotient d M L hL hc).bucket i = a)).card ≤ L := by
  let S := Finset.univ.filter (fun i => (quotient d M L hL hc).bucket i = a)
  let f : S → Fin L := fun i => ⟨i.val.val % L, Nat.mod_lt _ hL⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hi : i.val.val / L = a.val := congrArg Fin.val (Finset.mem_filter.mp i.property).2
    have hj : j.val.val / L = a.val := congrArg Fin.val (Finset.mem_filter.mp j.property).2
    have hm : i.val.val % L = j.val.val % L := congrArg Fin.val hij
    apply Subtype.ext
    apply Fin.ext
    have h1 := Nat.div_add_mod i.val.val L
    have h2 := Nat.div_add_mod j.val.val L
    rw [hi] at h1
    rw [hj, ← hm] at h2
    omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

def paddedFiber (sigma : ℕ) (a : Fin M) : Finset (Fin d) :=
  Finset.univ.filter (fun c => ∃ j ∈ columnWindow sigma c, B.bucket j = a)

@[simp] theorem mem_paddedFiber (sigma : ℕ) (a : Fin M) (c : Fin d) :
    c ∈ B.paddedFiber sigma a ↔ ∃ j ∈ columnWindow sigma c, B.bucket j = a := by
  simp [paddedFiber]

theorem quotient_paddedFiber_card (d M L : ℕ) (hL : 0 < L) (hc : d ≤ M * L)
    (sigma : ℕ) (a : Fin M) :
    ((quotient d M L hL hc).paddedFiber sigma a).card ≤ L + 2 * sigma := by
  let S := (quotient d M L hL hc).paddedFiber sigma a
  have hsub : S.image Fin.val ⊆ Finset.Ico (a.val * L - sigma) ((a.val + 1) * L + sigma) := by
    intro c hc'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨j, hj, heq⟩ := ((quotient d M L hL hc).mem_paddedFiber sigma a v).mp hv
    have hj' := (mem_columnWindow sigma v j).mp hj
    have heq' : j.val / L = a.val := congrArg Fin.val heq
    have hlo : a.val * L ≤ j.val := (Nat.le_div_iff_mul_le hL).mp heq'.ge
    have hhi : j.val < (a.val + 1) * L := (Nat.div_lt_iff_lt_mul hL).mp (by omega)
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hcard : S.card ≤ ((a.val + 1) * L + sigma) - (a.val * L - sigma) := by
    calc S.card = (S.image Fin.val).card := (Finset.card_image_of_injective S Fin.val_injective).symm
         _ ≤ (Finset.Ico (a.val * L - sigma) ((a.val + 1) * L + sigma)).card :=
           Finset.card_le_card hsub
         _ = _ := Nat.card_Ico _ _
  have he : (a.val + 1) * L = a.val * L + L := by ring
  rw [he] at hcard
  change S.card ≤ L + 2 * sigma
  omega

/-- The canonical choice has exactly the ceiling appearing in the packet bound. -/
def balanced (d M : ℕ) (hd : 0 < d) (hM : 0 < M) : RowBuckets d M :=
  let hcover : d ≤ M * (d ⌈/⌉ M) := (ceilDiv_le_iff_le_mul hM).mp le_rfl
  quotient d M (d ⌈/⌉ M) (by nlinarith) hcover

end RowBuckets

theorem columnWindow_interval {d : ℕ} (sigma : ℕ) (c : Fin d) :
    IsRowInterval (columnWindow sigma c) := by
  refine ⟨⟨c, mem_columnWindow_self _ _⟩, ?_⟩
  intro i hi j hj k hik hkj
  have hi' := (mem_columnWindow sigma c i).mp hi
  have hj' := (mem_columnWindow sigma c j).mp hj
  apply (mem_columnWindow sigma c k).mpr
  have h1 : i.val ≤ k.val := hik
  have h2 : k.val ≤ j.val := hkj
  omega

end TransposeFollowup
