import Transpose.Tape.Counting
import Transpose.Tape.Blocks
import Mathlib.Tactic

/-! Arbitrary finite slot labels on disjoint contiguous gadget windows.
Every nonconstant window consumes a different actual label change. A class
of good windows consumes at least its size times the minimum window length.
The change-between lemma is reused from the original paper.
-/

namespace TransposeFollowup

open Transpose.Tape Transpose.Tape.Impl
open scoped BigOperators
open Classical
set_option autoImplicit false

/-- The global r-slots wholly contained in the physical interval [a,c). -/
def fullSlots (r a c : ℕ) : Finset ℕ := Finset.Ico (numSlots r a) (c / r)

theorem mem_fullSlots {r a c s : ℕ} (hr : 0 < r) :
    s ∈ fullSlots r a c ↔ a ≤ s * r ∧ (s + 1) * r ≤ c := by
  have hl : numSlots r a ≤ s ↔ a ≤ s * r := by
    have h := not_congr (numSlots_spec (r := r) (T := a) (y := s) hr)
    simpa only [not_lt] using h
  simp only [fullSlots, Finset.mem_Ico, hl]
  exact and_congr_right (fun _ => by
    rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hr])

theorem fullSlots_card_lower {r a L : ℕ} (hr : 0 < r) :
    L - 1 ≤ (fullSlots r a (a + L * r)).card := by
  have hlo : numSlots r a ≤ a / r + 1 := by
    by_contra hn
    have hlt : a / r + 1 < numSlots r a := by omega
    have hb := (numSlots_spec hr).mp hlt
    have hd : a < a / r * r + r := Nat.lt_div_mul_add hr
    nlinarith
  have hhi : (a + L * r) / r = a / r + L := Nat.add_mul_div_right a L hr
  rw [fullSlots, Nat.card_Ico, hhi]
  omega

theorem fullSlots_disjoint {r a c a' c' : ℕ} (hr : 0 < r) (hca : c ≤ a') :
    Disjoint (fullSlots r a c) (fullSlots r a' c') := by
  apply Finset.disjoint_left.mpr
  intro s hs hs'
  obtain ⟨_, hsc⟩ := (mem_fullSlots hr).mp hs
  obtain ⟨has, _⟩ := (mem_fullSlots hr).mp hs'
  nlinarith

def badWindows {V : Type*} [Fintype V] (lab : ℕ → ℕ) (lo hi : V → ℕ) : Finset V :=
  Finset.univ.filter (fun v => ∃ s ∈ Finset.Ico (lo v) (hi v), lab s ≠ lab (lo v))

theorem badWindows_card_le {V : Type*} [Fintype V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) (N : ℕ)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hN : ∀ i, hi i ≤ N) :
    (badWindows lab lo hi).card ≤ labelChanges lab N := by
  let CH := (Finset.range N).filter (fun s => 1 ≤ s ∧ lab s ≠ lab (s - 1))
  have hex : ∀ i : badWindows lab lo hi, ∃ u, u ∈ CH ∧ lo i.val < u ∧ u < hi i.val := by
    intro i
    obtain ⟨_, s, hs, hl⟩ := Finset.mem_filter.mp i.property
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hs
    have hlt : lo i.val < s := by
      by_contra hn
      have he : s = lo i.val := by omega
      exact hl (congrArg lab he)
    obtain ⟨u, hu, hu', hchange⟩ := label_change_between lab hlt (Ne.symm hl)
    refine ⟨u, ?_, hu, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hN i.val; omega),
      by omega, hchange⟩
  let code : badWindows lab lo hi → CH := fun i => ⟨(hex i).choose, (hex i).choose_spec.1⟩
  have hinj : Function.Injective code := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    have hui := (hex i).choose_spec.2
    have huj := (hex j).choose_spec.2
    have hu := congrArg Subtype.val he
    change (hex i).choose = (hex j).choose at hu
    rcases hsep i.val j.val hne with h | h <;> omega
  have hc := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe, CH, labelChanges] using hc

/-- No regularity of the labels is assumed: they may vary with input size
and between every adjacent pair of slots. -/
theorem good_window_class_size {V : Type*} [Fintype V]
    (lab : ℕ → ℕ) (lo hi : V → ℕ) (N L m ell : ℕ)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hN : ∀ i, hi i ≤ N) (hL : ∀ i, L ≤ hi i - lo i)
    (hm : ((Finset.range N).filter (fun s => lab s = ell)).card ≤ m) :
    L * (Finset.univ.filter (fun i => i ∉ badWindows lab lo hi ∧ lab (lo i) = ell)).card ≤ m := by
  let S := Finset.univ.filter (fun i => i ∉ badWindows lab lo hi ∧ lab (lo i) = ell)
  have hdis : (S : Set V).PairwiseDisjoint (fun i => Finset.Ico (lo i) (hi i)) := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro u hiu hju
    obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hiu
    obtain ⟨hjl, hjh⟩ := Finset.mem_Ico.mp hju
    rcases hsep i j hne with h | h <;> omega
  have hsub : S.biUnion (fun i => Finset.Ico (lo i) (hi i)) ⊆
      (Finset.range N).filter (fun s => lab s = ell) := by
    intro u hu
    obtain ⟨i, hiS, hiu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨_, hgood, hell⟩ := Finset.mem_filter.mp hiS
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hiu).2 (hN i)), ?_⟩
    have he : lab u = lab (lo i) := by
      by_contra hn
      exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hiu, hn⟩)
    exact he.trans hell
  calc
    _ = ∑ _i ∈ S, L := by simp [S, Nat.mul_comm]
    _ ≤ ∑ i ∈ S, (Finset.Ico (lo i) (hi i)).card := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.card_Ico] using hL i
    _ = (S.biUnion (fun i => Finset.Ico (lo i) (hi i))).card := (Finset.card_biUnion hdis).symm
    _ ≤ ((Finset.range N).filter (fun s => lab s = ell)).card := Finset.card_le_card hsub
    _ ≤ m := hm

end TransposeFollowup
