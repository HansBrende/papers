import LeanMachine.DisjointSums
import Mathlib.Data.Fintype.Powerset

/-! The subset placement-delivery code, with arbitrary row and column
repetitions and entries in any abelian group. The supports, encoder and
raw-row decoder are explicit; no rank or recovery premise is assumed. -/

namespace LeanMachine.SubsetPlacement

open Finset
open scoped BigOperators Classical
noncomputable section

abbrev Subset (α : Type*) (k : ℕ) := {S : Finset α // S.card = k}
abbrev Entry (α : Type*) (k : ℕ) (U Z : Type*) := α × Subset α k × U × Z
abbrev Packet (α : Type*) (k : ℕ) (U Z : Type*) := Subset α (k + 1) × U × Z

variable {α U Z : Type*} {k : ℕ} [Fintype α] [Fintype U] [Fintype Z]

/-- Exactly the entries in the parity indexed by `(T,u,z)`. -/
def support (p : Packet α k U Z) : Finset (Entry α k U Z) :=
  univ.filter fun e => e.1 ∉ e.2.1.val ∧
    insert e.1 e.2.1.val = p.1.val ∧ e.2.2 = p.2

@[simp] theorem mem_support (p : Packet α k U Z) (e : Entry α k U Z) :
    e ∈ support p ↔ e.1 ∉ e.2.1.val ∧
      insert e.1 e.2.1.val = p.1.val ∧ e.2.2 = p.2 := by
  simp [support]

/-- The unique parity containing a nonqueried entry. -/
def owner (e : Entry α k U Z) (he : e.1 ∉ e.2.1.val) : Packet α k U Z :=
  (⟨insert e.1 e.2.1.val, by simp [he, e.2.1.property]⟩, e.2.2)

theorem mem_owner (e : Entry α k U Z) (he : e.1 ∉ e.2.1.val) :
    e ∈ support (owner e he) := by simp [owner, he]

theorem support_nonempty (p : Packet α k U Z) : (support p).Nonempty := by
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < p.1.val.card by rw [p.1.property]; omega)
  let S : Subset α k := ⟨p.1.val.erase i, by rw [card_erase_of_mem hi, p.1.property]; omega⟩
  refine ⟨(i, S, p.2), ?_⟩
  simp [S, insert_erase hi]

theorem support_disjoint : Pairwise fun p q : Packet α k U Z =>
    Disjoint (support p) (support q) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro e hp hq
  obtain ⟨_, hp, hrp⟩ := (mem_support p e).mp hp
  obtain ⟨_, hq, hrq⟩ := (mem_support q e).mp hq
  exact hpq (Prod.ext (Subtype.ext (hp.symm.trans hq)) (hrp.symm.trans hrq))

def code : DisjointSums (Entry α k U Z) (Packet α k U Z) where
  support := support
  nonempty := support_nonempty
  disjoint := support_disjoint

theorem queried_absent (e : Entry α k U Z) (he : e.1 ∈ e.2.1.val)
    (p : Packet α k U Z) : e ∉ (code (α := α) (k := k) (U := U) (Z := Z)).support p := by
  intro h
  exact ((mem_support p e).mp h).1 he

/-- Within one parity each row bin occurs only once. -/
theorem eq_of_same_bin {p : Packet α k U Z} {e f : Entry α k U Z}
    (he : e ∈ support p) (hf : f ∈ support p) (hbin : e.1 = f.1) : e = f := by
  obtain ⟨hne, he, hre⟩ := (mem_support p e).mp he
  obtain ⟨hnf, hf, hrf⟩ := (mem_support p f).mp hf
  have hcols : e.2.1.val = f.2.1.val := by
    have h := congrArg (fun S => S.erase e.1) (he.trans hf.symm)
    have hne' : f.1 ∉ e.2.1.val := hbin ▸ hne
    simpa [hbin, hne', hnf] using h
  exact Prod.ext hbin (Prod.ext (Subtype.ext hcols) (hre.trans hrf.symm))

/-- The displayed `(i,u,T \ {i},z)` summand of a packet. -/
def summand (p : Packet α k U Z) (i : p.1.val) : Entry α k U Z :=
  (i, ⟨p.1.val.erase i, by rw [card_erase_of_mem i.property, p.1.property]; omega⟩, p.2)

theorem summand_mem (p : Packet α k U Z) (i : p.1.val) : summand p i ∈ support p := by
  simp [summand, insert_erase i.property]

omit [Fintype α] [Fintype U] [Fintype Z] in
theorem summand_injective (p : Packet α k U Z) : Function.Injective (summand p) := by
  intro i j he
  exact Subtype.ext (congrArg Prod.fst he)

theorem support_eq_image (p : Packet α k U Z) : support p = univ.image (summand p) := by
  ext e
  constructor
  · intro he
    have hi : e.1 ∈ p.1.val := by
      rw [← ((mem_support p e).mp he).2.1]
      exact mem_insert_self _ _
    exact mem_image.mpr ⟨⟨e.1, hi⟩, mem_univ _,
      eq_of_same_bin (summand_mem p ⟨e.1, hi⟩) he rfl⟩
  · rintro he
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    exact summand_mem p i

/-- The encoder is exactly the specified subset parity, with one summand
per member of `T`. For binary words the group sum is bitwise XOR. -/
theorem encode_eq {A : Type*} [AddCommGroup A]
    (x : Entry α k U Z → A) (p : Packet α k U Z) :
    code.encode x p = ∑ i : p.1.val, x (summand p i) := by
  change (∑ e ∈ support p, x e) = _
  rw [support_eq_image, sum_image]
  exact fun _ _ _ _ he => summand_injective p he

/-- Every other summand in an entry's parity belongs to a queried row bin. -/
theorem other_bin_queried (e : Entry α k U Z) (he : e.1 ∉ e.2.1.val)
    {f : Entry α k U Z} (hf : f ∈ (support (owner e he)).erase e) :
    f.1 ∈ e.2.1.val := by
  obtain ⟨hne, hf⟩ := mem_erase.mp hf
  have hmem : f.1 ∈ insert e.1 e.2.1.val := by
    change f.1 ∈ (owner e he).1.val
    rw [← ((mem_support _ f).mp hf).2.1]
    exact mem_insert_self _ _
  rcases mem_insert.mp hmem with hbin | hbin
  · exact False.elim (hne (eq_of_same_bin hf (mem_owner e he) hbin))
  · exact hbin

/-- Equality of the helper and all queried raw rows determines the target
entry, for every input. The raw rows may include all columns. -/
theorem entry_recovery {A : Type*} [AddCommGroup A]
    (x y : Entry α k U Z → A) (e : Entry α k U Z)
    (hhelper : code.encode x = code.encode y)
    (hrows : ∀ f, f.1 ∈ e.2.1.val → x f = y f) : x e = y e := by
  by_cases he : e.1 ∈ e.2.1.val
  · exact hrows e he
  · let p := owner e he
    have hm : e ∈ code.support p := mem_owner e he
    rw [code.recover x p hm, code.recover y p hm, hhelper]
    congr 1
    apply sum_congr rfl
    exact fun f hf => hrows f (other_bin_queried e he hf)

theorem card_entry : Fintype.card (Entry α k U Z) =
    Fintype.card α * (Fintype.card α).choose k * Fintype.card U * Fintype.card Z := by
  simp [Entry, Subset, Fintype.card_finset_len, mul_assoc]

theorem card_packet : Fintype.card (Packet α k U Z) =
    (Fintype.card α).choose (k + 1) * Fintype.card U * Fintype.card Z := by
  simp [Packet, Subset, Fintype.card_finset_len, mul_assoc]

end
end LeanMachine.SubsetPlacement
