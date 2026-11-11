import AdaptiveTransfer.TransferInputCone
import DirectedRecovery.StorageCode
import Mathlib.Logic.Equiv.Fin.Basic
import TapeStorageRates.PaidInputs

/-! Literal entry and interior-lane coordinates. No lane or self-edge is
discarded in the original relation; only the extracted code alphabet is eroded.
-/

namespace AdaptiveTransfer.TransferEntry
open Finset MergeDepth
attribute [local instance] Classical.propDecidable

def bit {n b : ℕ} (e : Fin n) (lane : Fin b) : Fin (n * b) := finProdFinEquiv (e, lane)
def entry {n b : ℕ} (p : Fin (n * b)) : Fin n := (finProdFinEquiv.symm p).1
def lane {n b : ℕ} (p : Fin (n * b)) : Fin b := (finProdFinEquiv.symm p).2

@[simp] theorem bit_val {n b : ℕ} (e : Fin n) (l : Fin b) :
    (bit e l).val = l.val + b * e.val := rfl
@[simp] theorem entry_bit {n b : ℕ} (e : Fin n) (l : Fin b) : entry (bit e l) = e := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (e, l))
@[simp] theorem lane_bit {n b : ℕ} (e : Fin n) (l : Fin b) : lane (bit e l) = l := by
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (e, l))
@[simp] theorem bit_entry_lane {n b : ℕ} (p : Fin (n * b)) : bit (entry p) (lane p) = p :=
  finProdFinEquiv.apply_symm_apply p

theorem coordinate_split {n b : ℕ} (p : Fin (n * b)) :
    p.val = (lane p).val + b * (entry p).val := by
  have hh := congrArg Fin.val (bit_entry_lane p)
  exact hh.symm

def interiorLane (b s : ℕ) (j : Fin (b - 6 * s)) : Fin b := ⟨3 * s + j.val, by omega⟩
def interiorBit {n b : ℕ} (s : ℕ) (e : Fin n) (j : Fin (b - 6 * s)) : Fin (n * b) :=
  bit e (interiorLane b s j)

theorem interiorBit_injective {n b s : ℕ} :
    Function.Injective (fun x : Fin n × Fin (b - 6 * s) => interiorBit s x.1 x.2) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ he
  have hpair := finProdFinEquiv.injective he
  have hentry := congrArg Prod.fst hpair
  have hlane := congrArg (fun x : Fin n × Fin b => x.2.val) hpair
  refine Prod.ext (show e = f from hentry) ?_
  apply Fin.ext
  change i.val = j.val
  change 3 * s + i.val = 3 * s + j.val at hlane
  omega

noncomputable def retainedBits {n : ℕ} (J : Finset (Fin n)) (b s : ℕ) : Finset (Fin (n * b)) :=
  univ.image fun x : J × Fin (b - 6 * s) => interiorBit s x.1.val x.2

theorem retainedBits_card {n : ℕ} (J : Finset (Fin n)) (b s : ℕ) :
    (retainedBits J b s).card = (b - 6 * s) * J.card := by
  rw [retainedBits, card_image_of_injective]
  · simp [Nat.mul_comm]
  · intro x y he
    have hh := interiorBit_injective (n := n) (b := b) (s := s)
      (a₁ := (x.1.val, x.2)) (a₂ := (y.1.val, y.2)) he
    exact Prod.ext (show x.1 = y.1 from Subtype.ext (congrArg Prod.fst hh))
      (show x.2 = y.2 from congrArg (fun z : Fin n × Fin (b - 6 * s) => z.2) hh)

theorem mem_retainedBits {n b s : ℕ} {J : Finset (Fin n)} {p : Fin (n * b)} :
    p ∈ retainedBits J b s ↔ entry p ∈ J ∧ 3 * s ≤ (lane p).val ∧ (lane p).val + 3 * s < b := by
  constructor
  · intro hp
    obtain ⟨⟨e, j⟩, _, rfl⟩ := mem_image.mp hp
    simp only [interiorBit, entry_bit, lane_bit, interiorLane]
    exact ⟨e.property, by omega, by omega⟩
  · rintro ⟨he, hlo, hhi⟩
    let j : Fin (b - 6 * s) := ⟨(lane p).val - 3 * s, by omega⟩
    refine mem_image.mpr ⟨(⟨entry p, he⟩, j), mem_univ _, ?_⟩
    have hj : interiorLane b s j = lane p := by
      apply Fin.ext
      change 3 * s + ((lane p).val - 3 * s) = (lane p).val
      omega
    exact (congrArg (bit (entry p)) hj).trans (bit_entry_lane p)

def project {n b : ℕ} (J : Finset (Fin n)) (s : ℕ) (X : Fin (n * b) → Bool) :
    J → Fin (b - 6 * s) → Bool := fun e j => X (interiorBit s e.val j)

theorem project_injective_of_exterior {n b s : ℕ} {J : Finset (Fin n)}
    {X Y : Fin (n * b) → Bool}
    (hext : ∀ p ∉ retainedBits J b s, X p = Y p) (hproj : project J s X = project J s Y) : X = Y := by
  funext p
  by_cases hp : p ∈ retainedBits J b s
  · obtain ⟨⟨e, j⟩, _, rfl⟩ := mem_image.mp hp
    exact congrFun (congrFun hproj e) j
  · exact hext p hp

/-- An interior raw coordinate and every valid radius-3s neighbor have the
same original entry. This does not restrict the neighbor's own lane. -/
theorem neighbor_same_entry {n b s : ℕ} {p q : Fin (n * b)}
    (hlo : 3 * s ≤ (lane p).val) (hhi : (lane p).val + 3 * s < b)
    (hnear : |(p.val : ℤ) - q.val| ≤ (3 * s : ℕ)) : entry q = entry p := by
  have hbounds := abs_le.mp hnear
  have hp := coordinate_split p
  rw [Nat.mul_comm b] at hp
  have hlo' : (entry p).val * b ≤ q.val := by omega
  have hhi' : q.val < ((entry p).val + 1) * b := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  apply Fin.ext
  change q.val / b = (entry p).val
  exact Nat.div_eq_of_lt_le hlo' hhi'

/-- Interior coordinates avoid both physical input boundary strips. -/
theorem interior_avoids_boundary {n b s : ℕ} {p : Fin (n * b)}
    (hlo : 3 * s ≤ (lane p).val) (hhi : (lane p).val + 3 * s < b) :
    3 * s ≤ p.val ∧ p.val + 3 * s < n * b := by
  have hp := coordinate_split p
  have he := (entry p).isLt
  constructor
  · omega
  · have hh : b * ((entry p).val + 1) ≤ b * n := Nat.mul_le_mul_left b he
    nlinarith

/-- The 2s look-ahead of an interior output lane exists and stays in its
entry. In particular it requires no final-output guard surcharge. -/
theorem interior_lookahead {n b s : ℕ} {p : Fin (n * b)}
    (hhi : (lane p).val + 3 * s < b) :
    p.val + 2 * s < n * b ∧
      ∀ hlt : p.val + 2 * s < n * b,
        entry (⟨p.val + 2 * s, hlt⟩ : Fin (n * b)) = entry p := by
  have hp := coordinate_split p
  have he := (entry p).isLt
  have hbound : b * ((entry p).val + 1) ≤ b * n := Nat.mul_le_mul_left b he
  have hlt : p.val + 2 * s < n * b := by nlinarith
  refine ⟨hlt, fun _ => ?_⟩
  apply Fin.ext
  change (p.val + 2 * s) / b = (entry p).val
  apply Nat.div_eq_of_lt_le <;> nlinarith

def transposeEntry {d : ℕ} (e : Fin (d * d)) : Fin (d * d) :=
  finProdFinEquiv ((finProdFinEquiv.symm e).2, (finProdFinEquiv.symm e).1)

@[simp] theorem transposeEntry_twice {d : ℕ} (e : Fin (d * d)) :
    transposeEntry (transposeEntry e) = e := by
  simp only [transposeEntry, Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

theorem tpos_bit {d b : ℕ} (e : Fin (d * d)) (l : Fin b) :
    tposOf d b (bit e l) = bit (transposeEntry e) l := by
  obtain ⟨⟨i,j⟩, rfl⟩ := (finProdFinEquiv : Fin d × Fin d ≃ _).surjective e
  simpa only [bit, transposeEntry, Equiv.symm_apply_apply,
    TapeStorageRates.PaidInputs.matrixAddr] using
    TapeStorageRates.PaidInputs.tpos_matrixAddr i j l

@[simp] theorem lane_tpos {d b : ℕ} (p : Fin (d * d * b)) :
    lane (tposOf d b p) = lane p := by
  conv_lhs => rw [← bit_entry_lane p, tpos_bit, lane_bit]

@[simp] theorem entry_tpos {d b : ℕ} (p : Fin (d * d * b)) :
    entry (tposOf d b p) = transposeEntry (entry p) := by
  conv_lhs => rw [← bit_entry_lane p, tpos_bit, entry_bit]

/-- A later output ordinal in an interior lane exists; after transposition its
demanded raw coordinate still belongs to the same original entry. -/
theorem interior_output_lookahead {d b s : ℕ} {p : Fin (d * d * b)}
    (hhi : (lane p).val + 3 * s < b) :
    (tposOf d b p).val + 2 * s < d * d * b ∧
      ∀ hlt : (tposOf d b p).val + 2 * s < d * d * b,
        entry (tposOf d b ⟨(tposOf d b p).val + 2 * s, hlt⟩) = entry p := by
  have hh := interior_lookahead (p := tposOf d b p) (s := s) (by simpa using hhi)
  refine ⟨hh.1, fun hlt => ?_⟩
  rw [entry_tpos, hh.2 hlt, entry_tpos, transposeEntry_twice]

/-- The raw target demanded by the output ordinal 2s later. The arbitrary
fallback is never used on a retained interior lane. -/
def futureTarget {d b : ℕ} (s : ℕ) (p : Fin (d * d * b)) : Fin (d * d * b) :=
  if h : (tposOf d b p).val + 2 * s < d * d * b then
    tposOf d b ⟨(tposOf d b p).val + 2 * s, h⟩ else p

theorem entry_futureTarget {d b s : ℕ} {p : Fin (d * d * b)}
    (hhi : (lane p).val + 3 * s < b) : entry (futureTarget s p) = entry p := by
  have hh := interior_output_lookahead hhi
  simpa only [futureTarget, dite_eq_left hh.1] using hh.2 hh.1

/-- Every lane contributes to the quotient; equal source and helper entries
are retained. The relation is induced on J only after this full quotient. -/
noncomputable def entryQuotient {n b : ℕ}
    (cones : Fin (n * b) → Finset (Fin (n * b))) (e : Fin n) : Finset (Fin n) :=
  univ.filter fun f => ∃ l : Fin b, ∃ p ∈ cones (bit e l), entry p = f

theorem mem_entryQuotient {n b : ℕ} {cones : Fin (n * b) → Finset (Fin (n * b))}
    {e f : Fin n} : f ∈ entryQuotient cones e ↔
      ∃ l : Fin b, ∃ p ∈ cones (bit e l), entry p = f := by
  simp only [entryQuotient, mem_filter, mem_univ, true_and]

end AdaptiveTransfer.TransferEntry
