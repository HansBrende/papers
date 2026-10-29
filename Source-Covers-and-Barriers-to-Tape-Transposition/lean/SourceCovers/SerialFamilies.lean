import SourceCovers.NativeBankFamily
import SourceCovers.SerialWalks

set_option autoImplicit false

/-! The complete actual-family table of the eight-head construction.
Bank indices are the consecutive span indices used in the manuscript. -/

namespace SourceCovers.SerialGeometry.Parameters

open Finset BoundedNesting
noncomputable section

variable (P : Parameters)

def bankBase (c : Fin 2) : ℕ := if c.val = 0 then 4 * P.length else 11 * P.length

def bankHeadIndex (c : Fin 2) (j : Fin P.bankCount) : Fin 4 :=
  ⟨2 * c.val + j.val / 2 % 2, by have := c.isLt; have := Nat.mod_lt (j.val / 2) (by omega : 0 < 2); omega⟩

def bankRound (j : Fin P.bankCount) : Fin (2 * P.m) :=
  ⟨j.val / 4, by have := j.isLt; unfold bankCount at this; omega⟩

def bankTurn (j : Fin P.bankCount) : Fin 2 := ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩

theorem bankStart_index (c : Fin 2) (j : Fin P.bankCount) :
    P.bankStart (P.bankHeadIndex c j) = P.bankBase c + 2 * (j.val / 2 % 2) * P.width := by
  have hc := c.isLt
  have hj := Nat.mod_lt (j.val / 2) (by omega : 0 < 2)
  have hmod : (2 * c.val + j.val / 2 % 2) % 2 = j.val / 2 % 2 := by omega
  have hsmall : 2 * c.val + j.val / 2 % 2 < 2 ↔ c.val = 0 := by omega
  simp only [bankStart, bankHeadIndex, hsmall, hmod, bankBase]

theorem bank_owner_index (c : Fin 2) (j : Fin P.bankCount) :
    NativeBank.turnOwner P.width (P.bankStart (P.bankHeadIndex c j))
      (P.bankRound j) (P.bankTurn j) = P.bankBase c + (j.val + 1) * P.width := by
  have hj : 4 * (j.val / 4) + 2 * (j.val / 2 % 2) + j.val % 2 = j.val := by omega
  simp only [NativeBank.turnOwner, NativeBank.start, bankStart_index, bankRound, bankTurn]
  nlinarith [congrArg (fun a : ℕ => a * P.width) hj]

theorem bankFamily_before_horizon (c : Fin 2) (j : Fin P.bankCount) :
    NativeBank.turnOwner P.width (P.bankStart (P.bankHeadIndex c j))
      (P.bankRound j) (P.bankTurn j) + P.width < P.horizon := by
  have hb := NativeBank.turnOwner_bounds P.width (P.bankStart (P.bankHeadIndex c j))
    (P.bankRound j) (P.bankTurn j)
  have ht := P.bank_before_horizon (P.bankHeadIndex c j) (P.bankRound j)
  omega

def bankFamily (c : Fin 2) (j : Fin P.bankCount) : ActualFamily P.heads P.horizon :=
  NativeBank.family (h := P.width) (D := P.bankStart (P.bankHeadIndex c j))
    (n := 2 * P.m) (T := P.horizon) (Fin.castAdd 4 (P.bankHeadIndex c j))
    (P.heads_bank (P.bankHeadIndex c j)) (P.bankRound j) (P.bankTurn j)
    (P.bankFamily_before_horizon c j)

@[simp] theorem bankFamily_head (c : Fin 2) (j : Fin P.bankCount) :
    (P.bankFamily c j).val.1 = Fin.castAdd 4 (P.bankHeadIndex c j) := rfl

@[simp] theorem bankFamily_owner (c : Fin 2) (j : Fin P.bankCount) :
    (P.bankFamily c j).owner = P.bankBase c + (j.val + 1) * P.width :=
  P.bank_owner_index c j

@[simp] theorem bankFamily_start (c : Fin 2) (j : Fin P.bankCount) :
    (P.bankFamily c j).start = P.bankBase c + j.val * P.width := by
  rw [bankFamily, NativeBank.family_start, bank_owner_index,
    Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_sub_cancel]

@[simp] theorem bankFamily_stop (c : Fin 2) (j : Fin P.bankCount) :
    (P.bankFamily c j).stop = P.bankBase c + (j.val + 2) * P.width := by
  rw [bankFamily, NativeBank.family_stop, bank_owner_index]
  ring

@[simp] theorem bankFamily_card (c : Fin 2) (j : Fin P.bankCount) :
    (P.bankFamily c j).hops.card = P.width := NativeBank.family_card _ _ _ _ _

theorem bankFamily_hops (c : Fin 2) (j : Fin P.bankCount) :
    (P.bankFamily c j).hops = univ.image (fun a : Fin P.width =>
      (Fin.castAdd 4 (P.bankHeadIndex c j),
        P.bankBase c + (j.val + 1) * P.width - (a.val + 1),
        P.bankBase c + (j.val + 1) * P.width + (a.val + 1))) := by
  rw [bankFamily, NativeBank.family_hops, bank_owner_index]

theorem bankFamily_shadow_active (c : Fin 2) (j : Fin P.bankCount) {t : ℕ}
    (ht : P.bankBase c + (j.val + 1) * P.width < t)
    (hu : t ≤ P.bankBase c + (j.val + 2) * P.width) :
    (P.bankFamily c j).shadow t =
      max (P.bankBase c + j.val * P.width + 1)
        (2 * (P.bankBase c + (j.val + 1) * P.width) - t) := by
  have he : P.bankBase c + (j.val + 1) * P.width + P.width =
      P.bankBase c + (j.val + 2) * P.width := by ring
  have hs := NativeBank.family_shadow_active (Fin.castAdd 4 (P.bankHeadIndex c j))
    (P.heads_bank (P.bankHeadIndex c j)) (P.bankRound j) (P.bankTurn j)
    (P.bankFamily_before_horizon c j) P.heads_isWalk
    (by rw [P.bank_owner_index]; exact ht)
    (by rw [P.bank_owner_index, he]; exact hu)
  simpa only [bankFamily, bank_owner_index, Nat.add_mul, Nat.one_mul,
    ← Nat.add_assoc, Nat.add_sub_cancel] using hs

theorem bankFamily_injective :
    Function.Injective (fun cj : Fin 2 × Fin P.bankCount => P.bankFamily cj.1 cj.2) := by
  rintro ⟨c, j⟩ ⟨c', j'⟩ he
  have hh := congrArg (fun F : ActualFamily P.heads P.horizon => F.val.1.val) he
  change 2 * c.val + j.val / 2 % 2 = 2 * c'.val + j'.val / 2 % 2 at hh
  have hc : c = c' := Fin.ext (by omega)
  subst c'
  have hs := congrArg ActualFamily.start he
  simp only [bankFamily_start, Nat.add_left_cancel_iff] at hs
  exact Prod.ext rfl (Fin.ext (Nat.eq_of_mul_eq_mul_right P.width_pos hs))

/-- Inverse reindexing recovers a head, round, and turn without selecting
or discarding any member of the actual family system. -/
theorem bank_indices_surjective (q : Fin 4) (r : Fin (2 * P.m)) (a : Fin 2) :
    ∃ c : Fin 2, ∃ j : Fin P.bankCount,
      P.bankHeadIndex c j = q ∧ P.bankRound j = r ∧ P.bankTurn j = a := by
  let c : Fin 2 := ⟨q.val / 2, by have := q.isLt; omega⟩
  let j : Fin P.bankCount := ⟨4 * r.val + 2 * (q.val % 2) + a.val, by
    have := r.isLt
    have := a.isLt
    have := Nat.mod_lt q.val (by omega : 0 < 2)
    unfold bankCount
    omega⟩
  refine ⟨c, j, ?_, ?_, ?_⟩
  all_goals apply Fin.ext; dsimp only [bankHeadIndex, bankRound, bankTurn, c, j]
  all_goals have := q.isLt; have := a.isLt; omega

theorem bankFamily_exhaustive (F : ActualFamily P.heads P.horizon)
    (hh : F.val.1.val < 4) : ∃ c : Fin 2, ∃ j : Fin P.bankCount, F = P.bankFamily c j := by
  let q : Fin 4 := ⟨F.val.1.val, hh⟩
  have hq : F.val.1 = Fin.castAdd 4 q := Fin.ext rfl
  have hT : ∀ r : Fin (2 * P.m), ∀ a : Fin 2,
      NativeBank.turnOwner P.width (P.bankStart q) r a + P.width < P.horizon := by
    intro r a
    have hb := NativeBank.turnOwner_bounds P.width (P.bankStart q) r a
    have ht := P.bank_before_horizon q r
    omega
  obtain ⟨r, a, hF⟩ := NativeBank.family_exhaustive (h := P.width) (D := P.bankStart q)
    (n := 2 * P.m) (Fin.castAdd 4 q) (P.heads_bank q) hT F hq
  obtain ⟨c, j, he, hr, ha⟩ := P.bank_indices_surjective q r a
  refine ⟨c, j, ?_⟩
  apply Subtype.ext
  have hf := congrArg Subtype.val hF
  change F.val = (Fin.castAdd 4 q, decide (a.val = 0),
    NativeBank.turnOwner P.width (P.bankStart q) r a) at hf
  change F.val = (Fin.castAdd 4 (P.bankHeadIndex c j), decide ((P.bankTurn j).val = 0),
    NativeBank.turnOwner P.width (P.bankStart (P.bankHeadIndex c j)) (P.bankRound j) (P.bankTurn j))
  simpa only [he, hr, ha] using hf

/-- This exhausts the original actual families of all eight walks. -/
theorem actualFamily_exhaustive (F : ActualFamily P.heads P.horizon) :
    (∃ c : Fin 2, ∃ j : Fin P.bankCount, F = P.bankFamily c j) ∨
      F = P.newerFamily ∨ F = P.earlyFamily ∨ F = P.olderFamily ∨ F = P.bridgeFamily := by
  by_cases hh : F.val.1.val < 4
  · exact Or.inl (P.bankFamily_exhaustive F hh)
  · right
    have hf := F.val.1.isLt
    have he : F.val.1.val = 4 ∨ F.val.1.val = 5 ∨ F.val.1.val = 6 ∨ F.val.1.val = 7 := by omega
    rcases he with he | he | he | he
    · exact Or.inl (NativeExcursion.family_unique P.newer 4 P.heads_newer
        (P.newer_before_horizon 0) F (Fin.ext he))
    · exact Or.inr (Or.inl (NativeExcursion.family_unique P.early 5 P.heads_early _ F (Fin.ext he)))
    · exact Or.inr (Or.inr (Or.inl (NativeExcursion.family_unique P.older 6 P.heads_older
        (P.older_before_horizon 0) F (Fin.ext he))))
    · exact Or.inr (Or.inr (Or.inr (NativeExcursion.family_unique P.bridge 7 P.heads_bridge
        (P.bridge_before_horizon 0) F (Fin.ext he))))

end
end SourceCovers.SerialGeometry.Parameters
