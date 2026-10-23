import BitWord.CanonicalGates

namespace BitWord

def Gate.inverse : Gate → Gate
  | .suffix k => .suffix k
  | .right => .left
  | .left => .right

@[simp] theorem Gate.inverse_inverse (g : Gate) : g.inverse.inverse = g := by cases g <;> rfl

theorem Gate.inverse_legal {N : ℕ} {g : Gate} (hg : g.Legal N) : g.inverse.Legal N := by
  cases g <;> exact hg

theorem Gate.inverse_apply {N x : ℕ} {g : Gate} (hg : g.Legal N) (hx : x < N) :
    g.inverse.apply N (g.apply N x) = x := by
  cases g with
  | suffix k => exact suffixSwap_involutive hg hx
  | right =>
    change rotateLeft N (rotateRight N x) = x
    by_cases h : x+1 < N
    · simp [rotateRight, rotateLeft, h]
    · simp [rotateRight, rotateLeft, h]
      omega
  | left => change 0 < N at hg; dsimp [Gate.inverse, Gate.apply, rotateLeft, rotateRight]; split_ifs <;> omega

def Gate.equiv (N : ℕ) (g : Gate) (hg : g.Legal N) : Fin N ≃ Fin N where
  toFun x := ⟨g.apply N x, Gate.apply_lt hg x.isLt⟩
  invFun x := ⟨g.inverse.apply N x, Gate.apply_lt (Gate.inverse_legal hg) x.isLt⟩
  left_inv x := Fin.ext (Gate.inverse_apply hg x.isLt)
  right_inv x := Fin.ext (by simpa using Gate.inverse_apply (Gate.inverse_legal hg) x.isLt)

/-- Exact chronological action on finite address positions. -/
def gatesEquiv (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.Legal N) : Fin N ≃ Fin N :=
  match gs with
  | [] => Equiv.refl _
  | g::rest => (g.equiv N (hg g (by simp))).trans
      (gatesEquiv N rest (fun a ha => hg a (List.mem_cons_of_mem _ ha)))

@[simp] theorem gatesEquiv_val (N : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.Legal N) (x : Fin N) :
    (gatesEquiv N gs hg x).val = runGates N gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _ _

def headEquiv (h w : ℕ) : Fin (2*h+w) ≃ Fin (2*h+w) where
  toFun x := ⟨headSwap h x, by unfold headSwap; split_ifs <;> omega⟩
  invFun x := ⟨headSwap h x, by unfold headSwap; split_ifs <;> omega⟩
  left_inv x := Fin.ext (by change headSwap h (headSwap h x.val) = x.val; unfold headSwap; split_ifs <;> omega)
  right_inv x := Fin.ext (by change headSwap h (headSwap h x.val) = x.val; unfold headSwap; split_ifs <;> omega)

theorem canonicalGates_equiv {h : ℕ} (hh : 0 < h) :
    gatesEquiv (2*h+tailBits h) (canonicalGates h) (canonicalGates_legal hh) =
      headEquiv h (tailBits h) := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [gatesEquiv_val, canonicalGates_correct hh x.isLt]
  rfl

/-- Lift a position permutation to all binary addresses. -/
def addressEquiv {N : ℕ} (p : Fin N ≃ Fin N) : Address N ≃ Address N where
  toFun := moveAddress p
  invFun := moveAddress p.symm
  left_inv a := by funext i; simp [moveAddress]
  right_inv a := by funext i; simp [moveAddress]

/-- A raw bank indexed by its binary addresses; its values need not be bits. -/
def moveBank {N : ℕ} {α : Type*} (p : Fin N ≃ Fin N) (bank : Address N → α) :
    Address N → α := fun a => bank ((addressEquiv p).symm a)

theorem canonical_bank_action {h : ℕ} (hh : 0 < h) {α : Type*}
    (bank : Address (2*h+tailBits h) → α) :
    moveBank (gatesEquiv _ (canonicalGates h) (canonicalGates_legal hh)) bank =
      moveBank (headEquiv h (tailBits h)) bank := by
  rw [canonicalGates_equiv hh]

/-- The row field of the new address is the old column field. -/
theorem headAddress_row {h w i : ℕ} (hi : i < h) (a : Address (2*h+w)) :
    addressEquiv (headEquiv h w) a ⟨i, by omega⟩ = a ⟨i+h, by omega⟩ := by
  change a ⟨headSwap h i, _⟩ = _
  simp [headSwap, hi]

theorem headAddress_column {h w i : ℕ} (hi : i < h) (a : Address (2*h+w)) :
    addressEquiv (headEquiv h w) a ⟨h+i, by omega⟩ = a ⟨i, by omega⟩ := by
  change a ⟨headSwap h (h+i), _⟩ = _
  apply congrArg a
  apply Fin.ext
  change headSwap h (h+i) = i
  unfold headSwap
  split_ifs <;> omega

theorem headAddress_tail {h w i : ℕ} (hi : i < w) (a : Address (2*h+w)) :
    addressEquiv (headEquiv h w) a ⟨2*h+i, by omega⟩ = a ⟨2*h+i, by omega⟩ := by
  change a ⟨headSwap h (2*h+i), _⟩ = _
  apply congrArg a
  apply Fin.ext
  change headSwap h (2*h+i) = 2*h+i
  unfold headSwap
  split_ifs <;> omega

end BitWord
