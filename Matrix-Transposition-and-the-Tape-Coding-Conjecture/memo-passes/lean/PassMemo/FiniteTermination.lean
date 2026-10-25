import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-! A terminating deterministic finite-state path cannot repeat a live state. -/

namespace PassMemo

open Finset

/-- If a deterministic finite state trajectory eventually reaches `none`, then
it does so within the number of live states. No cycle-detection oracle is used. -/
theorem exists_exit_le_card {S : Type*} [Fintype S]
    (f : Option S → Option S) (s : Option S)
    (hterm : ∃ n, f^[n] s = none) :
    ∃ n ≤ Fintype.card S, f^[n] s = none := by
  classical
  let n := Nat.find hterm
  have hn : f^[n] s = none := Nat.find_spec hterm
  have hmin : ∀ j < n, f^[j] s ≠ none := fun j hj => Nat.find_min hterm hj
  have hinj : Function.Injective (fun i : Fin n => f^[i.val] s) := by
    intro i j heq
    apply Fin.ext
    by_contra hne
    have bad : ∀ (a b : ℕ), a < b → b < n → f^[a] s = f^[b] s → False := by
      intro a b hab hbn habsig
      have hsmall : n - b + a < n := by omega
      apply hmin _ hsmall
      calc f^[n - b + a] s = f^[n - b] (f^[a] s) := Function.iterate_add_apply _ _ _ _
        _ = f^[n - b] (f^[b] s) := congrArg (f^[n - b]) habsig
        _ = f^[n] s := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        _ = none := hn
    rcases lt_or_gt_of_ne hne with h | h
    · exact bad i j h j.isLt heq
    · exact bad j i h i.isLt heq.symm
  have hsub : (univ.image (fun i : Fin n => f^[i.val] s)) ⊆ univ.erase none := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_erase.mpr ⟨hmin _ i.isLt, mem_univ _⟩
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_option] at hcard
  exact ⟨n, by omega, hn⟩

/-- Any initial interval consisting entirely of live states has bounded length. -/
theorem live_prefix_le_card {S : Type*} [Fintype S]
    (f : Option S → Option S) (s : Option S)
    (hterm : ∃ n, f^[n] s = none) {m : ℕ}
    (hlive : ∀ j < m, f^[j] s ≠ none) : m ≤ Fintype.card S := by
  obtain ⟨n, hn, hnone⟩ := exists_exit_le_card f s hterm
  by_contra h
  exact hlive n (by omega) hnone

end PassMemo
