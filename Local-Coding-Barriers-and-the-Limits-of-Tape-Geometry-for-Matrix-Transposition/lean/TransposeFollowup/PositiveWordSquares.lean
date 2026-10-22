import TransposeFollowup.FreeWordSquares
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi

/-! All positive binary words of length L give 2^L freely generating
squares, each of reduced length 2L. No endpoint restrictions are needed. -/
namespace TransposeFollowup.FreeWordFamily
open Classical FreeGroup List
set_option autoImplicit false

def positiveWord {L : ℕ} (f : Fin L → Bool) : List (Bool × Bool) :=
  List.ofFn (fun i => (f i, true))

theorem positiveWord_length {L : ℕ} (f : Fin L → Bool) : (positiveWord f).length = L := by
  simp [positiveWord]

theorem positiveWord_sign {L : ℕ} (f : Fin L → Bool) (a : Bool × Bool)
    (ha : a ∈ positiveWord f) : a.2 = true := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  rfl

theorem positiveWord_injective (L : ℕ) : Function.Injective (@positiveWord L) := by
  intro f g h
  have he := List.ofFn_injective h
  funext i
  exact congrArg Prod.fst (congrFun he i)

theorem reduced_of_positive {α : Type*} (w : List (α × Bool))
    (hw : ∀ a ∈ w, a.2 = true) : IsReduced w := by
  rw [FreeGroup.IsReduced, List.isChain_iff_forall_rel_of_append_cons_cons]
  intro a b l₁ l₂ he _
  have ha := hw a (by rw [he]; simp)
  have hb := hw b (by rw [he]; simp)
  exact ha.trans hb.symm

def squareWord {L : ℕ} (f : Fin L → Bool) : List (Bool × Bool) :=
  positiveWord f ++ positiveWord f

theorem squareWord_length {L : ℕ} (f : Fin L → Bool) : (squareWord f).length = 2 * L := by
  simp [squareWord, positiveWord_length, two_mul]

theorem squareWord_reduced {L : ℕ} (f : Fin L → Bool) : IsReduced (squareWord f) := by
  apply reduced_of_positive
  intro a ha
  rcases List.mem_append.mp ha with ha | ha <;> exact positiveWord_sign f a ha

theorem positiveWord_ne_inverse {L : ℕ} (hL : 0 < L) (f g : Fin L → Bool) :
    positiveWord f ≠ invRev (positiveWord g) := by
  intro he
  have hn : positiveWord f ≠ [] := by
    intro hz
    have := positiveWord_length f
    rw [hz] at this
    simp only [List.length_nil] at this
    omega
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil (positiveWord f) hn
  have hs := positiveWord_sign f a ha
  rw [he] at ha
  obtain ⟨b, hb, hab⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  have hbpos := positiveWord_sign g b hb
  have hbsign := congrArg Prod.snd hab
  simp only [hbpos, Bool.not_true, hs] at hbsign
  cases hbsign

def positiveSquare {L : ℕ} (f : Fin L → Bool) : FreeGroup Bool := (mk (positiveWord f)) ^ 2

theorem positiveSquare_eq_mk {L : ℕ} (f : Fin L → Bool) :
    positiveSquare f = mk (squareWord f) := by
  rw [positiveSquare, pow_two, mul_mk]
  rfl

theorem positiveSquare_toWord {L : ℕ} (f : Fin L → Bool) :
    (positiveSquare f).toWord = squareWord f := by
  rw [positiveSquare_eq_mk, toWord_mk, (squareWord_reduced f).reduce_eq]

theorem positiveSquares_free {L : ℕ} (hL : 0 < L) :
    Function.Injective (FreeGroup.lift (@positiveSquare L)) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  exact squares_free positiveWord squareWord_reduced
    (fun f g => (positiveWord_length f).trans (positiveWord_length g).symm)
    (positiveWord_injective L) (positiveWord_ne_inverse hL)

theorem positiveSquare_injective {L : ℕ} (hL : 0 < L) :
    Function.Injective (@positiveSquare L) := by
  intro f g he
  apply FreeGroup.of_injective
  apply positiveSquares_free hL
  simpa only [FreeGroup.lift_apply_of] using he

theorem positiveSquare_card {L : ℕ} (hL : 0 < L) :
    (Finset.univ.image (@positiveSquare L)).card = 2 ^ L := by
  rw [Finset.card_image_of_injective _ (positiveSquare_injective hL)]
  simp

end TransposeFollowup.FreeWordFamily
