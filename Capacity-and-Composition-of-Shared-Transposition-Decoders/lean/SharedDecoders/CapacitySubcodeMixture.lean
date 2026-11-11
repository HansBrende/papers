import SharedDecoders.CapacityTripleBinary
import SharedDecoders.CapacitySubcodeRepeat
import SharedDecoders.ConstructionLinearLift

/-! # Actual coupled-lane sources above half with all linear subcodes below half -/

namespace SharedDecoders.CapacitySubcode

open Module
abbrev Bit := ZMod 2

variable {d : ℕ} [NeZero d] {κ : Type*}

theorem combine_binary_codes {g h : ℕ} {p : ZMod d → κ}
    (G : Submodule Bit (State d (Fin g → Bit)))
    (H : Submodule Bit (State d (Fin h → Bit)))
    (hG : IsSharedCode Bit p G) (hH : IsSharedCode Bit p H)
    (L : ℕ) (hL : ∀ C ≤ H, IsLinearSharedCode p C → finrank Bit C ≤ L) :
    ∃ C : Submodule Bit (State d (Fin (g + h) → Bit)), IsSharedCode Bit p C ∧
      finrank Bit C = finrank Bit G + finrank Bit H ∧
      ∀ D ≤ C, IsLinearSharedCode p D → finrank Bit D ≤ finrank Bit G + L := by
  let e : ((Fin g → Bit) × (Fin h → Bit)) ≃ₗ[Bit] (Fin (g + h) → Bit) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_prod])
  refine ⟨(productCode G H).map (entryEquiv e).toLinearMap,
    shared_map (shared_product hG hH) e, ?_, ?_⟩
  · rw [(entryEquiv e).finrank_map_eq, finrank_productCode]
  · exact subcode_bound_map (productCode G H) (finrank Bit G + L)
      (product_linear_subcode_bound G H L hL) e

variable {s : ℕ} [NeZero s]

/-- Every tripled partition admits an actual binary source with the stated
symmetric gap around half. A two-class partition is supplied below. -/
theorem symmetric_hard_mixture (hodd : Odd (3 * s)) (p : ZMod (3 * s) → κ)
    (hp : ∀ c, p (c + (s : ZMod (3 * s))) = p c) :
    ∃ B : ℕ, 0 < B ∧
      ∃ C : Submodule Bit (State (3 * s) (Fin B → Bit)), IsSharedCode Bit p C ∧
        (finrank Bit C : ℝ) =
          (1 / 2 + 1 / (8 * (3 * s) + 18 : ℝ)) * (B * (3 * s) * (3 * s)) ∧
        ∀ D ≤ C, IsLinearSharedCode p D →
          (finrank Bit D : ℝ) ≤
            (1 / 2 - 1 / (8 * (3 * s) + 18 : ℝ)) * (B * (3 * s) * (3 * s)) := by
  obtain ⟨ell, hell, hh⟩ := CapacityTriple.exists_width_stable_hard_source hodd p hp
  obtain ⟨H, hH, hHdim, hHlin⟩ := hh (9 * ell) (dvd_mul_left ell 9)
  let G : Submodule Bit (State (3 * s) (Fin (4 * (3 * s) * ell) → Bit)) := symmetricSpace
  have hGdim : 2 * finrank Bit G = (3 * s) * (3 * s + 1) * (4 * (3 * s) * ell) := by
    simpa [G, ZMod.card] using
      (two_mul_finrank_symmetricSpace (F := Bit) (A := Fin (4 * (3 * s) * ell) → Bit)
        (I := ZMod (3 * s)))
  have hL : ∀ D ≤ H, IsLinearSharedCode p D →
      finrank Bit D ≤ 2 * ell * (3 * s) * (3 * s) := by
    intro D hD hlin
    have hi := hHlin D hD hlin
    nlinarith
  obtain ⟨C, hC, hdim, hlin⟩ := combine_binary_codes G H (symmetric_shared p) hH _ hL
  refine ⟨4 * (3 * s) * ell + 9 * ell, by positivity, C, hC, ?_, ?_⟩
  · have hg : (2 : ℝ) * finrank Bit G =
        (3 * (s : ℝ)) * (3 * s + 1) * (4 * (3 * s) * ell) := by exact_mod_cast hGdim
    have hh : (3 : ℝ) * finrank Bit H = (9 * (ell : ℝ)) * (3 * s) * (3 * s) := by
      exact_mod_cast hHdim
    have hc : (finrank Bit C : ℝ) = finrank Bit G + finrank Bit H := by exact_mod_cast hdim
    push_cast
    field_simp
    nlinarith
  · intro D hD hdlin
    have hi : (finrank Bit D : ℝ) ≤ finrank Bit G + 2 * (ell : ℝ) * (3 * s) * (3 * s) := by
      exact_mod_cast hlin D hD hdlin
    have hg : (2 : ℝ) * finrank Bit G =
        (3 * (s : ℝ)) * (3 * s + 1) * (4 * (3 * s) * ell) := by exact_mod_cast hGdim
    push_cast
    have hden : (0 : ℝ) < 8 * (3 * s) + 18 := by positivity
    apply (le_of_eq_of_le ?_ hi).trans_eq ?_
    · rfl
    · field_simp
      nlinarith

/-- Exact rational mixing of any actual above-half good code with the hard
family. The result is about subcodes of this source, with no restriction on
how a candidate linear decoder mixes its lanes. -/
theorem good_hard_mixture (hodd : Odd (3 * s)) (p : ZMod (3 * s) → κ)
    (hp : ∀ c, p (c + (s : ZMod (3 * s))) = p c)
    {b k : ℕ} (hb : 0 < b) (hk : 0 < k)
    (G : Submodule Bit (State (3 * s) (Fin b → Bit)))
    (hG : IsSharedCode Bit p G)
    (hGdim : 2 * finrank Bit G = b * (3 * s) * (3 * s) + k) :
    ∃ B : ℕ, 0 < B ∧
      ∃ C : Submodule Bit (State (3 * s) (Fin B → Bit)), IsSharedCode Bit p C ∧
        (finrank Bit C : ℝ) =
          (1 / 2 + k / (8 * (b * (3 * s) * (3 * s)) + 18 * k : ℝ)) *
            (B * (3 * s) * (3 * s)) ∧
        ∀ D ≤ C, IsLinearSharedCode p D →
          (finrank Bit D : ℝ) ≤
            (1 / 2 - k / (8 * (b * (3 * s) * (3 * s)) + 18 * k : ℝ)) *
              (B * (3 * s) * (3 * s)) := by
  obtain ⟨ell, hell, hh⟩ := CapacityTriple.exists_width_stable_hard_source hodd p hp
  let V := b * (3 * s) * (3 * s)
  let g := 4 * V
  obtain ⟨G', hG', hG'dim⟩ := repeat_binary_code G hG (g * ell)
  have hdvd : ell ∣ 9 * k * ell * b := ⟨9 * k * b, by ring⟩
  obtain ⟨H, hH, hHdim, hHlin⟩ := hh (9 * k * ell * b) hdvd
  have hL : ∀ D ≤ H, IsLinearSharedCode p D →
      finrank Bit D ≤ 2 * k * ell * V := by
    intro D hD hlin
    have hi := hHlin D hD hlin
    dsimp [V]
    nlinarith
  obtain ⟨C, hC, hdim, hlin⟩ := combine_binary_codes G' H hG' hH _ hL
  have hgpos : 0 < g := by dsimp [g, V]; have := NeZero.pos s; positivity
  have hg : (2 : ℝ) * finrank Bit G = (b : ℝ) * (3 * s) * (3 * s) + k := by
    exact_mod_cast hGdim
  have hgp : (finrank Bit G' : ℝ) = (g : ℝ) * ell * finrank Bit G := by
    exact_mod_cast hG'dim
  have hh : (3 : ℝ) * finrank Bit H =
      (9 : ℝ) * k * ell * b * (3 * s) * (3 * s) := by exact_mod_cast hHdim
  have hc : (finrank Bit C : ℝ) = finrank Bit G' + finrank Bit H := by exact_mod_cast hdim
  have hgr : (finrank Bit G : ℝ) = ((b : ℝ) * (3 * s) * (3 * s) + k) / 2 := by linarith
  have hhr : (finrank Bit H : ℝ) = 3 * (k : ℝ) * ell * b * (3 * s) * (3 * s) := by linarith
  refine ⟨g * ell * b + 9 * k * ell * b, by positivity, C, hC, ?_, ?_⟩
  · rw [hc, hgp, hgr, hhr]
    dsimp [g, V]
    push_cast
    field_simp
    ring
  · intro D hD hdlin
    have hi : (finrank Bit D : ℝ) ≤ finrank Bit G' + 2 * (k : ℝ) * ell * V := by
      exact_mod_cast hlin D hD hdlin
    apply hi.trans_eq
    rw [hgp, hgr]
    dsimp [g, V]
    push_cast
    field_simp
    ring

omit [NeZero s] in
/-- Two genuinely nonempty classes, repeated at the three receivers of every
triple. No coprimality with three is needed for this partition. -/
theorem exists_two_class_tripled_partition (hs : 2 ≤ s) :
    ∃ p : ZMod (3 * s) → Bool, Function.Surjective p ∧
      ∀ c, p (c + (s : ZMod (3 * s))) = p c := by
  classical
  have : Fact (1 < s) := ⟨by omega⟩
  let r : ZMod (3 * s) →+* ZMod s := ZMod.castHom (dvd_mul_left s 3) (ZMod s)
  let p : ZMod (3 * s) → Bool := fun c => decide (r c = 0)
  refine ⟨p, ?_, ?_⟩
  · intro a
    cases a
    · exact ⟨1, by simp [p]⟩
    · exact ⟨0, by simp [p]⟩
  · intro c
    simp [p, map_add, map_natCast]

/-- The unconditional above-half barrier at every odd multiple of three of
size at least nine. Its positive excess tends to zero with the dimension. -/
theorem exists_above_half_barrier (hodd : Odd (3 * s)) (hs : 3 ≤ s) :
    ∃ p : ZMod (3 * s) → Bool, Function.Surjective p ∧
      ∃ B : ℕ, 0 < B ∧
        ∃ C : Submodule Bit (State (3 * s) (Fin B → Bit)), IsSharedCode Bit p C ∧
          (finrank Bit C : ℝ) =
            (1 / 2 + 1 / (8 * (3 * s) + 18 : ℝ)) * (B * (3 * s) * (3 * s)) ∧
          ∀ D ≤ C, IsLinearSharedCode p D →
            (finrank Bit D : ℝ) ≤
              (1 / 2 - 1 / (8 * (3 * s) + 18 : ℝ)) * (B * (3 * s) * (3 * s)) := by
  obtain ⟨p, hsurj, hp⟩ := exists_two_class_tripled_partition (by omega : 2 ≤ s)
  exact ⟨p, hsurj, symmetric_hard_mixture hodd p hp⟩

end SharedDecoders.CapacitySubcode
