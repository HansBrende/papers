import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Exact finite linear-hash collision counts and deterministic selections.
Hashes are actual linear maps; no independence or collision-probability premise
is assumed. The finite-field result specializes to uniform binary matrices. -/

namespace LeanMachine

open Module Classical
open scoped BigOperators

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

noncomputable local instance [Finite V] [Finite W] : Fintype (V →ₗ[F] W) := by
  have : Finite (V →ₗ[F] W) := Finite.of_injective
    (fun H : V →ₗ[F] W => (H : V → W)) DFunLike.coe_injective
  exact Fintype.ofFinite _

theorem linearHash_eval_surjective (v : V) (hv : v ≠ 0) :
    Function.Surjective (LinearMap.applyₗ (R := F) (M₂ := W) v) := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F hv
  intro w
  exact ⟨ℓ.smulRight w, by simp only [LinearMap.applyₗ_apply_apply,
    LinearMap.smulRight_apply, hℓ, one_smul]⟩

theorem linearHash_collision_finrank [FiniteDimensional F V] [FiniteDimensional F W]
    (v : V) (hv : v ≠ 0) :
    finrank F (LinearMap.applyₗ (R := F) (M₂ := W) v).ker =
      finrank F V * finrank F W - finrank F W := by
  have he := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.applyₗ (R := F) (M₂ := W) v)
  rw [LinearMap.range_eq_top.mpr (linearHash_eval_surjective v hv),
    finrank_top, finrank_linearMap] at he
  omega

theorem linearHash_collision_card [Finite F] [FiniteDimensional F V] [FiniteDimensional F W]
    (v : V) (hv : v ≠ 0) :
    Nat.card {H : V →ₗ[F] W // H v = 0} =
      Nat.card F ^ (finrank F V * finrank F W - finrank F W) := by
  change Nat.card (LinearMap.applyₗ (R := F) (M₂ := W) v).ker = _
  rw [Module.natCard_eq_pow_finrank (K := F), linearHash_collision_finrank (F := F) v hv]

/-- Exact denominator form, useful for union bounds without rational division. -/
theorem linearHash_collision_mul_card [Finite F] [FiniteDimensional F V] [FiniteDimensional F W]
    (v : V) (hv : v ≠ 0) :
    Nat.card {H : V →ₗ[F] W // H v = 0} * Nat.card W = Nat.card (V →ₗ[F] W) := by
  have he := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.applyₗ (R := F) (M₂ := W) v)
  rw [LinearMap.range_eq_top.mpr (linearHash_eval_surjective v hv), finrank_top] at he
  change Nat.card (LinearMap.applyₗ (R := F) (M₂ := W) v).ker * Nat.card W = _
  rw [Module.natCard_eq_pow_finrank (K := F)
    (V := (LinearMap.applyₗ (R := F) (M₂ := W) v).ker),
    Module.natCard_eq_pow_finrank (K := F) (V := W),
    Module.natCard_eq_pow_finrank (K := F) (V := V →ₗ[F] W), ← pow_add]
  rw [Nat.add_comm, he]

/-- The bad hashes are a union of the actual zero-evaluation fibres. -/
theorem linearHash_bad_card_le [Fintype F] [Fintype V] [Fintype W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (D : Finset V) (hD : ∀ v ∈ D, v ≠ 0) :
    (Finset.univ.filter (fun H : V →ₗ[F] W => ∃ v ∈ D, H v = 0)).card ≤
      D.card * Fintype.card F ^ (finrank F V * finrank F W - finrank F W) := by
  have he : Finset.univ.filter (fun H : V →ₗ[F] W => ∃ v ∈ D, H v = 0) =
      D.biUnion (fun v => Finset.univ.filter (fun H : V →ₗ[F] W => H v = 0)) := by
    ext H
    simp
  rw [he]
  calc
    _ ≤ ∑ v ∈ D, (Finset.univ.filter (fun H : V →ₗ[F] W => H v = 0)).card :=
      Finset.card_biUnion_le
    _ = ∑ _v ∈ D, Fintype.card F ^ (finrank F V * finrank F W - finrank F W) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hc := linearHash_collision_card (F := F) (W := W) v (hD v hv)
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
    _ = _ := by simp

/-- A single exhibited hash avoids every supplied nonzero difference whenever
the number of differences is smaller than the output alphabet. -/
theorem exists_linearHash_avoiding [Fintype F] [Fintype V] [Fintype W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (D : Finset V) (hD : ∀ v ∈ D, v ≠ 0) (hsize : D.card < Fintype.card W) :
    ∃ H : V →ₗ[F] W, ∀ v ∈ D, H v ≠ 0 := by
  by_cases hne : D.Nonempty
  · obtain ⟨v, hv⟩ := hne
    have hc := linearHash_collision_mul_card (F := F) (W := W) v (hD v hv)
    rw [linearHash_collision_card (F := F) v (hD v hv)] at hc
    simp only [Nat.card_eq_fintype_card] at hc
    have hp : 0 < Fintype.card F ^ (finrank F V * finrank F W - finrank F W) :=
      pow_pos Fintype.card_pos _
    have hb := linearHash_bad_card_le (F := F) (W := W) D hD
    by_contra hh
    have hall : ∀ H : V →ₗ[F] W, ∃ v ∈ D, H v = 0 := by
      simpa only [not_exists, not_forall, exists_prop, not_not] using hh
    have he : Finset.univ.filter (fun H : V →ₗ[F] W => ∃ v ∈ D, H v = 0) =
        Finset.univ := Finset.filter_eq_self.mpr (fun H _ => hall H)
    rw [he, Finset.card_univ, ← hc] at hb
    exact (Nat.mul_lt_mul_of_pos_right hsize hp).not_ge (by simpa only [Nat.mul_comm] using hb)
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩

/-- One hash works on a common large set of inputs. Each comparison family is
fixed before choosing the hash. If the output alphabet has at least `m * B`
values, at most a `1/m` fraction of the inputs need be discarded. -/
theorem exists_linearHash_few_bad {X : Type*}
    [Fintype F] [Fintype V] [Fintype W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (G : Finset X) (D : X → Finset V) (B m : ℕ)
    (hnonzero : ∀ x ∈ G, ∀ v ∈ D x, v ≠ 0)
    (hsize : ∀ x ∈ G, (D x).card ≤ B) (hbudget : m * B ≤ Fintype.card W) :
    ∃ H : V →ₗ[F] W, m * (G.filter (fun x => ∃ v ∈ D x, H v = 0)).card ≤ G.card := by
  by_cases hsome : ∃ x ∈ G, (D x).Nonempty
  · obtain ⟨x₀, hx₀, v, hv⟩ := hsome
    let K := Fintype.card F ^ (finrank F V * finrank F W - finrank F W)
    have hc : K * Fintype.card W = Fintype.card (V →ₗ[F] W) := by
      have hh := linearHash_collision_mul_card (F := F) (W := W) v (hnonzero x₀ hx₀ v hv)
      rw [linearHash_collision_card (F := F) v (hnonzero x₀ hx₀ v hv)] at hh
      simpa only [Nat.card_eq_fintype_card] using hh
    let bad (H : V →ₗ[F] W) := (G.filter (fun x => ∃ v ∈ D x, H v = 0)).card
    have hsum : ∑ H : V →ₗ[F] W, bad H ≤ G.card * (B * K) := by
      have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (Finset.univ : Finset (V →ₗ[F] W))) (t := G)
        (fun H x => ∃ v ∈ D x, H v = 0)
      change (∑ H : V →ₗ[F] W, bad H) =
        ∑ x ∈ G, (Finset.univ.filter (fun H : V →ₗ[F] W => ∃ v ∈ D x, H v = 0)).card at he
      rw [he]
      calc
        _ ≤ ∑ _x ∈ G, B * K := by
          apply Finset.sum_le_sum
          intro x hx
          exact (linearHash_bad_card_le (F := F) (W := W) (D x) (hnonzero x hx)).trans
            (Nat.mul_le_mul_right K (hsize x hx))
        _ = _ := by simp
    have hsum' : ∑ H : V →ₗ[F] W, m * bad H ≤
        Fintype.card (V →ₗ[F] W) * G.card := by
      rw [← Finset.mul_sum, ← hc]
      calc
        _ ≤ m * (G.card * (B * K)) := Nat.mul_le_mul_left m hsum
        _ = (m * B) * (K * G.card) := by ring
        _ ≤ Fintype.card W * (K * G.card) := Nat.mul_le_mul_right _ hbudget
        _ = _ := by ring
    by_contra hn
    have hall : ∀ H : V →ₗ[F] W, G.card < m * bad H := by
      simpa only [not_exists, not_le] using hn
    have hlt := Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty : (Finset.univ : Finset (V →ₗ[F] W)).Nonempty)
      (fun H (_ : H ∈ Finset.univ) => hall H)
    have hh : Fintype.card (V →ₗ[F] W) * G.card < ∑ H : V →ₗ[F] W, m * bad H := by
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using hlt
    exact hh.not_ge hsum'
  · refine ⟨0, ?_⟩
    have he : G.filter (fun x => ∃ v ∈ D x, (0 : V →ₗ[F] W) v = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxG, v, hv, _⟩ := Finset.mem_filter.mp hx
      exact hsome ⟨x, hxG, v, hv⟩
    rw [he, Finset.card_empty, mul_zero]
    exact Nat.zero_le _

theorem exists_linearHash_common_half {X : Type*}
    [Fintype F] [Fintype V] [Fintype W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (G : Finset X) (D : X → Finset V) (B : ℕ)
    (hnonzero : ∀ x ∈ G, ∀ v ∈ D x, v ≠ 0)
    (hsize : ∀ x ∈ G, (D x).card ≤ B) (hbudget : 2 * B ≤ Fintype.card W) :
    ∃ H : V →ₗ[F] W,
      G.card ≤ 2 * (G.filter (fun x => ∀ v ∈ D x, H v ≠ 0)).card := by
  obtain ⟨H, hH⟩ := exists_linearHash_few_bad (F := F) G D B 2 hnonzero hsize hbudget
  refine ⟨H, ?_⟩
  have he := Finset.card_filter_add_card_filter_not
    (s := G) (p := fun x => ∃ v ∈ D x, H v = 0)
  simp only [not_exists, not_and] at he
  change (G.filter (fun x => ∃ v ∈ D x, H v = 0)).card +
    (G.filter (fun x => ∀ v ∈ D x, H v ≠ 0)).card = G.card at he
  omega

/-- A common subset interface avoids exposing the implementation of the good
input filter to applications with concrete, large finite alphabets. -/
theorem exists_linearHash_common_subset {X : Type*}
    [Fintype F] [Fintype V] [Fintype W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (G : Finset X) (D : X → Finset V) (B : ℕ)
    (hnonzero : ∀ x ∈ G, ∀ v ∈ D x, v ≠ 0)
    (hsize : ∀ x ∈ G, (D x).card ≤ B) (hbudget : 2 * B ≤ Fintype.card W) :
    ∃ (H : V →ₗ[F] W) (G' : Finset X), G' ⊆ G ∧ G.card ≤ 2 * G'.card ∧
      ∀ x ∈ G', ∀ v ∈ D x, H v ≠ 0 := by
  obtain ⟨H, hH⟩ := exists_linearHash_common_half (F := F) G D B hnonzero hsize hbudget
  refine ⟨H, G.filter (fun x => ∀ v ∈ D x, H v ≠ 0), Finset.filter_subset _ _, hH, ?_⟩
  exact fun _ hx => (Finset.mem_filter.mp hx).2

/-- Replacing one symbol updates its actual syndrome by one embedded local
difference, independently of how dense the rest of the word is. -/
theorem linearHash_update {I : Type*} [DecidableEq I]
    (H : (I → V) →ₗ[F] W) (x : I → V) (i : I) (v : V) :
    H (Function.update x i v) = H x + H (Pi.single i (v - x i)) := by
  have he : Function.update x i v = x + Pi.single i (v - x i) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
      abel
    · simp [h]
  rw [he, map_add]

end LeanMachine
