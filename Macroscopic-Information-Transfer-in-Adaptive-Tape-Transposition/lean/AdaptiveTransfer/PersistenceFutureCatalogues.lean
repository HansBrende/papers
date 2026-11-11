import AdaptiveTransfer.PersistenceFutureWindow
import AdaptiveTransfer.PersistenceCatalogues

/-! Symmetric time catalogues of actual future-readable words. Every input
uses its own future horizon, while top sets and graph balls live in one
common finite observation window. The public catalogue is explicitly the
whole-word image of those vertices.
-/

namespace AdaptiveTransfer.PersistenceFutureCatalogues

open Transpose Transpose.Tape LeanMachine Finset
open FiniteTapeGraph PersistenceGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {n : ℕ}

noncomputable def catalogue (menu : ℕ → Finset (Vertex A n)) (t R : ℕ) : Finset (Vertex A n) :=
  (Icc (t - R) (t + R)).biUnion fun u => PersistenceCatalogues.thicken (menu u) R

theorem card_catalogue_le (menu : ℕ → Finset (Vertex A n)) (K : ℕ)
    (hK : ∀ u, (menu u).card ≤ K) (t R : ℕ) :
    (catalogue menu t R).card ≤ (2 * R + 1) * K * (6 * Fintype.card A) ^ (R + 1) := by
  have htimes : (Icc (t - R) (t + R)).card ≤ 2 * R + 1 := by simp; omega
  calc
    _ ≤ ∑ u ∈ Icc (t - R) (t + R), (PersistenceCatalogues.thicken (menu u) R).card :=
      card_biUnion_le
    _ ≤ ∑ _u ∈ Icc (t - R) (t + R), K * (6 * Fintype.card A) ^ (R + 1) :=
      sum_le_sum fun u _ => (PersistenceCatalogues.card_thicken_le (menu u) R).trans
        (Nat.mul_le_mul_right _ (hK u))
    _ = (Icc (t - R) (t + R)).card * (K * (6 * Fintype.card A) ^ (R + 1)) := by simp
    _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (K * (6 * Fintype.card A) ^ (R + 1)) htimes

variable {Ω : Type*} [Fintype Ω]

noncomputable def nativeTop (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (T K : ℕ) (h : Fin M.k) (u : ℕ) :
    Finset (Vertex (Fin (M.g + 1)) (2 * T + 1)) :=
  FiniteObservationTopSets.top w (fun _ => ())
    (fun x => PersistenceFutureWindow.vertex M (input x) (τ x) T u h) () K

theorem nativeTop_card (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (T K : ℕ) (h : Fin M.k) (u : ℕ) : (nativeTop M input τ w T K h u).card ≤ K :=
  FiniteObservationTopSets.card_top_le _ _ _ _ _

theorem native_catalogue_card (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (T K R t : ℕ) (h : Fin M.k) :
    (catalogue (nativeTop M input τ w T K h) t R).card ≤
      (2 * R + 1) * K * (6 * (M.g + 1)) ^ (R + 1) := by
  simpa only [Fintype.card_fin] using card_catalogue_le (nativeTop M input τ w T K h) K
    (nativeTop_card M input τ w T K h) t R

noncomputable def wordCatalogue (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (T K R t : ℕ) (h : Fin M.k) : Finset (ℤ → Fin (M.g + 1)) :=
  (catalogue (nativeTop M input τ w T K h) t R).image
    (fun v => PersistenceGraph.extendWord 0 T v.1)

theorem word_catalogue_card (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (T K R t : ℕ) (h : Fin M.k) :
    (wordCatalogue M input τ w T K R t h).card ≤
      (2 * R + 1) * K * (6 * (M.g + 1)) ^ (R + 1) :=
  card_image_le.trans (native_catalogue_card M input τ w T K R t h)

theorem native_escape_history (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (T K R : ℕ) (h : Fin M.k) (x : Ω) {u t : ℕ}
    (hut : u ≤ t) (ht : t ≤ T) (hR : t - u ≤ R)
    (hescape : PersistenceFutureWindow.vertex M (input x) (τ x) T t h ∉
      catalogue (nativeTop M input τ w T K h) t R) :
    PersistenceFutureWindow.vertex M (input x) (τ x) T u h ∉ nativeTop M input τ w T K h u := by
  intro htop
  apply hescape
  apply mem_biUnion.mpr
  refine ⟨u, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  exact mem_biUnion.mpr ⟨PersistenceFutureWindow.vertex M (input x) (τ x) T u h, htop,
    PersistenceFutureWindow.native_ball M (input x) (τ x) T h hut ht hR⟩

theorem initial_top (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (hprob : ∑ x, w x = 1) (T K : ℕ) (hK : 1 ≤ K) (h : Fin M.k) (x : Ω) :
    PersistenceFutureWindow.vertex M (input x) (τ x) T 0 h ∈ nativeTop M input τ w T K h 0 := by
  let v₀ := PersistenceGraph.vertex M [] T 0 h
  have hv (x : Ω) : PersistenceFutureWindow.vertex M (input x) (τ x) T 0 h = v₀ :=
    PersistenceFutureWindow.vertex_initial M (input x) (τ x) T h
  have hatom : FiniteObservationTopSets.atom w (fun _ => ())
      (fun x => PersistenceFutureWindow.vertex M (input x) (τ x) T 0 h) () =
      fun v => if v = v₀ then 1 else 0 := by
    funext v
    unfold FiniteObservationTopSets.atom
    simp only [hv, true_and]
    by_cases he : v = v₀ <;> simp [he, eq_comm, hprob]
  change PersistenceFutureWindow.vertex M (input x) (τ x) T 0 h ∈ FiniteTopSets.top _ K
  rw [hatom, hv]
  exact FiniteTopSets.top_contains_constant v₀ 1 (by norm_num) hK

theorem escape_after_radius (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (hprob : ∑ x, w x = 1) (T K R : ℕ) (hK : 1 ≤ K) (h : Fin M.k) (x : Ω)
    {t : ℕ} (ht : t ≤ T)
    (hescape : PersistenceFutureWindow.vertex M (input x) (τ x) T t h ∉
      catalogue (nativeTop M input τ w T K h) t R) : R < t := by
  by_contra hn
  have ha := native_escape_history M input τ w T K R h x (Nat.zero_le t) ht (by omega) hescape
  exact ha (initial_top M input τ w hprob T K hK h x)

theorem native_escape_grid (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ) (w : Ω → ℝ)
    (hprob : ∑ x, w x = 1) (T K R : ℕ) (hK : 1 ≤ K) (hR : 2 ≤ R)
    (h : Fin M.k) (x : Ω) {t : ℕ} (ht : t ≤ T)
    (hescape : PersistenceFuture.word M (input x) (τ x) t h ∉ wordCatalogue M input τ w T K R t h) :
    ∀ u ∈ FiniteTimeGrid.interval (R / 2) (FiniteTimeGrid.previousIndex (R / 2) t),
      u < t ∧ PersistenceFutureWindow.vertex M (input x) (τ x) T u h ∉
        nativeTop M input τ w T K h u := by
  have hv : PersistenceFutureWindow.vertex M (input x) (τ x) T t h ∉
      catalogue (nativeTop M input τ w T K h) t R := by
    intro hin
    apply hescape
    exact mem_image.mpr ⟨_, hin, PersistenceFutureWindow.extendWord_vertex M (input x) (τ x) T t h ht⟩
  have hafter := escape_after_radius M input τ w hprob T K R hK h x ht hv
  have hg := (FiniteTimeGrid.half_radius_interval hR hafter).2
  intro u hu
  obtain ⟨hlo, hhi⟩ := hg u hu
  exact ⟨hhi, native_escape_history M input τ w T K R h x hhi.le ht (by omega) hv⟩

end AdaptiveTransfer.PersistenceFutureCatalogues
