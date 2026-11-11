import AdaptiveTransfer.PersistenceGraph
import LeanMachine.FiniteObservationTopSets
import LeanMachine.FiniteTimeGrid

/-! Literal time/prefix catalogues formed by thickening the actual conditional
top sets. Historical output prefixes are enumerated using the append-time law,
not supplied as freely chosen catalogue indices. -/

namespace AdaptiveTransfer.PersistenceCatalogues

open Transpose Transpose.Tape Transpose.Tape.Impl LeanMachine Finset
open FiniteTapeGraph PersistenceGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem historical_prefix (emit : ℕ → Option Bool) {u t : ℕ} (hut : u ≤ t) :
    let loss := (PrefixOutput.word emit t).length - (PrefixOutput.word emit u).length
    loss ≤ t - u ∧
      (PrefixOutput.word emit t).take ((PrefixOutput.word emit t).length - loss) =
        PrefixOutput.word emit u := by
  have he := PrefixOutput.word_add emit u (t - u)
  rw [Nat.add_sub_of_le hut] at he
  have hlen := List.length_filterMap_le (fun i => emit (u + i)) (List.range (t - u))
  simp only [List.length_range] at hlen
  have hm := PrefixOutput.length_mono emit hut
  change (PrefixOutput.word emit u).length ≤ (PrefixOutput.word emit t).length at hm
  dsimp only
  constructor
  · rw [he, List.length_append]
    omega
  · have hc : (PrefixOutput.word emit t).length -
        ((PrefixOutput.word emit t).length - (PrefixOutput.word emit u).length) =
        (PrefixOutput.word emit u).length := by omega
    rw [hc, he, List.take_left]

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {n : ℕ}

noncomputable def thicken (S : Finset (Vertex A n)) (R : ℕ) : Finset (Vertex A n) :=
  S.biUnion fun v => GraphBall.closedBall (graph A n) v R

theorem card_thicken_le (S : Finset (Vertex A n)) (R : ℕ) :
    (thicken S R).card ≤ S.card * (6 * Fintype.card A) ^ (R + 1) := by
  calc
    _ ≤ ∑ v ∈ S, (GraphBall.closedBall (graph A n) v R).card := card_biUnion_le
    _ ≤ ∑ _v ∈ S, (6 * Fintype.card A) ^ (R + 1) :=
      sum_le_sum fun v _ => card_ball_le v R
    _ = _ := by simp

noncomputable def catalogue (menu : ℕ → List Bool → Finset (Vertex A n))
    (t R : ℕ) (y : List Bool) : Finset (Vertex A n) :=
  (range (R + 1)).biUnion fun lag => (range (R + 1)).biUnion fun loss =>
    thicken (menu (t - lag) (y.take (y.length - loss))) R

theorem card_catalogue_le (menu : ℕ → List Bool → Finset (Vertex A n))
    (K : ℕ) (hK : ∀ u z, (menu u z).card ≤ K) (t R : ℕ) (y : List Bool) :
    (catalogue menu t R y).card ≤ (R + 1) ^ 2 * K * (6 * Fintype.card A) ^ (R + 1) := by
  calc
    _ ≤ ∑ lag ∈ range (R + 1),
        ((range (R + 1)).biUnion fun loss =>
          thicken (menu (t - lag) (y.take (y.length - loss))) R).card := card_biUnion_le
    _ ≤ ∑ lag ∈ range (R + 1), ∑ loss ∈ range (R + 1),
        (thicken (menu (t - lag) (y.take (y.length - loss))) R).card :=
      sum_le_sum fun _ _ => card_biUnion_le
    _ ≤ ∑ _lag ∈ range (R + 1), ∑ _loss ∈ range (R + 1),
        K * (6 * Fintype.card A) ^ (R + 1) := by
      apply sum_le_sum
      intro lag _
      apply sum_le_sum
      intro loss _
      exact (card_thicken_le _ _).trans (Nat.mul_le_mul_right _ (hK _ _))
    _ = _ := by simp [pow_two, Nat.mul_assoc]

variable {Ω : Type*} [Fintype Ω]

noncomputable def nativeTop (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (T K : ℕ) (h : Fin M.k) (u : ℕ) (z : List Bool) :
    Finset (Vertex (Fin (M.g + 1)) (2 * T + 1)) :=
  FiniteObservationTopSets.top w (fun x => PrefixOutput.word (outBit M (input x)) u)
    (fun x => vertex M (input x) T u h) z K

theorem nativeTop_card (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (T K : ℕ) (h : Fin M.k) (u : ℕ) (z : List Bool) :
    (nativeTop M input w T K h u z).card ≤ K :=
  FiniteObservationTopSets.card_top_le _ _ _ _ _

theorem native_catalogue_card (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (T K R t : ℕ) (h : Fin M.k) (y : List Bool) :
    (catalogue (nativeTop M input w T K h) t R y).card ≤
      (R + 1) ^ 2 * K * (6 * (M.g + 1)) ^ (R + 1) := by
  simpa using card_catalogue_le (nativeTop M input w T K h) K
    (nativeTop_card M input w T K h) t R y

/-- Escape at the witness implies avoidance of the actual conditional top
sets at every historical time in the preceding radius. -/
theorem native_escape_history (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (T K R : ℕ) (h : Fin M.k) (x : Ω) {u t : ℕ}
    (hut : u ≤ t) (ht : t ≤ T) (hR : t - u ≤ R)
    (hescape : vertex M (input x) T t h ∉
      catalogue (nativeTop M input w T K h) t R (PrefixOutput.word (outBit M (input x)) t)) :
    vertex M (input x) T u h ∉ nativeTop M input w T K h u
      (PrefixOutput.word (outBit M (input x)) u) := by
  intro htop
  apply hescape
  obtain ⟨hloss, hprefix⟩ := historical_prefix (outBit M (input x)) hut
  apply mem_biUnion.mpr
  refine ⟨t - u, mem_range.mpr (by omega), ?_⟩
  apply mem_biUnion.mpr
  refine ⟨(PrefixOutput.word (outBit M (input x)) t).length -
    (PrefixOutput.word (outBit M (input x)) u).length, mem_range.mpr (by omega), ?_⟩
  rw [Nat.sub_sub_self hut, hprefix]
  exact mem_biUnion.mpr ⟨vertex M (input x) T u h, htop, native_ball M (input x) T h hut ht hR⟩

theorem initial_top (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (hprob : ∑ x, w x = 1) (T K : ℕ) (hK : 1 ≤ K) (h : Fin M.k) (x : Ω) :
    vertex M (input x) T 0 h ∈ nativeTop M input w T K h 0 [] := by
  let v₀ := vertex M [] T 0 h
  have hv (x : Ω) : vertex M (input x) T 0 h = v₀ := rfl
  have hatom : FiniteObservationTopSets.atom w
      (fun x => PrefixOutput.word (outBit M (input x)) 0)
      (fun x => vertex M (input x) T 0 h) [] = fun v => if v = v₀ then 1 else 0 := by
    funext v
    unfold FiniteObservationTopSets.atom
    simp only [PrefixOutput.word_zero, hv, true_and]
    by_cases he : v = v₀ <;> simp [he, eq_comm, hprob]
  change vertex M (input x) T 0 h ∈ FiniteTopSets.top _ K
  rw [hatom, hv]
  exact FiniteTopSets.top_contains_constant v₀ 1 (by norm_num) hK

theorem escape_after_radius (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (hprob : ∑ x, w x = 1) (T K R : ℕ) (hK : 1 ≤ K) (h : Fin M.k) (x : Ω)
    {t : ℕ} (ht : t ≤ T)
    (hescape : vertex M (input x) T t h ∉
      catalogue (nativeTop M input w T K h) t R (PrefixOutput.word (outBit M (input x)) t)) :
    R < t := by
  by_contra hn
  have ha := native_escape_history M input w T K R h x (Nat.zero_le t) ht (by omega) hescape
  exact ha (initial_top M input w hprob T K hK h x)

/-- The concrete grid interval is live even if the escaping configuration is
the halting configuration itself. -/
theorem native_escape_grid (M : TM) (input : Ω → List Bool) (w : Ω → ℝ)
    (hprob : ∑ x, w x = 1) (T K R : ℕ) (hK : 1 ≤ K) (hR : 2 ≤ R)
    (h : Fin M.k) (x : Ω) {t : ℕ} (ht : t ≤ T)
    (hescape : vertex M (input x) T t h ∉
      catalogue (nativeTop M input w T K h) t R (PrefixOutput.word (outBit M (input x)) t)) :
    ∀ u ∈ FiniteTimeGrid.interval (R / 2) (FiniteTimeGrid.previousIndex (R / 2) t),
      u < t ∧ vertex M (input x) T u h ∉ nativeTop M input w T K h u
        (PrefixOutput.word (outBit M (input x)) u) := by
  have hafter := escape_after_radius M input w hprob T K R hK h x ht hescape
  have hg := (FiniteTimeGrid.half_radius_interval hR hafter).2
  intro u hu
  obtain ⟨hlo, hhi⟩ := hg u hu
  exact ⟨hhi, native_escape_history M input w T K R h x hhi.le ht (by omega) hescape⟩

end AdaptiveTransfer.PersistenceCatalogues
