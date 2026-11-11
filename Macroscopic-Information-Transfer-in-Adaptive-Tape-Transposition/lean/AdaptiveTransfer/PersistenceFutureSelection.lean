import AdaptiveTransfer.PersistenceFutureCatalogues
import LeanMachine.FiniteIntervalSelection

/-! One common event and interval from literal future-word catalogue escape.
The original law determines the unconditioned top sets. Every input uses its
own actual halting horizon; no probability, recovery, or movement certificate
replaces the native observations. The source catalogue theorem is a separate
dependency that must supply the literal escape event.
-/

namespace AdaptiveTransfer.PersistenceFutureSelection

open Transpose Transpose.Tape LeanMachine Finset BoundedNesting
open PersistenceFutureCatalogues FiniteTimeGrid FiniteObservationTopSets
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

theorem exists_fixed_escape_interval (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : ∑ x, w x = 1)
    (T K R m : ℕ) (hK : 1 ≤ K) (hR : 2 ≤ R)
    (B : Finset Ω) (hp : 0 < ContextPruning.mass w B)
    (hτ : ∀ x ∈ B, τ x ≤ T)
    (hescape : ∀ x ∈ B, ∃ t ≤ τ x, ∃ H : Finset (Fin M.k), H.card = m ∧
      ∀ h ∈ H, PersistenceFuture.word M (input x) (τ x) t h ∉
        wordCatalogue M input τ w T K R t h) :
    ∃ H : Finset (Fin M.k), H.card = m ∧ ∃ j < T / (R / 2) + 1,
      ∃ E ⊆ B,
        ContextPruning.mass w B / (M.k.choose m * (T / (R / 2) + 1) : ℕ) ≤
          ContextPruning.mass w E ∧
        ∀ x ∈ E, ∀ h ∈ H, ∀ u ∈ interval (R / 2) j,
          u < τ x ∧ PersistenceFutureWindow.vertex M (input x) (τ x) T u h ∉
            nativeTop M input τ w T K h u := by
  apply FiniteIntervalSelection.exists_fixed_interval w hw B hp M.k m T (R / 2)
    (fun x h u => u < τ x ∧ PersistenceFutureWindow.vertex M (input x) (τ x) T u h ∉
      nativeTop M input τ w T K h u)
  intro x hx
  obtain ⟨t, ht, H, hH, hout⟩ := hescape x hx
  refine ⟨t, ht.trans (hτ x hx), H, hH, ?_⟩
  intro h hh u hu
  have hg := native_escape_grid M input τ w hprob T K R hK hR h x
    (ht.trans (hτ x hx)) (hout h hh) u hu
  exact ⟨hg.1.trans_le ht, hg.2⟩

private theorem restricted_atom_congr {W : Type*} (w : Ω → ℝ) (E : Finset Ω)
    (f g : Ω → W) (hfg : ∀ x ∈ E, f x = g x) (v : W) :
    atom (fun x => if x ∈ E then w x else 0) (fun _ => ()) f () v =
      atom (fun x => if x ∈ E then w x else 0) (fun _ => ()) g () v := by
  unfold atom
  apply sum_congr rfl
  intro x _
  by_cases hx : x ∈ E
  · simp only [hx, ite_true, hfg x hx]
  · simp only [hx, ite_false, ite_self]

private theorem marginal_atom_bound {V W : Type*} [Fintype V] [DecidableEq V]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : ∑ x, w x = 1)
    (f : Ω → V) (g : V → W) (actual : Ω → W) (E : Finset Ω)
    (heq : ∀ x ∈ E, actual x = g (f x))
    (K n L : ℕ) (p : ℝ) (hp : 0 < p) (hL : 0 < L)
    (hmass : p / L ≤ ContextPruning.mass w E)
    (havoid : ∀ x ∈ E, f x ∉ top w (fun _ => ()) f () K)
    (v : W) (hfib : (univ.filter fun y => g y = v).card ≤ n) :
    atom (fun x => if x ∈ E then w x else 0) (fun _ => ()) actual () v /
      ContextPruning.mass w E ≤ (n : ℝ) * L / ((K + 1) * p) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hEp : 0 < ContextPruning.mass w E := (div_pos hp hLr).trans_le hmass
  have henv := coarsened_avoid_top w hw (fun _ => ()) f g E () v K n hfib
    (fun x hx _ => havoid x hx)
  have hcontext : context w (fun _ => ()) () = 1 := by simpa only [context, ite_true] using hprob
  rw [hcontext, mul_one, ← restricted_atom_congr w E actual (g ∘ f) heq v] at henv
  have hm := (div_le_iff₀ hLr).mp hmass
  calc
    _ ≤ ((n : ℝ) / (K + 1)) / ContextPruning.mass w E :=
      div_le_div_of_nonneg_right henv hEp.le
    _ = (n : ℝ) / ((K + 1) * ContextPruning.mass w E) := by rw [div_div]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ (n : ℝ) * (K + 1) by positivity)
      convert hm' using 1 <;> ring

/-- Literal escape gives one event for every selected time, every selected
tape, and every head-mask radius. Marginal atoms of both whole future words
and whole remote words are derived from the actual finite fibres. -/
theorem exists_common_interval_atoms (M : TM) (input : Ω → List Bool) (τ : Ω → ℕ)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : ∑ x, w x = 1)
    (T K R m : ℕ) (hK : 1 ≤ K) (hR : 2 ≤ R)
    (B : Finset Ω) (hp : 0 < ContextPruning.mass w B)
    (hτ : ∀ x ∈ B, τ x ≤ T) (hhalt : ∀ x ∈ B, HaltsAt M (input x) (τ x))
    (hescape : ∀ x ∈ B, ∃ t ≤ τ x, ∃ H : Finset (Fin M.k), H.card = m ∧
      ∀ h ∈ H, PersistenceFuture.word M (input x) (τ x) t h ∉
        wordCatalogue M input τ w T K R t h) :
    ∃ H : Finset (Fin M.k), H.card = m ∧ ∃ j < T / (R / 2) + 1,
      ∃ E ⊆ B,
        ContextPruning.mass w B / (M.k.choose m * (T / (R / 2) + 1) : ℕ) ≤
          ContextPruning.mass w E ∧
        (∀ x ∈ E, ∀ h ∈ H, ∀ u ∈ interval (R / 2) j, u < τ x) ∧
        (∀ h ∈ H, ∀ u ∈ interval (R / 2) j, ∀ v,
          atom (fun x => if x ∈ E then w x else 0) (fun _ => ())
              (fun x => PersistenceFuture.word M (input x) (τ x) u h) () v /
            ContextPruning.mass w E ≤
              (2 * T + 1 : ℕ) * (M.k.choose m * (T / (R / 2) + 1) : ℕ) /
                ((K + 1) * ContextPruning.mass w B)) ∧
        (∀ Hmask : ℕ, ∀ h ∈ H, ∀ u ∈ interval (R / 2) j, ∀ v,
          atom (fun x => if x ∈ E then w x else 0) (fun _ => ())
              (fun x => PersistenceFutureWindow.remoteWord M (input x) (τ x) T u Hmask h) () v /
            ContextPruning.mass w E ≤
              ((2 * T + 1) * (M.g + 1) ^ (2 * Hmask + 1) : ℕ) *
                (M.k.choose m * (T / (R / 2) + 1) : ℕ) / ((K + 1) * ContextPruning.mass w B)) ∧
        ∀ Hmask : ℕ, ∀ x ∈ E, ∀ h ∈ H, ∀ u ∈ interval (R / 2) j, ∀ z,
          PersistenceFutureWindow.remoteWord M (input x) (τ x) T u Hmask h z ≠ 0 →
          ∃ p q, p < u ∧ u < q ∧ IsHop (fun s => (run M (input x) s).workPos h) (τ x) p q ∧
            transAt M (input x) p ≠ none ∧ transAt M (input x) q ≠ none ∧
            (run M (input x) p).workPos h = z ∧
            (Hmask : ℤ) < |(run M (input x) u).workPos h - (run M (input x) p).workPos h| := by
  classical
  obtain ⟨H, hH, j, hj, E, hEB, hmass, havoid⟩ :=
    exists_fixed_escape_interval M input τ w hw hprob T K R m hK hR B hp hτ hescape
  let L := M.k.choose m * (T / (R / 2) + 1)
  have hmk : m ≤ M.k := by simpa only [hH, Fintype.card_fin] using card_le_univ H
  have hL : 0 < L := Nat.mul_pos (Nat.choose_pos hmk) (Nat.succ_pos _)
  refine ⟨H, hH, j, hj, E, hEB, hmass, ?_, ?_, ?_, ?_⟩
  · exact fun x hx h hh u hu => (havoid x hx h hh u hu).1
  · intro h hh u hu v
    apply marginal_atom_bound w hw hprob
      (fun x => PersistenceFutureWindow.vertex M (input x) (τ x) T u h)
      (fun y => PersistenceGraph.extendWord 0 T y.1)
      (fun x => PersistenceFuture.word M (input x) (τ x) u h) E
      (fun x hx => (PersistenceFutureWindow.extendWord_vertex M (input x) (τ x) T u h
        ((havoid x hx h hh u hu).1.le.trans (hτ x (hEB hx)))).symm)
      K (2 * T + 1) L (ContextPruning.mass w B) hp hL hmass
      (fun x hx => (havoid x hx h hh u hu).2) v
    exact PersistenceGraph.whole_word_fibre 0 T v
  · intro Hmask h hh u hu v
    apply marginal_atom_bound w hw hprob
      (fun x => PersistenceFutureWindow.vertex M (input x) (τ x) T u h)
      (fun y => PersistenceGraph.extendWord 0 T
        (FiniteMaskFibres.maskedVertex 0 (FiniteMaskFibres.headWindow Hmask) y))
      (fun x => PersistenceFutureWindow.remoteWord M (input x) (τ x) T u Hmask h) E
      (fun _ _ => rfl) K ((2 * T + 1) * (M.g + 1) ^ (2 * Hmask + 1)) L
      (ContextPruning.mass w B) hp hL hmass
      (fun x hx => (havoid x hx h hh u hu).2) v
    exact PersistenceFutureWindow.remote_word_fibre M T Hmask v
  · intro Hmask x hx h hh u hu z hz
    exact PersistenceFutureWindow.remoteWord_successful_return M (input x) (τ x) T u Hmask
      (hhalt x (hEB hx)) h ((havoid x hx h hh u hu).1.le.trans (hτ x (hEB hx))) z hz

end AdaptiveTransfer.PersistenceFutureSelection
