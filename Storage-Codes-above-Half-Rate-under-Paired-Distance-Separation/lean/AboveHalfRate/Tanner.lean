import AboveHalfRate.Peeling
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tanner codes and local checks

A *local datum* on a graph `G` assigns to every vertex `w` a local code `C w`: a space of functions on
the edges, of which only the values on the edges at `w` matter. A *Tanner word* is a function on the edges whose
restriction to the edges at every vertex is a local word; it may have infinite support. The *local
checks* at `w` are the finitely supported functions on the edges at `w` orthogonal to `C w`.

* `pairing_eq_zero_of_mem_iSup`: every finite sum of local checks is orthogonal to every Tanner
  word. This is how a check built on a tree is valid for the Tanner codes of its quotients.
* `interpolates_of_minWeight`: if every nonzero local word has more than `t` nonzero coordinates
  (for instance, an MDS local code of redundancy `t`), the local checks interpolate on `t`
  coordinates, as the peeling lemma requires.
-/

namespace AboveHalf

open Finset

set_option autoImplicit false

variable {W : Type*} [DecidableEq W] (G : SimpleGraph W) [G.LocallyFinite]
variable {𝔽 : Type*} [Field 𝔽]

/-- The pairing of a finitely supported function with an arbitrary function on the edges. -/
noncomputable def pairing (h : Sym2 W →₀ 𝔽) (c : Sym2 W → 𝔽) : 𝔽 :=
  h.sum fun e a => a * c e

omit [DecidableEq W] in
theorem pairing_add (h₁ h₂ : Sym2 W →₀ 𝔽) (c : Sym2 W → 𝔽) :
    pairing (h₁ + h₂) c = pairing h₁ c + pairing h₂ c := by
  unfold pairing
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

omit [DecidableEq W] in
theorem pairing_zero (c : Sym2 W → 𝔽) : pairing (0 : Sym2 W →₀ 𝔽) c = 0 := by
  simp [pairing]

/-- The local checks at `w`: finitely supported functions on the edges at `w` that are orthogonal
to every word of the local code at `w`. -/
def localChecks (C : W → Submodule 𝔽 (Sym2 W → 𝔽)) (w : W) : Submodule 𝔽 (Sym2 W →₀ 𝔽) where
  carrier := {g | (∀ e ∈ g.support, e ∈ star G w) ∧ ∀ c ∈ C w, ∑ e ∈ star G w, g e * c e = 0}
  add_mem' := by
    intro g₁ g₂ h₁ h₂
    refine ⟨fun e he => ?_, fun c hc => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add he) with h | h
      · exact h₁.1 e h
      · exact h₂.1 e h
    · simp only [Finsupp.add_apply, add_mul, Finset.sum_add_distrib, h₁.2 c hc, h₂.2 c hc,
        add_zero]
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    intro a g hg
    refine ⟨fun e he => hg.1 e (Finsupp.support_smul he), fun c hc => ?_⟩
    simp only [Finsupp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hg.2 c hc, mul_zero]

/-- A Tanner word: its restriction to the edges at each vertex is a word of the local code. -/
def IsTannerWord (C : W → Submodule 𝔽 (Sym2 W → 𝔽)) (c : Sym2 W → 𝔽) : Prop :=
  ∀ w, (fun e => if e ∈ star G w then c e else 0) ∈ C w

/-- A local check is orthogonal to every Tanner word. -/
theorem pairing_localCheck {C : W → Submodule 𝔽 (Sym2 W → 𝔽)} {w : W} {g : Sym2 W →₀ 𝔽}
    (hg : g ∈ localChecks G C w) {c : Sym2 W → 𝔽} (hc : IsTannerWord G C c) :
    pairing g c = 0 := by
  classical
  have hsub : g.support ⊆ star G w := fun e he => hg.1 e he
  have h0 := hg.2 _ (hc w)
  unfold pairing
  rw [Finsupp.sum, Finset.sum_subset hsub]
  · rw [← h0]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [ite_eq_left he]
  · intro e _ he
    rw [Finsupp.notMem_support_iff.1 he, zero_mul]

/-- **Validity of checks.** Every element of a span of local checks is orthogonal to every Tanner
word, whatever its support. -/
theorem pairing_eq_zero_of_mem_iSup {C : W → Submodule 𝔽 (Sym2 W → 𝔽)} {ι : Sort*}
    (φ : ι → W) {h : Sym2 W →₀ 𝔽} (hh : h ∈ ⨆ i, localChecks G C (φ i))
    {c : Sym2 W → 𝔽} (hc : IsTannerWord G C c) : pairing h c = 0 := by
  refine Submodule.iSup_induction (fun i => localChecks G C (φ i))
    (motive := fun h => pairing h c = 0) hh ?_ ?_ ?_
  · exact fun i g hg => pairing_localCheck G hg hc
  · exact pairing_zero c
  · intro g₁ g₂ h₁ h₂
    rw [pairing_add, h₁, h₂, add_zero]

/-- The checks produced by peeling (in `downChecks`) are orthogonal to every Tanner word. -/
theorem pairing_eq_zero_of_mem_downChecks {C : W → Submodule 𝔽 (Sym2 W → 𝔽)}
    {A : Sym2 W → Prop} {r : W → ℕ} {u : W} {h : Sym2 W →₀ 𝔽}
    (hh : h ∈ downChecks G (localChecks G C) A r u) {c : Sym2 W → 𝔽} (hc : IsTannerWord G C c) :
    pairing h c = 0 :=
  pairing_eq_zero_of_mem_iSup G (fun w : Down G A r u => w.1) hh hc

/-- **MDS local codes give interpolating local checks.** Suppose every nonzero word of each local
code has more than `t` nonzero coordinates among the edges at its vertex. Then the local checks
interpolate on `t` coordinates. -/
theorem interpolates_of_minWeight [DecidableEq 𝔽] (C : W → Submodule 𝔽 (Sym2 W → 𝔽)) (t : ℕ)
    (hwt : ∀ w, ∀ c ∈ C w, c ≠ 0 → t < ((star G w).filter (fun e => c e ≠ 0)).card) :
    Interpolates G (localChecks G C) t := by
  classical
  intro w S hS hcard f
  set Q := star G w \ S with hQ
  -- restriction of local words to the coordinates outside `S` is injective
  let R : C w →ₗ[𝔽] (Q → 𝔽) :=
    { toFun := fun c q => (c : Sym2 W → 𝔽) q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hRinj : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    by_contra hne
    have hne' : (c : Sym2 W → 𝔽) ≠ 0 := fun h => hne (Subtype.ext h)
    have hlt := hwt w c c.2 hne'
    have hsubS : (star G w).filter (fun e => (c : Sym2 W → 𝔽) e ≠ 0) ⊆ S := by
      intro e he
      obtain ⟨hes, hce⟩ := Finset.mem_filter.1 he
      by_contra heS
      have heQ : e ∈ Q := Finset.mem_sdiff.2 ⟨hes, heS⟩
      exact hce (congrFun hc ⟨e, heQ⟩)
    exact absurd (hlt.trans_le ((Finset.card_le_card hsubS).trans hcard)) (lt_irrefl _)
  obtain ⟨L, hL⟩ := R.exists_leftInverse_of_injective hRinj
  -- the functional to be represented on the coordinates outside `S`
  let φ : C w →ₗ[𝔽] 𝔽 :=
    { toFun := fun c => -∑ e ∈ S, f e * (c : Sym2 W → 𝔽) e
      map_add' := fun a b => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
      map_smul' := fun a b => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_neg, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun e _ => by ring }
  let ψ : (Q → 𝔽) →ₗ[𝔽] 𝔽 := φ.comp L
  let g' : Q → 𝔽 := fun q => ψ (Pi.single q 1)
  have hψ : ∀ x : Q → 𝔽, ψ x = ∑ q, g' q * x q := by
    intro x
    conv_lhs => rw [show x = ∑ q, x q • Pi.single q (1 : 𝔽) by
      ext q'; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_smul, smul_eq_mul, mul_comm]
  -- the local check: `f` on `S`, `g'` on the other edges at `w`
  let gfun : Sym2 W → 𝔽 := fun e => if e ∈ S then f e else if h : e ∈ Q then g' ⟨e, h⟩ else 0
  have hgfun : ∀ e, gfun e ≠ 0 → e ∈ star G w := by
    intro e he
    by_cases heS : e ∈ S
    · exact hS heS
    · by_cases heQ : e ∈ Q
      · exact (Finset.mem_sdiff.1 heQ).1
      · simp [gfun, heS, heQ] at he
  let g : Sym2 W →₀ 𝔽 := Finsupp.onFinset (star G w) gfun hgfun
  refine ⟨g, ⟨fun e he => hgfun e (by simpa [g] using he), fun c hc => ?_⟩, fun e he => ?_⟩
  · -- orthogonality to the local code
    have hsplit : ∑ e ∈ star G w, g e * c e =
        ∑ e ∈ S, f e * c e + ∑ e ∈ Q, gfun e * c e := by
      rw [← Finset.sum_sdiff hS, add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun e he => by simp [g, gfun, he]
    have hQsum : ∑ e ∈ Q, gfun e * c e = ∑ q : Q, g' q * R ⟨c, hc⟩ q := by
      rw [← Finset.sum_coe_sort Q]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hqS : (q : Sym2 W) ∉ S := (Finset.mem_sdiff.1 q.2).2
      simp [gfun, hqS, q.2, R]
    rw [hsplit, hQsum, ← hψ]
    have : ψ (R ⟨c, hc⟩) = φ ⟨c, hc⟩ := by
      show φ (L (R ⟨c, hc⟩)) = φ ⟨c, hc⟩
      rw [show L (R ⟨c, hc⟩) = ⟨c, hc⟩ from LinearMap.congr_fun hL _]
    rw [this]
    simp [φ]
  · -- the prescribed values on `S`
    simp [g, gfun, he]

end AboveHalf
