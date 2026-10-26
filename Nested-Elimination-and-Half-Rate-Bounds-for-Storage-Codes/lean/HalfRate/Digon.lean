import HalfRate.PathCert
import HalfRate.Circulant

/-!
# Theorem PC for digon components

The blocks are the components of the digon graph `G₂(N)`, whose edges are the reciprocated arcs.
A parent outside a vertex's component is a one-way parent, and an arc from outside a component
into it is one-way; so (H1) and (H2) give the private outside parents of Theorem PC, and a
component that induces a path of `G₂(N)` is a chorded digon path.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- The digon graph `G₂(N)`: `u ~ v` iff `u → v` and `v → u`. -/
def digonGraph (N : V → Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => u ∈ N v ∧ v ∈ N u)

open Classical in
/-- The component of `v` in the digon graph. -/
noncomputable def digonComp (N : V → Finset V) (v : V) : Finset V :=
  univ.filter (fun w => (digonGraph N).Reachable v w)

theorem mem_digonComp {v w : V} : w ∈ digonComp N v ↔ (digonGraph N).Reachable v w := by
  classical
  simp [digonComp]

theorem digonComp_eq_iff {v w : V} : digonComp N w = digonComp N v ↔ (digonGraph N).Reachable v w := by
  constructor
  · intro h
    have hw : w ∈ digonComp N w := mem_digonComp.mpr SimpleGraph.Reachable.rfl
    rw [h] at hw
    exact mem_digonComp.mp hw
  · intro h
    ext x
    simp only [mem_digonComp]
    exact ⟨fun hx => h.trans hx, fun hx => h.symm.trans hx⟩

omit [DecidableEq V] [Fintype V] in
theorem digonGraph_adj {u v : V} (huv : u ≠ v) (h1 : u ∈ N v) (h2 : v ∈ N u) :
    (digonGraph N).Adj u v := by
  simp [digonGraph, SimpleGraph.fromRel_adj, huv, h1, h2]

/-- A parent in another component is a one-way parent. -/
theorem oneWay_of_comp_ne {u v : V} (h : u ∈ N v) (hne : digonComp N u ≠ digonComp N v) :
    v ∉ N u := by
  intro hvu
  apply hne
  rw [digonComp_eq_iff]
  have huv : u ≠ v := by rintro rfl; exact hne rfl
  exact (digonGraph_adj huv h hvu).reachable.symm

theorem fibre_digonComp (v : V) : univ.filter (digonComp N · = digonComp N v) = digonComp N v := by
  ext w
  simp only [mem_filter, mem_univ, true_and, digonComp_eq_iff, mem_digonComp]

/-- `K` induces a path `f 0 ~ f 1 ~ ⋯ ~ f (L-1)` of the digon graph. -/
def InducesDigonPath (N : V → Finset V) (K : Finset V) : Prop :=
  ∃ (L : ℕ) (f : Fin L → V), 0 < L ∧ Function.Injective f ∧ univ.image f = K ∧
    ∀ i j : Fin L, (digonGraph N).Adj (f i) (f j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

/-- **Theorem PC for digon components.** Let `N` be loopless and TT-free, let every vertex have
at most one one-way parent (H1), and let no vertex have one-way arcs to two vertices of one
component of the digon graph (H2). If every component has no one-way arc inside it and only
vertices with at most three parents, or induces a path of the digon graph, or carries an
elimination certificate, then `N` satisfies the weighted half bound. -/
theorem rateBound_pc_digon (hloop : ∀ v, v ∉ N v) (htt : TTFree N)
    (hH1 : ∀ v u u', u ∈ N v → v ∉ N u → u' ∈ N v → v ∉ N u' → u = u')
    (hH2 : ∀ w v v', w ∈ N v → v ∉ N w → w ∈ N v' → v' ∉ N w → (digonGraph N).Reachable v v' →
      v = v')
    (hK : ∀ v, ((∀ x ∈ digonComp N v, ∀ u ∈ N x, u ∈ digonComp N v → x ∈ N u) ∧
        ∀ x ∈ digonComp N v, (N x).card ≤ 3) ∨
      InducesDigonPath N (digonComp N v) ∨ Nonempty (ElimOn N (digonComp N v))) :
    RateBound N (1 / 2) := by
  have htt' : ∀ K, TTFreeOn N K := fun K x _ y _ z _ hxy hyz hxz h1 h2 h3 =>
    htt x y z hxy hyz hxz h1 h2 h3
  refine rateBound_pc hloop (digonComp N) ?_ ?_ ?_
  · intro v u hu u' hu' hne hne'
    exact hH1 v u u' hu (oneWay_of_comp_ne hu hne) hu' (oneWay_of_comp_ne hu' hne')
  · intro w v v' hvv' hne hwv hwv'
    have hne' : digonComp N w ≠ digonComp N v' := hvv' ▸ hne
    exact hH2 w v v' hwv (oneWay_of_comp_ne hwv hne) hwv' (oneWay_of_comp_ne hwv' hne')
      (digonComp_eq_iff.mp hvv'.symm)
  · intro i
    by_cases hi : ∃ v, digonComp N v = i
    · obtain ⟨v, rfl⟩ := hi
      rw [fibre_digonComp v]
      rcases hK v with ⟨ha, hb⟩ | ⟨L, f, hL, hf, himg, hadj⟩ | hc
      · exact Or.inl ⟨ha, hb, htt' _⟩
      · right; left
        have hmem : ∀ a, f a ∈ digonComp N v := fun a => himg ▸ mem_image_of_mem f (mem_univ a)
        -- arcs between positions at distance at least two are one-way
        have hone : ∀ a b : Fin L, f a ∈ N (f b) → (a.val + 2 ≤ b.val ∨ b.val + 2 ≤ a.val) →
            f b ∉ N (f a) := by
          intro a b hab hfar hba
          have hne : f a ≠ f b := fun he => by
            have := hf he; subst this; omega
          have := (hadj a b).mp (digonGraph_adj hne hab hba)
          omega
        refine ⟨{
          L := L
          pos := hL
          f := f
          inj := hf
          image := himg
          digon := ?_
          chordIn := ?_
          chordOut := ?_
          tt := htt' _ }⟩
        · intro a ha
          have h := (hadj ⟨a, by omega⟩ ⟨a + 1, ha⟩).mpr (Or.inl rfl)
          simp only [digonGraph, SimpleGraph.fromRel_adj] at h
          rcases h.2 with h' | h'
          · exact h'
          · exact ⟨h'.2, h'.1⟩
        · intro a a' b ha ha' hb h1 h2 hfar hfar'
          have := hH1 _ _ _ h1 (hone ⟨a, ha⟩ ⟨b, hb⟩ h1 hfar) h2 (hone ⟨a', ha'⟩ ⟨b, hb⟩ h2 hfar')
          exact Fin.mk.inj_iff.mp (hf this)
        · intro a b b' ha hb hb' h1 h2 hfar hfar'
          have hreach : (digonGraph N).Reachable (f ⟨b, hb⟩) (f ⟨b', hb'⟩) :=
            (mem_digonComp.mp (hmem _)).symm.trans (mem_digonComp.mp (hmem _))
          have := hH2 _ _ _ h1 (hone ⟨a, ha⟩ ⟨b, hb⟩ h1 hfar) h2 (hone ⟨a, ha⟩ ⟨b', hb'⟩ h2 hfar')
            hreach
          exact Fin.mk.inj_iff.mp (hf this)
      · exact Or.inr (Or.inr hc)
    · push Not at hi
      have hempty : univ.filter (digonComp N · = i) = ∅ := by
        ext w; simp [hi w]
      rw [hempty]
      exact Or.inl ⟨by simp, by simp, htt' _⟩

end HalfRate
