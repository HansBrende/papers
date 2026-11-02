import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Logic.Relation

/-!
# Peeling: private checks from a degenerate edge set

A graph `G` (possibly infinite, locally finite) carries at each vertex `w` a space `D w` of local
checks, finitely supported functions on the edges at `w`. The local checks *interpolate on `t`
coordinates*: on any `t` edges at `w` they take arbitrary prescribed values. (This holds when the
local checks are the dual of an MDS local code of redundancy `t`; see `AboveHalfRate.Tanner`.)

Let `A` be a set of edges and `r` a rank function on vertices such that the two ends of an edge of
`A` have different ranks and every vertex has at most `t` edges of `A` to vertices of larger rank.
Then every edge `a = uv` of `A` with `r u < r v` has a *private check*: a finite sum of local checks
that equals `1` on `a` and `0` on every other edge of `A`. It is a sum of local checks at vertices
reachable from `u` along edges of `A` with strictly decreasing rank, so it is supported on the edges
at those vertices, all within distance `r u` of `u`.

The proof is the peeling recursion: at the lower end `w` of an edge, choose a local check with the
prescribed values on the edges of `A` going up from `w`, then cancel its values on the edges of `A`
going down by recursion at their lower ends.
-/

namespace AboveHalf

open Finset

set_option autoImplicit false

variable {W : Type*} [DecidableEq W] (G : SimpleGraph W) [G.LocallyFinite]
variable {𝔽 : Type*} [Field 𝔽]

/-- The edges at `w`. -/
def star (w : W) : Finset (Sym2 W) := (G.neighborFinset w).image (fun y => s(w, y))

theorem mem_star {w : W} {e : Sym2 W} : e ∈ star G w ↔ ∃ y, G.Adj w y ∧ s(w, y) = e := by
  simp [star]

theorem mk_mem_star {w y : W} (h : G.Adj w y) : s(w, y) ∈ star G w :=
  (mem_star G).2 ⟨y, h, rfl⟩

/-- Local checks interpolate on `t` coordinates: on at most `t` edges at a vertex, some local
check takes arbitrary prescribed values. -/
def Interpolates (D : W → Submodule 𝔽 (Sym2 W →₀ 𝔽)) (t : ℕ) : Prop :=
  ∀ (w : W) (S : Finset (Sym2 W)), S ⊆ star G w → S.card ≤ t →
    ∀ f : Sym2 W → 𝔽, ∃ g ∈ D w, ∀ e ∈ S, g e = f e

/-- One step down: from `w` to a neighbour `w'` of smaller rank across an edge of `A`. -/
def DownStep (A : Sym2 W → Prop) (r : W → ℕ) (w w' : W) : Prop :=
  G.Adj w w' ∧ A s(w, w') ∧ r w' < r w

/-- The down-set of `u`: the vertices reachable from `u` by steps down. -/
abbrev Down (A : Sym2 W → Prop) (r : W → ℕ) (u : W) : Type _ :=
  {w // Relation.ReflTransGen (DownStep G A r) u w}

/-- The span of the local checks at the vertices of the down-set of `u`. -/
noncomputable def downChecks (D : W → Submodule 𝔽 (Sym2 W →₀ 𝔽)) (A : Sym2 W → Prop) (r : W → ℕ) (u : W) :
    Submodule 𝔽 (Sym2 W →₀ 𝔽) :=
  ⨆ w : Down G A r u, D w.1

section Peel

variable {G}
variable (D : W → Submodule 𝔽 (Sym2 W →₀ 𝔽)) (A : Sym2 W → Prop)
  (r : W → ℕ) (t : ℕ)

omit [DecidableEq W] [G.LocallyFinite] in
/-- The down-sets are nested along steps down. -/
theorem downChecks_mono {w z : W} (h : DownStep G A r w z) :
    downChecks G D A r z ≤ downChecks G D A r w := by
  exact iSup_le fun x =>
    le_iSup (fun y : Down G A r w => D y.1) ⟨x.1, Relation.ReflTransGen.head h x.2⟩

omit [DecidableEq W] [G.LocallyFinite] in
theorem le_downChecks_self (w : W) : D w ≤ downChecks G D A r w :=
  le_iSup (fun y : Down G A r w => D y.1) ⟨w, Relation.ReflTransGen.refl⟩

/-- The recursion behind `exists_private_check`, for an edge going up from `w`, with an arbitrary
prescribed value `c` on it. -/
theorem exists_check_up [DecidablePred A]
    (hsupp : ∀ w, ∀ g ∈ D w, ∀ e ∈ g.support, e ∈ star G w)
    (hint : Interpolates G D t)
    (hsep : ∀ x y, G.Adj x y → A s(x, y) → r x ≠ r y)
    (hdeg : ∀ w, ((G.neighborFinset w).filter (fun y => A s(w, y) ∧ r w < r y)).card ≤ t) :
    ∀ (n : ℕ) (w : W), r w = n → ∀ y, G.Adj w y → A s(w, y) → r w < r y → ∀ c : 𝔽,
      ∃ h ∈ downChecks G D A r w, ∀ e, A e → h e = if e = s(w, y) then c else 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hwn y hwy hAy hry c
  -- the up-neighbours and the up-edges at `w`
  set U := (G.neighborFinset w).filter (fun y' => A s(w, y') ∧ r w < r y') with hU
  set Sup := U.image (fun y' => s(w, y')) with hSup
  have hSup_star : Sup ⊆ star G w := by
    intro e he
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 he
    exact mk_mem_star G ((G.mem_neighborFinset w y').1 (Finset.mem_filter.1 hy').1)
  have hSup_card : Sup.card ≤ t := (Finset.card_image_le).trans (hdeg w)
  obtain ⟨g₀, hg₀D, hg₀⟩ :=
    hint w Sup hSup_star hSup_card (fun e => if e = s(w, y) then c else 0)
  -- the down-neighbours, and the recursive corrections there
  set Dn := (G.neighborFinset w).filter (fun z => A s(w, z) ∧ r z < r w) with hDn
  have hrec : ∀ z ∈ Dn, ∃ h ∈ downChecks G D A r z,
      ∀ e, A e → h e = if e = s(z, w) then -g₀ s(w, z) else 0 := by
    intro z hz
    have hz' := Finset.mem_filter.1 hz
    have hzadj : G.Adj w z := (G.mem_neighborFinset w z).1 hz'.1
    have hzA : A s(w, z) := hz'.2.1
    have hzr : r z < r w := hz'.2.2
    refine ih (r z) (hwn ▸ hzr) z rfl w hzadj.symm (by rwa [Sym2.eq_swap]) hzr _
  choose! hz hzmem hzval using hrec
  refine ⟨g₀ + ∑ z ∈ Dn, hz z, ?_, ?_⟩
  · refine Submodule.add_mem _ (le_downChecks_self D A r w hg₀D) ?_
    refine Submodule.sum_mem _ fun z hzD => ?_
    have hz' := Finset.mem_filter.1 hzD
    have hstep : DownStep G A r w z :=
      ⟨(G.mem_neighborFinset w z).1 hz'.1, hz'.2.1, hz'.2.2⟩
    exact downChecks_mono D A r hstep (hzmem z hzD)
  · intro e hAe
    have hsum : (∑ z ∈ Dn, hz z) e = ∑ z ∈ Dn, (if e = s(z, w) then -g₀ s(w, z) else 0) := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.sum_congr rfl fun z hzD => hzval z hzD e hAe
    rw [Finsupp.add_apply, hsum]
    by_cases hstar : e ∈ star G w
    · obtain ⟨x, hwx, rfl⟩ := (mem_star G).1 hstar
      rcases lt_or_gt_of_ne (hsep w x hwx hAe) with hlt | hgt
      · -- an up-edge: `g₀` has the prescribed value and no correction touches it
        have hxU : x ∈ U := Finset.mem_filter.2 ⟨(G.mem_neighborFinset w x).2 hwx, hAe, hlt⟩
        have hval := hg₀ _ (Finset.mem_image_of_mem _ hxU)
        have hzero : ∑ z ∈ Dn, (if s(w, x) = s(z, w) then -g₀ s(w, z) else 0) = 0 := by
          refine Finset.sum_eq_zero fun z hzD => ?_
          have hz' := Finset.mem_filter.1 hzD
          rw [ite_eq_right]
          intro heq
          rcases Sym2.eq_iff.1 heq with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact ((G.mem_neighborFinset w z).1 hz'.1).ne h1
          · subst h2; exact absurd (hlt.trans hz'.2.2) (lt_irrefl _)
        rw [hval, hzero, add_zero]
      · -- a down-edge: the correction at `x` cancels `g₀`
        have hxDn : x ∈ Dn := Finset.mem_filter.2 ⟨(G.mem_neighborFinset w x).2 hwx, hAe, hgt⟩
        have hone : ∑ z ∈ Dn, (if s(w, x) = s(z, w) then -g₀ s(w, z) else 0) = -g₀ s(w, x) := by
          rw [Finset.sum_eq_single x]
          · rw [ite_eq_left (Sym2.eq_swap)]
          · intro z hzD hzx
            rw [ite_eq_right]
            intro heq
            rcases Sym2.eq_iff.1 heq with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact ((G.mem_neighborFinset w z).1 (Finset.mem_filter.1 hzD).1).ne h1
            · exact hzx h2.symm
          · intro h; exact absurd hxDn h
        rw [hone, add_neg_cancel, ite_eq_right]
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨_, h2⟩ | ⟨h1, _⟩
        · subst h2; exact absurd (hgt.trans hry) (lt_irrefl _)
        · exact hwy.ne h1
    · -- an edge away from `w`: nothing touches it
      have hg0 : g₀ e = 0 := by
        by_contra hne
        exact hstar (hsupp w g₀ hg₀D e (Finsupp.mem_support_iff.2 hne))
      have hzero : ∑ z ∈ Dn, (if e = s(z, w) then -g₀ s(w, z) else 0) = 0 := by
        refine Finset.sum_eq_zero fun z hzD => ?_
        rw [ite_eq_right]
        rintro rfl
        exact hstar (by
          rw [Sym2.eq_swap]
          exact mk_mem_star G ((G.mem_neighborFinset w z).1 (Finset.mem_filter.1 hzD).1))
      rw [hg0, hzero, add_zero, ite_eq_right]
      rintro rfl
      exact hstar (mk_mem_star G hwy)

/-- **Peeling.** An edge `a = uv` of `A` with `r u < r v` has a private check: a sum of local checks
at the vertices of the down-set of `u` that is `1` on `a` and `0` on every other edge of `A`. -/
theorem exists_private_check [DecidablePred A]
    (hsupp : ∀ w, ∀ g ∈ D w, ∀ e ∈ g.support, e ∈ star G w)
    (hint : Interpolates G D t)
    (hsep : ∀ x y, G.Adj x y → A s(x, y) → r x ≠ r y)
    (hdeg : ∀ w, ((G.neighborFinset w).filter (fun y => A s(w, y) ∧ r w < r y)).card ≤ t)
    {u v : W} (huv : G.Adj u v) (hA : A s(u, v)) (hr : r u < r v) :
    ∃ h ∈ downChecks G D A r u, ∀ e, A e → h e = if e = s(u, v) then 1 else 0 :=
  exists_check_up D A r t hsupp hint hsep hdeg (r u) u rfl v huv hA hr 1

/-- Elements of `downChecks` are supported on the edges at vertices of the down-set. -/
theorem support_downChecks
    (hsupp : ∀ w, ∀ g ∈ D w, ∀ e ∈ g.support, e ∈ star G w) {u : W} {h : Sym2 W →₀ 𝔽}
    (hh : h ∈ downChecks G D A r u) :
    ∀ e ∈ h.support, ∃ w : Down G A r u, e ∈ star G w.1 := by
  classical
  refine Submodule.iSup_induction (fun w : Down G A r u => D w.1)
    (motive := fun h => ∀ e ∈ h.support, ∃ w : Down G A r u, e ∈ star G w.1) hh ?_ ?_ ?_
  · exact fun w g hg e he => ⟨w, hsupp w.1 g hg e he⟩
  · simp
  · intro g₁ g₂ h₁ h₂ e he
    rcases Finset.mem_union.1 (Finsupp.support_add he) with h | h
    · exact h₁ e h
    · exact h₂ e h

omit [DecidableEq W] [G.LocallyFinite] in
/-- The down-set of `u` lies within distance `r u` of `u`: each step down lowers the rank. -/
theorem exists_walk_of_down {u w : W} (h : Relation.ReflTransGen (DownStep G A r) u w) :
    ∃ p : G.Walk u w, p.length + r w ≤ r u := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | tail _ hstep ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat hstep.1, ?_⟩
    rw [SimpleGraph.Walk.length_concat]
    have := hstep.2.2
    omega

end Peel

end AboveHalf
