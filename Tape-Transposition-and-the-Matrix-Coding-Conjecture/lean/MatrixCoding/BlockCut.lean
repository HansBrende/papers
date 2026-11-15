import MatrixCoding.BlockIntervalWalk

/-!
# Capacity-independent cuts of the actual block graph

Bounded-depth cuts for the interval refinement project to a bounded rank
on the surviving block graph. The cut is geometric and independent of any
input values or network code.
-/

namespace LeanBacklog.BlockTCC

open Finset Transpose Transpose.Tape Transpose.Tape.Impl BoundedNesting MergeDepth BoundedStackDepth

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical in
/-- Maximum length of a completely uncut dependency path starting at `v`. -/
noncomputable def depthRank {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (Γ : Finset ℕ) (D v : ℕ) : ℕ :=
  Nat.findGreatest (fun n => ∃ π : List ℕ, IsDepPath xs T (v :: π) ∧
    (∀ u ∈ v :: π, u ∉ Γ) ∧ (v :: π).length = n) D

theorem depthRank_le {k : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ)
    (Γ : Finset ℕ) (D v : ℕ) : depthRank xs T Γ D v ≤ D := by
  classical
  exact Nat.findGreatest_le D

theorem depthRank_spec {k T D : ℕ} {xs : Fin k → ℕ → ℤ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ D)
    {v : ℕ} (hv : v ∉ Γ) :
    ∃ π : List ℕ, IsDepPath xs T (v :: π) ∧
      (∀ u ∈ v :: π, u ∉ Γ) ∧ (v :: π).length = depthRank xs T Γ D v := by
  classical
  have h1 : 1 ≤ D := hdepth [v] trivial (by simp [LinNet.GFree])
  exact Nat.findGreatest_spec (P := fun n => ∃ π : List ℕ,
    IsDepPath xs T (v :: π) ∧ (∀ u ∈ v :: π, u ∉ Γ) ∧ (v :: π).length = n)
    h1 ⟨[], trivial, by simpa using hv, rfl⟩

theorem depthRank_step {k T D a b : ℕ} {xs : Fin k → ℕ → ℤ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ D)
    (hab : DepStep xs T a b) (ha : a ∉ Γ) (hb : b ∉ Γ) :
    depthRank xs T Γ D b < depthRank xs T Γ D a := by
  classical
  obtain ⟨π, hp, hf, hn⟩ := depthRank_spec hdepth hb
  have hpath : IsDepPath xs T (a :: b :: π) := ⟨hab, hp⟩
  have hfree : ∀ u ∈ a :: b :: π, u ∉ Γ := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ha
    · exact hf u hu
  have hlen : depthRank xs T Γ D b + 1 ≤ D := by
    simpa only [List.length_cons, hn] using
      hdepth (a :: b :: π) hpath (fun u hu => hf u hu)
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  exact Nat.le_findGreatest hlen ⟨b :: π, hpath, hfree, by simpa only [List.length_cons] using congrArg Nat.succ hn⟩

theorem depthRank_state {k T D a b : ℕ} {xs : Fin k → ℕ → ℤ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ D)
    (hab : a ≤ b) (hbT : b < T) (hfree : ∀ t, a ≤ t → t ≤ b → t ∉ Γ) :
    depthRank xs T Γ D a ≤ depthRank xs T Γ D b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (by omega) (by omega) (fun t ht ht' => hfree t ht (by omega))
    have hstep := depthRank_step hdepth
      (a := a + (n + 1)) (b := a + n) (Or.inl ⟨by omega, hbT⟩)
      (hfree _ (by omega) le_rfl) (hfree _ (by omega) (by omega))
    exact hprev.trans hstep.le

theorem depthRank_state_strict {k T D a b : ℕ} {xs : Fin k → ℕ → ℤ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → π.length ≤ D)
    (hab : a < b) (hbT : b < T) (hfree : ∀ t, a ≤ t → t ≤ b → t ∉ Γ) :
    depthRank xs T Γ D a < depthRank xs T Γ D b := by
  have hle := depthRank_state hdepth (b := b - 1) (by omega) (by omega)
    (fun t ht ht' => hfree t ht (by omega))
  have hlt := depthRank_step hdepth (a := b) (b := b - 1)
    (Or.inl ⟨by omega, hbT⟩) (hfree _ hab.le le_rfl)
    (hfree _ (by omega) (by omega))
  exact hle.trans_lt hlt

/-- The depth constant depends on the tape count and cut density only. -/
noncomputable def blockDepth (k : ℕ) (θ : ℝ) : ℕ := genieDepth k 1 12 θ

/-- A small cut and bounded increasing rank on the actual surviving block
graph. Only unit-speed work walks are needed, not a code or correctness. -/
theorem exists_block_cut {k r : ℕ} (Dg : TSDiagram k)
    (hwalk : ∀ t, UnitSteps (Dg.work t)) (hr : 1 ≤ r)
    (hN : 1 ≤ Dg.nodes r) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (Γ : Finset ℕ) (rank : ℕ → ℕ),
      Γ ⊆ range (Dg.nodes r) ∧ (Γ.card : ℝ) ≤ θ * Dg.nodes r ∧
      (∀ v, rank v ≤ blockDepth k θ) ∧
      ∀ e ∈ Dg.edges r, e.1 ∉ Γ → e.2 ∉ Γ → rank e.1 < rank e.2 := by
  classical
  let N := Dg.nodes r
  let Q : Fin k → IntervalData N := fun t => residentData (Dg.work t) Dg.T (hwalk t) hr
  let xs : Fin k → ℕ → ℤ := fun t => (Q t).walk
  obtain ⟨γ, hγ, hdepth⟩ := genie_cost (k := k) (β := 1) (L := N) (T := 12 * N)
    (by omega) hN (C := 12) (by norm_num) hθ
    (by push_cast; nlinarith) xs (fun t => (Q t).isWalk)
  norm_num only [Nat.cast_one, one_mul] at hγ
  let Γ := (γ.filter (fun t => t < 12 * N)).image (fun t => t / 12)
  let rank := fun y => depthRank xs (12 * N) γ (blockDepth k θ) (12 * y + 6)
  have hsub : Γ ⊆ range N := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hy
    have ht' := (mem_filter.mp ht).2
    exact mem_range.mpr (by omega)
  have hcard : (Γ.card : ℝ) ≤ θ * N := by
    have hc : Γ.card ≤ γ.card := card_image_le.trans (card_filter_le _ _)
    have hc' : (Γ.card : ℝ) ≤ γ.card := by exact_mod_cast hc
    simpa only [Nat.one_mul] using hc'.trans hγ
  have hfree {y t : ℕ} (hy : y < N) (hyΓ : y ∉ Γ) (ht : t / 12 = y) : t ∉ γ := by
    intro htγ
    apply hyΓ
    exact mem_image.mpr ⟨t, mem_filter.mpr ⟨htγ, by omega⟩, ht⟩
  refine ⟨Γ, rank, hsub, hcard, fun v => depthRank_le _ _ _ _ _, ?_⟩
  intro e he hxΓ hzΓ
  obtain ⟨hx, hz⟩ := edges_lt Dg e he
  change e.1 < N at hx
  change e.2 < N at hz
  rcases mem_union.mp he with hm | hc
  · obtain ⟨heq, _⟩ := (mem_memEdges Dg).mp hm
    apply depthRank_state_strict hdepth (by omega) (by omega)
    intro t ht ht'
    have hh : t / 12 = e.1 ∨ t / 12 = e.2 := by omega
    rcases hh with hh | hh
    · exact hfree hx hxΓ hh
    · exact hfree hz hzΓ hh
  · obtain ⟨_, _, t, β, hch⟩ := (mem_chordEdges Dg).mp hc
    have hxβ : (Q t).lo e.1 ≤ β ∧ β ≤ (Q t).hi e.1 :=
      (residentData_mem_iff (hwalk t) hr hx β).mp hch.2.1
    have hzβ : (Q t).lo e.2 ≤ β ∧ β ≤ (Q t).hi e.2 :=
      (residentData_mem_iff (hwalk t) hr hz β).mp hch.2.2.1
    obtain ⟨p, u, hp0, hp1, hu0, hu1, hhop⟩ := (Q t).chord_hop hch.1 hz hxβ hzβ (by
      intro y hxy hyz hyβ
      exact hch.2.2.2 y hxy hyz
        ((residentData_mem_iff (hwalk t) hr (hyz.trans hz) β).mpr hyβ))
    have hpΓ : p ∉ γ := hfree hx hxΓ (by omega)
    have huΓ : u ∉ γ := hfree hz hzΓ (by omega)
    have hstep : DepStep xs (12 * N) u p := by
      right
      exact mem_image.mpr ⟨(t, p, u), mem_allHops.mpr hhop, rfl⟩
    have hleft := depthRank_state hdepth hp0 (by omega : p < 12 * N)
      (fun s hs hs' => hfree hx hxΓ (by omega))
    have hmid := depthRank_step hdepth hstep huΓ hpΓ
    have hright := depthRank_state hdepth (by omega : u ≤ 12 * e.2 + 6)
      (by omega : 12 * e.2 + 6 < 12 * N)
      (fun s hs hs' => hfree hz hzΓ (by omega))
    exact (hleft.trans_lt hmid).trans_le hright

#print axioms depthRank
#print axioms depthRank_le
#print axioms depthRank_spec
#print axioms depthRank_step
#print axioms depthRank_state
#print axioms depthRank_state_strict
#print axioms blockDepth
#print axioms exists_block_cut

end LeanBacklog.BlockTCC
