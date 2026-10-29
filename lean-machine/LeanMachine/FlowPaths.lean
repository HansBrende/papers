import LeanMachine.FiniteFlow
import Mathlib.Combinatorics.Quiver.Path

/-! Finite weighted path extraction from real flows. Paths retain edge
identities and their loads count every traversal. Cycles and unused
residual flow are allowed; the entire nonnegative source value is routed. -/

namespace LeanMachine.FiniteFlow.Network

open Finset
open scoped BigOperators Classical
noncomputable section

variable {Vertex Edge : Type*} (G : Network Vertex Edge)

/-- The arrows are the original edge identities with their endpoints. -/
@[instance_reducible] def quiver : Quiver Vertex where
  Hom u v := {e : Edge // G.source e = u ∧ G.target e = v}

abbrev Path (s t : Vertex) := @Quiver.Path Vertex G.quiver s t

/-- Original edges in traversal order, including repetitions. -/
def pathEdges {s t : Vertex} (p : G.Path s t) : List Edge := by
  letI := G.quiver
  induction p with
  | nil => exact []
  | cons p e ih => exact ih ++ [e.val]

/-- One unit of path mass, counting every traversal of every edge. -/
def pathFlow {s t : Vertex} (p : G.Path s t) : Edge → ℝ := by
  letI := G.quiver
  induction p with
  | nil => exact 0
  | cons p e ih => exact ih + unit e.val

@[simp] theorem pathEdges_cons {s u v : Vertex} (p : G.Path s u)
    (e : {e : Edge // G.source e = u ∧ G.target e = v}) :
    G.pathEdges (@Quiver.Path.cons _ G.quiver s u v p e) =
      G.pathEdges p ++ [e.val] := rfl

@[simp] theorem pathFlow_cons {s u v : Vertex} (p : G.Path s u)
    (e : {e : Edge // G.source e = u ∧ G.target e = v}) :
    G.pathFlow (@Quiver.Path.cons _ G.quiver s u v p e) =
      G.pathFlow p + unit e.val := rfl

theorem pathFlow_eq_count {s t : Vertex} (p : G.Path s t) (e : Edge) :
    G.pathFlow p e = ((G.pathEdges p).count e : ℝ) := by
  induction p with
  | nil => simp [pathFlow, pathEdges]
  | cons p a ih =>
    rw [G.pathFlow_cons, G.pathEdges_cons, Pi.add_apply, ih, List.count_append]
    by_cases he : e = a.val <;> simp [unit, he, eq_comm]

theorem pathFlow_nonneg {s t : Vertex} (p : G.Path s t) (e : Edge) :
    0 ≤ G.pathFlow p e := by
  rw [G.pathFlow_eq_count]
  exact Nat.cast_nonneg _

theorem pathFlow_pos_iff {s t : Vertex} (p : G.Path s t) (e : Edge) :
    0 < G.pathFlow p e ↔ e ∈ G.pathEdges p := by
  rw [G.pathFlow_eq_count, Nat.cast_pos, List.count_pos_iff]

theorem pathEdges_ne_nil {s t : Vertex} (p : G.Path s t) (hst : s ≠ t) :
    G.pathEdges p ≠ [] := by
  cases p with
  | nil => exact False.elim (hst rfl)
  | cons p e => simp [pathEdges]

variable [fe : Fintype Edge]

theorem divergence_sub (f g : Edge → ℝ) (v : Vertex) :
    G.divergence (f - g) v = G.divergence f v - G.divergence g v := by
  rw [sub_eq_add_neg, G.divergence_add, G.divergence_neg, sub_eq_add_neg]

/-- Internal divergences telescope even if a path repeats edges. -/
theorem pathFlow_divergence {s t : Vertex} (p : G.Path s t) (v : Vertex) :
    G.divergence (G.pathFlow p) v =
      (if v = s then 1 else 0) - (if v = t then 1 else 0) := by
  induction p with
  | nil => simp [pathFlow]
  | cons p e ih =>
    rw [G.pathFlow_cons, G.divergence_add, ih, G.divergence_unit]
    simp only [incidence, e.property.1, e.property.2, eq_comm]
    ring

def PositiveStep (f : Edge → ℝ) (u v : Vertex) : Prop :=
  ∃ e, G.source e = u ∧ G.target e = v ∧ 0 < f e

omit [Fintype Edge] in
/-- Reachability retains a concrete arrow at every step. -/
theorem positive_path_of_reachable {f : Edge → ℝ} {s t : Vertex}
    (hr : Relation.ReflTransGen (G.PositiveStep f) s t) :
    ∃ p : G.Path s t, ∀ e ∈ G.pathEdges p, 0 < f e := by
  induction hr with
  | refl => exact ⟨@Quiver.Path.nil _ G.quiver _, by simp [pathEdges]⟩
  | tail _ he ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨e, hs, ht, he⟩ := he
    refine ⟨@Quiver.Path.cons _ G.quiver _ _ _ p ⟨e, hs, ht⟩, ?_⟩
    intro k hk
    simp only [G.pathEdges_cons, List.mem_append, List.mem_singleton] at hk
    exact hk.elim (hp k) (fun h => h ▸ he)

variable [fv : Fintype Vertex]

/-- A positive net source value forces a positive source-to-sink path.
No acyclicity or restriction on incoming source edges is needed. -/
theorem exists_positive_path {s t : Vertex} {f : Edge → ℝ}
    (hf : G.Feasible s t f) (hp : 0 < G.divergence f s) :
    ∃ p : G.Path s t, ∀ e ∈ G.pathEdges p, 0 < f e := by
  apply G.positive_path_of_reachable
  by_contra ht
  let U : Set Vertex := {v | Relation.ReflTransGen (G.PositiveStep f) s v}
  have hs : s ∈ U := .refl
  have ho : G.crossingSum f U = 0 := by
    apply sum_eq_zero
    intro e _
    split_ifs with he
    · apply le_antisymm ?_ (hf.1.1 e)
      by_contra hn
      exact he.2 (he.1.tail ⟨e, rfl, rfl, lt_of_not_ge hn⟩)
    · rfl
  have hi : 0 ≤ G.crossingSum f Uᶜ := by
    apply sum_nonneg
    intro e _
    split_ifs <;> [exact hf.1.1 e; exact le_rfl]
  rw [G.value_eq_net_cut hf hs ht, ho] at hp
  linarith

omit [Fintype Vertex] in
/-- The largest permitted scalar step either uses the whole remaining
demand or exhausts a previously positive edge. -/
theorem exhausting_step (f h : Edge → ℝ) (R : ℝ) (hR : 0 < R)
    (hf : ∀ e, 0 ≤ f e) (hh : ∀ e, 0 ≤ h e)
    (hpos : ∀ e, 0 < h e → 0 < f e) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ (∀ e, δ * h e ≤ f e) ∧
      (δ = R ∨ ∃ e, 0 < f e ∧ δ * h e = f e) := by
  let radius : Option Edge → ℝ :=
    Option.elim' R (fun e => if 0 < h e then f e / h e else R)
  let δ := univ.inf' univ_nonempty radius
  have hδ : 0 < δ := by
    apply (lt_inf'_iff _).mpr
    rintro (_ | e) _
    · exact hR
    · dsimp [radius]
      split_ifs with he
      · exact div_pos (hpos e he) he
      · exact hR
  have hle (i : Option Edge) : δ ≤ radius i := inf'_le _ (mem_univ i)
  refine ⟨δ, hδ, hle none, ?_, ?_⟩
  · intro e
    by_cases he : 0 < h e
    · exact (le_div_iff₀ he).mp (by simpa [radius, he] using hle (some e))
    · have hz : h e = 0 := le_antisymm (le_of_not_gt he) (hh e)
      simpa [hz] using hf e
  · obtain ⟨i, _, hi⟩ := exists_mem_eq_inf' univ_nonempty radius
    rcases i with _ | e
    · exact Or.inl hi
    · by_cases he : 0 < h e
      · right
        refine ⟨e, hpos e he, ?_⟩
        have hd : δ = f e / h e := by simpa [radius, he] using hi
        rw [hd, div_mul_cancel₀ _ he.ne']
      · exact Or.inl (by simpa [radius, he] using hi)

omit [Fintype Edge] [Fintype Vertex]

def packingMass {s t : Vertex} (P : List (ℝ × G.Path s t)) : ℝ :=
  (P.map Prod.fst).sum

def packingLoad {s t : Vertex} (P : List (ℝ × G.Path s t)) : Edge → ℝ :=
  (P.map (fun q => q.1 • G.pathFlow q.2)).sum

@[simp] theorem packingMass_nil (s t : Vertex) :
    G.packingMass ([] : List (ℝ × G.Path s t)) = 0 := rfl

@[simp] theorem packingLoad_nil (s t : Vertex) :
    G.packingLoad ([] : List (ℝ × G.Path s t)) = 0 := rfl

@[simp] theorem packingMass_cons {s t : Vertex} (δ : ℝ) (p : G.Path s t)
    (P : List (ℝ × G.Path s t)) :
    G.packingMass ((δ, p) :: P) = δ + G.packingMass P := rfl

@[simp] theorem packingLoad_cons {s t : Vertex} (δ : ℝ) (p : G.Path s t)
    (P : List (ℝ × G.Path s t)) :
    G.packingLoad ((δ, p) :: P) = δ • G.pathFlow p + G.packingLoad P := rfl

theorem packingLoad_nonneg {s t : Vertex} (P : List (ℝ × G.Path s t))
    (hP : ∀ q ∈ P, 0 ≤ q.1) (e : Edge) : 0 ≤ G.packingLoad P e := by
  induction P with
  | nil => simp
  | cons q P ih =>
    have hq := hP q (by simp)
    have ht : ∀ p ∈ P, 0 ≤ p.1 := fun p hp => hP p (by simp [hp])
    exact add_nonneg (mul_nonneg hq (G.pathFlow_nonneg q.2 e)) (ih ht)

include fe

theorem packingLoad_divergence {s t : Vertex} (P : List (ℝ × G.Path s t))
    (v : Vertex) : G.divergence (G.packingLoad P) v =
      G.packingMass P * ((if v = s then 1 else 0) - (if v = t then 1 else 0)) := by
  induction P with
  | nil => simp
  | cons q P ih =>
    rw [G.packingLoad_cons, G.divergence_add, G.divergence_smul,
      G.pathFlow_divergence, ih, G.packingMass_cons]
    ring

theorem packing_feasible {s t : Vertex} (P : List (ℝ × G.Path s t))
    (hP : ∀ q ∈ P, 0 ≤ q.1) (hc : ∀ e, G.packingLoad P e ≤ G.capacity e) :
    G.Feasible s t (G.packingLoad P) := by
  refine ⟨⟨G.packingLoad_nonneg P hP, hc⟩, fun v hs ht => ?_⟩
  simp [G.packingLoad_divergence, hs, ht]

include fe fv

/-- Extract the entire nonnegative net source value as a finite packing of
positive-weight paths, with multiplicity-sensitive loads bounded by `f`.
At most one path per originally positive edge is needed. Cycles, incoming
source arcs and outgoing sink arcs are permitted; unused flow is discarded. -/
theorem exists_path_packing {s t : Vertex} (hst : s ≠ t) {f : Edge → ℝ}
    (hf : G.Feasible s t f) (hR : 0 ≤ G.divergence f s) :
    ∃ P : List (ℝ × G.Path s t),
      (∀ q ∈ P, 0 < q.1) ∧ G.packingMass P = G.divergence f s ∧
      (∀ e, G.packingLoad P e ≤ f e) ∧
      P.length ≤ (univ.filter (fun e => 0 < f e)).card := by
  generalize hk : (univ.filter (fun e => 0 < f e)).card = k
  induction k using Nat.strong_induction_on generalizing f with
  | h k ih =>
    by_cases hz : G.divergence f s = 0
    · exact ⟨[], by simp, by simp [hz], fun e => hf.1.1 e, by simp⟩
    have hpos : 0 < G.divergence f s := lt_of_le_of_ne hR (Ne.symm hz)
    obtain ⟨p, hp⟩ := G.exists_positive_path hf hpos
    obtain ⟨δ, hδ, hδR, hstep, hstop⟩ := exhausting_step f (G.pathFlow p)
      (G.divergence f s) hpos hf.1.1 (G.pathFlow_nonneg p)
      (fun e he => hp e ((G.pathFlow_pos_iff p e).mp he))
    have hlen : 1 ≤ k := by
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil (G.pathEdges p) (G.pathEdges_ne_nil p hst)
      have : 0 < (univ.filter (fun e => 0 < f e)).card :=
        card_pos.mpr ⟨e, by simp [hp e he]⟩
      omega
    rcases hstop with hfull | ⟨e₀, he₀, hexhaust⟩
    · refine ⟨[(δ, p)], by simp [hδ], by simpa using hfull, ?_, by simpa⟩
      intro e
      simpa using hstep e
    let g := f - δ • G.pathFlow p
    have hgle (e : Edge) : g e ≤ f e :=
      sub_le_self _ (mul_nonneg hδ.le (G.pathFlow_nonneg p e))
    have hgdiv (v : Vertex) : G.divergence g v = G.divergence f v -
        δ * ((if v = s then 1 else 0) - (if v = t then 1 else 0)) := by
      dsimp [g]
      rw [G.divergence_sub, G.divergence_smul, G.pathFlow_divergence]
    have hg : G.Feasible s t g := by
      refine ⟨⟨fun e => sub_nonneg.mpr (hstep e),
        fun e => (hgle e).trans (hf.1.2 e)⟩, fun v hs ht => ?_⟩
      simp [hgdiv, hf.2 v hs ht, hs, ht]
    have hgv : G.divergence g s = G.divergence f s - δ := by
      simpa [hst] using hgdiv s
    have hcard : (univ.filter (fun e => 0 < g e)).card < k := by
      rw [← hk]
      apply card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [mem_filter, mem_univ, true_and] at he ⊢
        exact he.trans_le (hgle e)
      · intro heq
        have hmem : e₀ ∈ univ.filter (fun e => 0 < f e) := by simp [he₀]
        rw [← heq] at hmem
        have hgzero : g e₀ = 0 := sub_eq_zero.mpr hexhaust.symm
        simp [hgzero] at hmem
    obtain ⟨P, hP, hmass, hload, hlength⟩ := ih _ hcard hg
      (by rw [hgv]; exact sub_nonneg.mpr hδR) rfl
    refine ⟨(δ, p) :: P, ?_, ?_, ?_, ?_⟩
    · simpa using And.intro hδ hP
    · rw [G.packingMass_cons, hmass, hgv]
      ring
    · intro e
      change δ * G.pathFlow p e + G.packingLoad P e ≤ f e
      have he := hload e
      change G.packingLoad P e ≤ f e - δ * G.pathFlow p e at he
      linarith
    · simp only [List.length_cons]
      omega

end
end LeanMachine.FiniteFlow.Network
