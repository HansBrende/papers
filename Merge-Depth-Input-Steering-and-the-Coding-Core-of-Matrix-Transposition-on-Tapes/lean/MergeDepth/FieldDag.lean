import MergeDepth.Lineage
import MergeDepth.ColdGenie

/-!
# Function DAGs: the cone lemma and index codes (Lemma 3.3(b))

A *function DAG* (`FunDag`) has vertices `ℕ`, out-edges to earlier vertices, an optional input
position read at each vertex, and a value `val w u` for every binary input `w`, determined by the
values at the out-neighbours and by the bit read (`det`). The field DAG of a pruning is one (the
fourth paper's local recursion). Its paths, freeness and deep-edge counts are those of the
underlying network `G.net` (with zero coefficients; only its edges and reads are used).

* `FunDag.cone`: inputs that agree on the revealed vertices `Γ` and on the positions read at the
  ends of the `Γ`-free paths from `u` (`coneSet`) give `u` the same value.
* `FunDag.isIndexCode`: with output vertices whose values determine the transposed bits, the
  revealed values together with the bits of the positions in `X` form an index code for the system
  that is empty on `X` and on revealed outputs and is the cone set of the output elsewhere.
-/

namespace MergeDepth

open Finset BoundedNesting

/-- A DAG of functions of a binary input. -/
structure FunDag (L : ℕ) where
  out : ℕ → Finset ℕ
  out_lt : ∀ t, ∀ s ∈ out t, s < t
  rd : ℕ → Option (Fin L)
  val : (Fin L → Bool) → ℕ → ℕ
  det : ∀ w w' u, (∀ v ∈ out u, val w v = val w' v) → (∀ j, rd u = some j → w j = w' j) →
    val w u = val w' u

namespace FunDag

variable {L : ℕ} (G : FunDag L)

/-- The underlying network, with zero coefficients. -/
def net : LinNet ℚ L 1 where
  out := G.out
  out_lt := G.out_lt
  c := fun _ => 0
  A := fun _ _ => 0
  a := fun _ => 0
  rd := G.rd

open Classical in
/-- The cone set `I_Γ(u)`: the positions read at the ends of the `Γ`-free paths from `u`. -/
noncomputable def coneSet (Γ : Finset ℕ) (u : ℕ) : Finset (Fin L) :=
  univ.filter fun j => ∃ π ∈ G.net.paths u, LinNet.GFree Γ π ∧ G.rd (π.getLastD u) = some j

theorem coneSet_mono {Γ : Finset ℕ} {u v : ℕ} (hv : v ∈ G.out u) (hvΓ : v ∉ Γ) :
    G.coneSet Γ v ⊆ G.coneSet Γ u := by
  intro j hj
  simp only [coneSet, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, hfree, hrd⟩ := hj
  obtain ⟨π', rfl⟩ := G.net.mem_paths_head hπ
  refine ⟨u :: v :: π', cons_cons_mem_paths.mpr ⟨hv, hπ⟩, gfree_cons_cons.mpr ⟨hvΓ, hfree⟩, ?_⟩
  rwa [LinNet.getLastD_cons_cons]

theorem rd_mem_coneSet {Γ : Finset ℕ} {u : ℕ} {j : Fin L} (h : G.rd u = some j) :
    j ∈ G.coneSet Γ u := by
  simp only [coneSet, mem_filter, mem_univ, true_and]
  exact ⟨[u], singleton_mem_paths _ _, gfree_singleton _ _, h⟩

/-- **The cone lemma.** -/
theorem cone (Γ : Finset ℕ) (w w' : Fin L → Bool) (hΓ : ∀ v ∈ Γ, G.val w v = G.val w' v) :
    ∀ u, (∀ j ∈ G.coneSet Γ u, w j = w' j) → G.val w u = G.val w' u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    refine G.det w w' u (fun v hv => ?_) (fun j hj => hu j (G.rd_mem_coneSet hj))
    by_cases hvΓ : v ∈ Γ
    · exact hΓ v hvΓ
    · exact ih v (G.out_lt u v hv) fun j hj => hu j (G.coneSet_mono hv hvΓ hj)

end FunDag

/-- An index code for the system `I` and the demands `tpos`: inputs with the same code word that
agree on `I ℓ` agree at `tpos ℓ`. -/
def IsIndexCode {L : ℕ} {α : Type*} (E : (Fin L → Bool) → α) (I : Fin L → Finset (Fin L))
    (tpos : Fin L → Fin L) : Prop :=
  ∀ ℓ w w', E w = E w' → (∀ j ∈ I ℓ, w j = w' j) → w (tpos ℓ) = w' (tpos ℓ)

namespace FunDag

variable {L : ℕ} (G : FunDag L)

open Classical in
/-- An index code from any code word that determines the revealed values and the bits at `X`. -/
theorem isIndexCode_of {α : Type*} (E : (Fin L → Bool) → α) (Γ : Finset ℕ) (X : Finset (Fin L))
    (o : Fin L → ℕ) (tpos : Fin L → Fin L) (dec : Fin L → ℕ → Bool)
    (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ))
    (hE : ∀ w w', E w = E w' → (∀ v ∈ Γ, G.val w v = G.val w' v) ∧
      ∀ ℓ ∈ X, w (tpos ℓ) = w' (tpos ℓ)) :
    IsIndexCode E (fun ℓ => if ℓ ∈ X ∨ o ℓ ∈ Γ then ∅ else G.coneSet Γ (o ℓ)) tpos := by
  intro ℓ w w' hEw hI
  obtain ⟨hΓ', hX⟩ := hE w w' hEw
  by_cases hℓ : ℓ ∈ X
  · exact hX ℓ hℓ
  by_cases ho : o ℓ ∈ Γ
  · rw [← hdec w ℓ, ← hdec w' ℓ, hΓ' _ ho]
  · have hI' : ∀ j ∈ G.coneSet Γ (o ℓ), w j = w' j := fun j hj => hI j (by simp [hℓ, ho, hj])
    rw [← hdec w ℓ, ← hdec w' ℓ, G.cone Γ w w' hΓ' (o ℓ) hI']

open Classical in
/-- **Lemma 3.3(b), index code.** If the value of the output vertex `o ℓ` determines the bit at
`tpos ℓ`, the revealed values and the bits of the positions in `X` form an index code for the system
that is empty on `X` and on revealed outputs and is the cone set of `o ℓ` elsewhere. -/
theorem isIndexCode (Γ : Finset ℕ) (X : Finset (Fin L)) (o : Fin L → ℕ) (tpos : Fin L → Fin L)
    (dec : Fin L → ℕ → Bool) (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ)) :
    IsIndexCode (fun w => ((fun v : Γ => G.val w v.1), (fun ℓ : X => w (tpos ℓ.1))))
      (fun ℓ => if ℓ ∈ X ∨ o ℓ ∈ Γ then ∅ else G.coneSet Γ (o ℓ)) tpos := by
  intro ℓ w w' hE hI
  simp only [Prod.mk.injEq] at hE
  obtain ⟨hΓ, hX⟩ := hE
  have hΓ' : ∀ v ∈ Γ, G.val w v = G.val w' v := fun v hv => congr_fun hΓ ⟨v, hv⟩
  by_cases hℓ : ℓ ∈ X
  · exact congr_fun hX ⟨ℓ, hℓ⟩
  by_cases ho : o ℓ ∈ Γ
  · rw [← hdec w ℓ, ← hdec w' ℓ, hΓ' _ ho]
  · have hI' : ∀ j ∈ G.coneSet Γ (o ℓ), w j = w' j := fun j hj => hI j (by simp [hℓ, ho, hj])
    rw [← hdec w ℓ, ← hdec w' ℓ, G.cone Γ w w' hΓ' (o ℓ) hI']

end FunDag

end MergeDepth
