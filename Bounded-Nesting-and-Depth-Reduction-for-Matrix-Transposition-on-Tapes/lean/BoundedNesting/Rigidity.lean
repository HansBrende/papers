import Mathlib

/-!
# Per-machine rigidity for linear networks

A machine with an `F`-linear data path at length `L` defines a linear network (`LinNet`). Each step
`t` has out-neighbours `out t` at earlier steps (the dependency DAG), and the data path is a vector
recursion with values in `F^m`: a constant `c t`, matrices `A t s` and an input vector `a t` added at
the input position read by step `t`, if any (`rd t`). The recursion defines formal values
`val w t ∈ F^m` for every `w ∈ F^L`; on binary inputs they are the encodings of the step values.

For a genie `Γ` (a set of steps), `C Γ t j` is the sum of `W(π) a(t_n)` over the `Γ`-free paths
`π = (t = t₀ → ⋯ → t_n)` whose last step reads position `j`. Here `W(π)` is the product of the
matrices along `π` (`wt`), and a path is `Γ`-free if `t₁, …, t_n ∉ Γ` (`GFree`).

`reach Γ D t` is the set of positions read at the ends of `Γ`-free paths with at most `D` edges
from `t`. For `Γ = ∅` it is the ball set `B^D`.

`rigidity`: let the network transpose on binary inputs, with outputs read off steps `tout ℓ` by
affine functionals. Let each step of `Γ` take at most `2^β` values on binary inputs, and let every
output have linear depth at most `D` for `Γ`. Then `P_tpos = R + S` with `rank R ≤ β |Γ|` and row
`ℓ` of `S` supported in `reach Γ D (tout ℓ) ⊆ B^D (tout ℓ)`. Equivalently, the system has minrank at
most `β |Γ|` (`minrank_le`).

`dlin_step` is the step of Theorem `D_lin` at one size: a minrank of at least `(ρ - η) L` for the
ball system contradicts such a genie of cost `β |Γ| ≤ εL`.
-/

namespace BoundedNesting

open Finset Matrix Module

variable {F : Type*} [Field F] {L m : ℕ}

/-- A linear network: the dependency DAG of a schedule, with out-neighbours at earlier steps, and
a linear data path on it. -/
structure LinNet (F : Type*) [Field F] (L m : ℕ) where
  out : ℕ → Finset ℕ
  out_lt : ∀ t, ∀ s ∈ out t, s < t
  c : ℕ → Fin m → F
  A : ℕ → ℕ → Matrix (Fin m) (Fin m) F
  a : ℕ → Fin m → F
  rd : ℕ → Option (Fin L)

namespace LinNet

variable (net : LinNet F L m)

/-- The input term of step `t`: `w_j a_t` if step `t` reads position `j`. -/
def inp (w : Fin L → F) (t : ℕ) : Fin m → F :=
  match net.rd t with
  | some j => w j • net.a t
  | none => 0

/-- The formal values `V_t(w)`, `w ∈ F^L`, defined by the recursion of the data path. -/
def val (w : Fin L → F) (t : ℕ) : Fin m → F :=
  net.c t + (∑ s ∈ (net.out t).attach, net.A t s *ᵥ val w s.1) + net.inp w t
termination_by t
decreasing_by exact net.out_lt t s.1 s.2

theorem val_eq (w : Fin L → F) (t : ℕ) :
    net.val w t = net.c t + (∑ s ∈ net.out t, net.A t s *ᵥ net.val w s) + net.inp w t := by
  rw [val, Finset.sum_attach (net.out t) (fun s => net.A t s *ᵥ net.val w s)]

/-- The linear part of the values. -/
def vlin (w : Fin L → F) (t : ℕ) : Fin m → F :=
  (∑ s ∈ (net.out t).attach, net.A t s *ᵥ vlin w s.1) + net.inp w t
termination_by t
decreasing_by exact net.out_lt t s.1 s.2

theorem vlin_eq (w : Fin L → F) (t : ℕ) :
    net.vlin w t = (∑ s ∈ net.out t, net.A t s *ᵥ net.vlin w s) + net.inp w t := by
  rw [vlin, Finset.sum_attach (net.out t) (fun s => net.A t s *ᵥ net.vlin w s)]

theorem inp_add (w w' : Fin L → F) (t : ℕ) : net.inp (w + w') t = net.inp w t + net.inp w' t := by
  unfold inp
  cases net.rd t <;> simp [add_smul]

theorem inp_smul (c : F) (w : Fin L → F) (t : ℕ) : net.inp (c • w) t = c • net.inp w t := by
  unfold inp
  cases net.rd t <;> simp [mul_smul]

theorem inp_zero (t : ℕ) : net.inp 0 t = 0 := by
  unfold inp
  cases net.rd t <;> simp

/-- The values are affine in the input: `V_t(w) = V_t(0) + vlin w t`. -/
theorem val_eq_add (w : Fin L → F) : ∀ t, net.val w t = net.val 0 t + net.vlin w t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [net.val_eq w t, net.val_eq 0 t, net.vlin_eq w t, net.inp_zero, add_zero]
    have : ∑ s ∈ net.out t, net.A t s *ᵥ net.val w s =
        ∑ s ∈ net.out t, net.A t s *ᵥ net.val 0 s + ∑ s ∈ net.out t, net.A t s *ᵥ net.vlin w s := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [ih s (net.out_lt t s hs), Matrix.mulVec_add]
    rw [this]
    abel

theorem vlin_add (w w' : Fin L → F) : ∀ t, net.vlin (w + w') t = net.vlin w t + net.vlin w' t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [net.vlin_eq, net.vlin_eq w, net.vlin_eq w', net.inp_add]
    have : ∑ s ∈ net.out t, net.A t s *ᵥ net.vlin (w + w') s =
        ∑ s ∈ net.out t, net.A t s *ᵥ net.vlin w s + ∑ s ∈ net.out t, net.A t s *ᵥ net.vlin w' s := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [ih s (net.out_lt t s hs), Matrix.mulVec_add]
    rw [this]
    abel

theorem vlin_smul (c : F) (w : Fin L → F) : ∀ t, net.vlin (c • w) t = c • net.vlin w t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [net.vlin_eq, net.vlin_eq w, net.inp_smul, smul_add, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [ih s (net.out_lt t s hs), Matrix.mulVec_smul]

/-- The linear part of step `t`, as a linear map. -/
def vlinMap (t : ℕ) : (Fin L → F) →ₗ[F] (Fin m → F) where
  toFun w := net.vlin w t
  map_add' w w' := net.vlin_add w w' t
  map_smul' c w := net.vlin_smul c w t

/-! ### Paths and path sums -/

/-- The paths `t = t₀ → t₁ → ⋯ → t_n` of the network from `t`, as lists. -/
def paths (t : ℕ) : Finset (List ℕ) :=
  insert [t] ((net.out t).attach.biUnion fun s => (paths s.1).image (List.cons t))
termination_by t
decreasing_by exact net.out_lt t s.1 s.2

/-- The weight `W(π)` of a path: the product of the matrices along it. -/
def wt : List ℕ → Matrix (Fin m) (Fin m) F
  | [] => 1
  | [_] => 1
  | t :: s :: π => net.A t s * wt (s :: π)

/-- A path is `Γ`-free if no vertex after the first lies in `Γ`. -/
def GFree (Γ : Finset ℕ) (π : List ℕ) : Prop := ∀ v ∈ π.tail, v ∉ Γ

instance (Γ : Finset ℕ) : DecidablePred (GFree Γ) := fun π => by unfold GFree; infer_instance

open Classical in
/-- **The path sum** `C_{t,j}`: `W(π) a(t_n)` summed over the `Γ`-free paths from `t` whose last
step reads position `j`. -/
noncomputable def C (Γ : Finset ℕ) (t : ℕ) (j : Fin L) : Fin m → F :=
  ∑ π ∈ (net.paths t).filter (fun π => GFree Γ π ∧ net.rd (π.getLastD t) = some j),
    net.wt π *ᵥ net.a (π.getLastD t)

open Classical in
/-- The positions read at the ends of the `Γ`-free paths with at most `D` edges from `t`. -/
noncomputable def reach (Γ : Finset ℕ) (D t : ℕ) : Finset (Fin L) :=
  univ.filter fun j => ∃ π ∈ net.paths t, GFree Γ π ∧ π.length ≤ D + 1 ∧
    net.rd (π.getLastD t) = some j

/-- `I^D_Γ ⊆ B^D`: the ball set is the reach of the empty genie. -/
theorem reach_subset (Γ : Finset ℕ) (D t : ℕ) : net.reach Γ D t ⊆ net.reach ∅ D t := by
  intro j hj
  simp only [reach, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, -, hlen, hrd⟩ := hj
  exact ⟨π, hπ, fun v _ => Finset.notMem_empty v, hlen, hrd⟩

theorem paths_eq (t : ℕ) :
    net.paths t = insert [t] ((net.out t).biUnion fun s => (net.paths s).image (List.cons t)) := by
  rw [paths]
  congr 1
  ext π
  simp only [mem_biUnion, mem_attach, true_and, Subtype.exists, exists_prop]

theorem mem_paths_head {t : ℕ} : ∀ {π : List ℕ}, π ∈ net.paths t → ∃ π', π = t :: π' := by
  intro π hπ
  rw [paths_eq] at hπ
  rcases mem_insert.mp hπ with rfl | hπ
  · exact ⟨[], rfl⟩
  · obtain ⟨s, -, hs⟩ := mem_biUnion.mp hπ
    obtain ⟨π', -, rfl⟩ := mem_image.mp hs
    exact ⟨π', rfl⟩

theorem getLastD_cons_cons (t s : ℕ) (π : List ℕ) :
    (t :: s :: π).getLastD t = (s :: π).getLastD s := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_cons_cons]
  cases h : (s :: π).getLast? with
  | none => simp at h
  | some x => rfl

/-- **The recursion of the path sums.** -/
theorem C_eq (Γ : Finset ℕ) (t : ℕ) (j : Fin L) :
    net.C Γ t j = (if net.rd t = some j then net.a t else 0) +
      ∑ s ∈ (net.out t).filter (· ∉ Γ), net.A t s *ᵥ net.C Γ s j := by
  classical
  unfold C
  rw [paths_eq, filter_insert]
  have hnot : [t] ∉ (net.out t).biUnion fun s => (net.paths s).image (List.cons t) := by
    intro h
    obtain ⟨s, -, hs⟩ := mem_biUnion.mp h
    obtain ⟨π', hπ', he⟩ := mem_image.mp hs
    obtain ⟨π'', rfl⟩ := net.mem_paths_head hπ'
    simp at he
  have hfree : GFree Γ [t] := fun v hv => by simp at hv
  have hlast : [t].getLastD t = t := rfl
  split_ifs with h1 h2 h2
  · rw [sum_insert (fun h => hnot (mem_filter.mp h).1)]
    congr 1
    · simp [wt]
    · exact sum_biUnion_part net Γ t j
  · exact absurd (by simpa [hlast] using h1.2) h2
  · exact absurd ⟨hfree, by simpa [hlast] using h2⟩ h1
  · rw [zero_add]
    exact sum_biUnion_part net Γ t j
where
  sum_biUnion_part (net : LinNet F L m) (Γ : Finset ℕ) (t : ℕ) (j : Fin L) :
      ∑ π ∈ ((net.out t).biUnion fun s => (net.paths s).image (List.cons t)).filter
          (fun π => GFree Γ π ∧ net.rd (π.getLastD t) = some j),
        net.wt π *ᵥ net.a (π.getLastD t) =
      ∑ s ∈ (net.out t).filter (· ∉ Γ), net.A t s *ᵥ
        ∑ π ∈ (net.paths s).filter (fun π => GFree Γ π ∧ net.rd (π.getLastD s) = some j),
          net.wt π *ᵥ net.a (π.getLastD s) := by
    classical
    rw [filter_biUnion, sum_biUnion]
    · rw [sum_filter]
      refine sum_congr rfl fun s _ => ?_
      rw [filter_image, sum_image (fun x _ y _ h => List.cons_injective h)]
      by_cases hs : s ∈ Γ
      · simp only [hs, not_true_eq_false, ↓reduceIte]
        refine sum_eq_zero fun π hπ => ?_
        exfalso
        obtain ⟨hπ, hfree, -⟩ := mem_filter.mp hπ
        obtain ⟨π', rfl⟩ := net.mem_paths_head hπ
        exact hfree s (by simp) hs
      · simp only [hs, not_false_eq_true, ↓reduceIte]
        rw [Matrix.mulVec_sum]
        refine sum_congr ?_ fun π hπ => ?_
        · ext π
          simp only [mem_filter]
          constructor
          · rintro ⟨hπ, hfree, hrd⟩
            obtain ⟨π', rfl⟩ := net.mem_paths_head hπ
            refine ⟨hπ, fun v hv => hfree v (by
              simp only [List.tail_cons] at hv ⊢; exact List.mem_cons_of_mem _ hv), ?_⟩
            rwa [getLastD_cons_cons] at hrd
          · rintro ⟨hπ, hfree, hrd⟩
            obtain ⟨π', rfl⟩ := net.mem_paths_head hπ
            refine ⟨hπ, fun v hv => ?_, ?_⟩
            · simp only [List.tail_cons, List.mem_cons] at hv
              rcases hv with rfl | hv
              · exact hs
              · exact hfree v (by simpa using hv)
            · rwa [getLastD_cons_cons]
        · obtain ⟨π', rfl⟩ := net.mem_paths_head (mem_filter.mp hπ).1
          simp only [wt, getLastD_cons_cons, Matrix.mulVec_mulVec]
    · intro s _ s' _ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro π h1 h2
      obtain ⟨π1, hπ1, rfl⟩ := mem_image.mp (mem_filter.mp h1).1
      obtain ⟨π2, hπ2, he⟩ := mem_image.mp (mem_filter.mp h2).1
      obtain ⟨π1', rfl⟩ := net.mem_paths_head hπ1
      obtain ⟨π2', rfl⟩ := net.mem_paths_head hπ2
      simp only [List.cons.injEq] at he
      exact hne he.2.1.symm

/-! ### The expansion through the genie -/

/-- The transfer matrices `T_{t,s}` to a genie step `s`: the path sums of `W(π)` over the paths from
`t` to `s` with at least one edge whose interior avoids `Γ`, computed by their recursion. -/
def Tm (Γ : Finset ℕ) (s : ℕ) (t : ℕ) : Matrix (Fin m) (Fin m) F :=
  ∑ s' ∈ (net.out t).attach,
    (if s'.1 ∈ Γ then (if s'.1 = s then net.A t s'.1 else 0) else net.A t s'.1 * Tm Γ s s'.1)
termination_by t
decreasing_by exact net.out_lt t s'.1 s'.2

theorem Tm_eq (Γ : Finset ℕ) (s t : ℕ) :
    net.Tm Γ s t = ∑ s' ∈ net.out t,
      (if s' ∈ Γ then (if s' = s then net.A t s' else 0) else net.A t s' * net.Tm Γ s s') := by
  rw [Tm, Finset.sum_attach (net.out t)
    (fun s' => if s' ∈ Γ then (if s' = s then net.A t s' else 0) else net.A t s' * net.Tm Γ s s')]

theorem inp_eq_sum (w : Fin L → F) (t : ℕ) :
    net.inp w t = ∑ j, w j • (if net.rd t = some j then net.a t else 0) := by
  unfold inp
  cases net.rd t with
  | none => simp
  | some j0 => simp [smul_ite, Finset.sum_ite_eq]

/-- **Expansion.** The linear part of a step is the transfer of the genie values plus the input
contributions of the `Γ`-free paths: `vlin_t(w) = ∑_{s ∈ Γ} T_{t,s} vlin_s(w) + ∑_j w_j C_{t,j}`. -/
theorem vlin_expand (Γ : Finset ℕ) (w : Fin L → F) : ∀ t,
    net.vlin w t = ∑ s ∈ Γ, net.Tm Γ s t *ᵥ net.vlin w s + ∑ j, w j • net.C Γ t j := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    have hT : ∑ s ∈ Γ, net.Tm Γ s t *ᵥ net.vlin w s =
        ∑ s' ∈ net.out t, (if s' ∈ Γ then net.A t s' *ᵥ net.vlin w s'
          else net.A t s' *ᵥ ∑ s ∈ Γ, net.Tm Γ s s' *ᵥ net.vlin w s) := by
      simp only [net.Tm_eq Γ _ t, Matrix.sum_mulVec]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      by_cases h : s' ∈ Γ
      · simp only [h, ↓reduceIte]
        rw [Finset.sum_congr rfl (fun x _ => show (if s' = x then net.A t s' else 0) *ᵥ net.vlin w x =
          (if s' = x then net.A t s' *ᵥ net.vlin w x else 0) by split_ifs <;> simp),
          Finset.sum_ite_eq]
        simp [h]
      · simp only [h, ↓reduceIte, Matrix.mulVec_sum, Matrix.mulVec_mulVec]
    have hC : ∑ j, w j • net.C Γ t j = net.inp w t +
        ∑ s' ∈ (net.out t).filter (· ∉ Γ), net.A t s' *ᵥ ∑ j, w j • net.C Γ s' j := by
      simp only [net.C_eq Γ t, smul_add, Finset.sum_add_distrib, ← net.inp_eq_sum]
      congr 1
      simp only [Finset.smul_sum, Matrix.mulVec_sum, Matrix.mulVec_smul]
      exact Finset.sum_comm
    have hu : ∀ s' ∈ net.out t, net.A t s' *ᵥ net.vlin w s' =
        (if s' ∈ Γ then net.A t s' *ᵥ net.vlin w s'
          else net.A t s' *ᵥ ∑ s ∈ Γ, net.Tm Γ s s' *ᵥ net.vlin w s) +
        (if s' ∈ Γ then 0 else net.A t s' *ᵥ ∑ j, w j • net.C Γ s' j) := by
      intro s' hs'
      by_cases h : s' ∈ Γ
      · simp [h]
      · simp only [h, ↓reduceIte]
        rw [← Matrix.mulVec_add, ← ih s' (net.out_lt t s' hs')]
    rw [net.vlin_eq w t, hT, hC, Finset.sum_congr rfl hu, Finset.sum_add_distrib,
      Finset.sum_filter]
    simp only [ite_not]
    abel

/-! ### Counting values on binary inputs -/

open Classical in
/-- The binary vectors `{0, 1}^L` in `F^L`. -/
noncomputable def binVecs (L : ℕ) (F : Type*) [Field F] : Finset (Fin L → F) :=
  Fintype.piFinset fun _ => ({0, 1} : Finset F)

/-- **A linear map of rank `ρ` takes at least `2^ρ` values on the binary vectors**: on the binary
vectors supported on `ρ` coordinates with independent columns it is injective. -/
theorem two_pow_finrank_le {W : Type*} [AddCommGroup W] [Module F W] [DecidableEq W]
    (E : (Fin L → F) →ₗ[F] W) :
    2 ^ finrank F (LinearMap.range E) ≤ ((binVecs L F).image E).card := by
  classical
  set col : Fin L → W := fun j => E (Pi.single j 1)
  have hrange : LinearMap.range E = Submodule.span F (Set.range col) := by
    apply le_antisymm
    · rintro x ⟨w, rfl⟩
      have : w = ∑ j, w j • (Pi.single j 1 : Fin L → F) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      rw [this, map_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨_, rfl⟩
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F col
  have : Fintype κ := Fintype.ofInjective a ha
  have hcard : finrank F (LinearMap.range E) = Fintype.card κ := by
    rw [hrange, ← hspan, finrank_span_eq_card hli]
  rw [hcard]
  -- the binary vectors supported on the image of `a`
  let vec : Finset κ → Fin L → F := fun S => ∑ k ∈ S, (Pi.single (a k) 1 : Fin L → F)
  have hvec : ∀ S, vec S ∈ binVecs L F := by
    intro S
    refine Fintype.mem_piFinset.mpr fun j => ?_
    have hle : (S.filter fun k => a k = j).card ≤ 1 :=
      card_le_one.mpr fun k hk k' hk' => ha ((mem_filter.mp hk).2.trans (mem_filter.mp hk').2.symm)
    have : vec S j = ((S.filter fun k => a k = j).card : F) := by
      simp only [vec, Finset.sum_apply, Pi.single_apply, Finset.sum_boole, eq_comm]
    rw [this]
    interval_cases (S.filter fun k => a k = j).card <;> simp
  have hEvec : ∀ S, E (vec S) = ∑ k, (if k ∈ S then (1 : F) else 0) • col (a k) := by
    intro S
    simp only [vec, map_sum, ite_smul, one_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter,
      col]
  have hinj : Set.InjOn (fun S => E (vec S)) (univ : Finset (Finset κ)) := by
    intro S _ S' _ h
    simp only [hEvec] at h
    have h0 : ∑ k, ((if k ∈ S then (1 : F) else 0) - (if k ∈ S' then 1 else 0)) • col (a k) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    have hcoef := Fintype.linearIndependent_iff.mp hli _ h0
    ext k
    have := hcoef k
    by_cases hS : k ∈ S <;> by_cases hS' : k ∈ S' <;> simp_all
  calc 2 ^ Fintype.card κ = (univ : Finset (Finset κ)).card := by
        rw [card_univ, Fintype.card_finset]
    _ = ((univ : Finset (Finset κ)).image fun S => E (vec S)).card := (card_image_of_injOn hinj).symm
    _ ≤ ((binVecs L F).image E).card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨S, -, rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨vec S, hvec S, rfl⟩

/-! ### Rigidity -/

/-- The demand matrix `P_tpos`: row `ℓ` is the unit vector `e_{tpos ℓ}`. -/
def Pmat (tpos : Fin L → Fin L) : Matrix (Fin L) (Fin L) F :=
  Matrix.of fun ℓ j => if j = tpos ℓ then 1 else 0

open Classical in
/-- **Per-machine rigidity**. Let the network transpose on binary inputs, output `ℓ`
being the affine functional `φc ℓ + φ ℓ ⬝ᵥ ·` of the value at step `tout ℓ`. Let each step of the
genie `Γ` take at most `2^β` values on binary inputs, and let every output have linear depth at
most `D` for `Γ`: `φ ℓ ⬝ᵥ C_{tout ℓ, j} = 0` for `j` outside `I^D_Γ(ℓ)`. Then `P_tpos = R + S` with
`rank R ≤ β |Γ|` and row `ℓ` of `S` supported in `I^D_Γ(ℓ)`. -/
theorem rigidity (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L) (β : ℕ) (Γ : Finset ℕ) (D : ℕ)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ))
    (hval : ∀ s ∈ Γ, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (hdepth : ∀ ℓ, ∀ j ∉ net.reach Γ D (tout ℓ), φ ℓ ⬝ᵥ net.C Γ (tout ℓ) j = 0) :
    ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧ R.rank ≤ β * Γ.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → j ∈ net.reach Γ D (tout ℓ) := by
  -- the revealed linear parts and the transfer to the outputs
  let E : (Fin L → F) →ₗ[F] (Γ → Fin m → F) := LinearMap.pi fun s => net.vlinMap s.1
  let G : (Γ → Fin m → F) →ₗ[F] (Fin L → F) :=
    { toFun := fun e ℓ => ∑ s : Γ, φ ℓ ⬝ᵥ (net.Tm Γ s (tout ℓ) *ᵥ e s)
      map_add' := fun e e' => by
        funext ℓ
        simp only [Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]
      map_smul' := fun c e => by
        funext ℓ
        simp only [Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum] }
  let R : Matrix (Fin L) (Fin L) F := LinearMap.toMatrix' (G ∘ₗ E)
  let S : Matrix (Fin L) (Fin L) F := Matrix.of fun ℓ j => φ ℓ ⬝ᵥ net.C Γ (tout ℓ) j
  refine ⟨R, S, ?_, ?_, ?_⟩
  · -- `P = R + S`, read off at the unit vectors
    ext ℓ j
    have hb : ∀ w : Fin L → F, (∀ i, w i = 0 ∨ w i = 1) → w ∈ binVecs L F := fun w hw =>
      Fintype.mem_piFinset.mpr fun i => by rcases hw i with h | h <;> simp [h]
    have h0 := htrans 0 (hb 0 fun _ => Or.inl rfl) ℓ
    have hj := htrans (Pi.single j 1) (hb _ fun i => by
      by_cases h : i = j
      · subst h; simp
      · simp [h]) ℓ
    rw [net.val_eq_add (Pi.single j 1) (tout ℓ), dotProduct_add] at hj
    have hlin : φ ℓ ⬝ᵥ net.vlin (Pi.single j 1) (tout ℓ) = (Pi.single j 1 : Fin L → F) (tpos ℓ) := by
      have : φc ℓ + φ ℓ ⬝ᵥ net.val 0 (tout ℓ) = 0 := by simpa using h0
      linear_combination hj - this
    rw [net.vlin_expand Γ (Pi.single j 1) (tout ℓ), dotProduct_add, dotProduct_sum] at hlin
    have hsum : ∑ j', (Pi.single j 1 : Fin L → F) j' • net.C Γ (tout ℓ) j' = net.C Γ (tout ℓ) j := by
      rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj'])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp
    rw [hsum] at hlin
    simp only [Pmat, Matrix.of_apply, Matrix.add_apply, R, S, LinearMap.toMatrix'_apply,
      LinearMap.comp_apply]
    rw [show (if j = tpos ℓ then (1 : F) else 0) = (Pi.single j 1 : Fin L → F) (tpos ℓ) by
      simp [Pi.single_apply, eq_comm], ← hlin]
    congr 1
    simp only [G, E, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply, vlinMap,
      LinearMap.coe_mk, AddHom.coe_mk]
    exact (Finset.sum_coe_sort Γ fun s => φ ℓ ⬝ᵥ (net.Tm Γ s (tout ℓ) *ᵥ net.vlin (Pi.single j 1) s)).symm
  · -- `rank R ≤ rank E ≤ β |Γ|`
    have hR : R.mulVecLin = G ∘ₗ E := by
      rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    have h1 : R.rank ≤ finrank F (LinearMap.range E) := by
      change finrank F (LinearMap.range R.mulVecLin) ≤ _
      rw [hR, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    have h2 := two_pow_finrank_le E
    have h3 : ((binVecs L F).image E).card ≤ 2 ^ (β * Γ.card) := by
      calc ((binVecs L F).image E).card
          ≤ (Fintype.piFinset fun s : Γ => (binVecs L F).image fun w => net.vlin w s.1).card := by
            refine card_le_card fun x hx => ?_
            obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
            exact Fintype.mem_piFinset.mpr fun s => mem_image.mpr ⟨w, hw, rfl⟩
        _ = ∏ s : Γ, ((binVecs L F).image fun w => net.vlin w s.1).card := Fintype.card_piFinset _
        _ ≤ ∏ _s : Γ, 2 ^ β := by
            refine Finset.prod_le_prod fun s _ => ?_
            have : (binVecs L F).image (fun w => net.vlin w s.1) =
                ((binVecs L F).image fun w => net.val w s.1).image (· - net.val 0 s.1) := by
              rw [Finset.image_image]
              refine Finset.image_congr fun w _ => ?_
              simp only [Function.comp_apply, net.val_eq_add w s.1, add_sub_cancel_left]
            rw [this]
            exact card_image_le.trans (hval s.1 s.2)
        _ = 2 ^ (β * Γ.card) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
    have h4 : 2 ^ finrank F (LinearMap.range E) ≤ 2 ^ (β * Γ.card) := h2.trans h3
    have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
    omega
  · intro ℓ j hS
    by_contra hj
    exact hS (hdepth ℓ j hj)

/-- The minrank of a system `I` for the demands `tpos`: the least rank of a matrix `R` such that
row `ℓ` of `P_tpos - R` is supported in `I ℓ`. -/
noncomputable def minrank (F : Type*) [Field F] (tpos : Fin L → Fin L)
    (I : Fin L → Finset (Fin L)) : ℕ :=
  sInf {r | ∃ R : Matrix (Fin L) (Fin L) F, R.rank = r ∧
    ∀ ℓ j, (Pmat (F := F) tpos - R) ℓ j ≠ 0 → j ∈ I ℓ}

open Classical in
/-- **Rigidity, minrank form.** Under the hypotheses of `rigidity`, the system `I^D_Γ`, and hence
the ball system `B^D`, has minrank at most `β |Γ|`. -/
theorem minrank_le (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L) (β : ℕ) (Γ : Finset ℕ) (D : ℕ)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ))
    (hval : ∀ s ∈ Γ, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (hdepth : ∀ ℓ, ∀ j ∉ net.reach Γ D (tout ℓ), φ ℓ ⬝ᵥ net.C Γ (tout ℓ) j = 0) :
    minrank F tpos (fun ℓ => net.reach Γ D (tout ℓ)) ≤ β * Γ.card ∧
      minrank F tpos (fun ℓ => net.reach ∅ D (tout ℓ)) ≤ β * Γ.card := by
  obtain ⟨R, S, hPRS, hrank, hsupp⟩ := net.rigidity tout φ φc tpos β Γ D htrans hval hdepth
  have hsub : Pmat tpos - R = S := by rw [hPRS]; abel
  have hmem1 : R.rank ∈ {r : ℕ | ∃ R' : Matrix (Fin L) (Fin L) F, R'.rank = r ∧
      ∀ ℓ j, (Pmat (F := F) tpos - R') ℓ j ≠ 0 → j ∈ net.reach Γ D (tout ℓ)} :=
    ⟨R, rfl, fun ℓ j h => hsupp ℓ j (by rwa [hsub] at h)⟩
  have hmem2 : R.rank ∈ {r : ℕ | ∃ R' : Matrix (Fin L) (Fin L) F, R'.rank = r ∧
      ∀ ℓ j, (Pmat (F := F) tpos - R') ℓ j ≠ 0 → j ∈ net.reach ∅ D (tout ℓ)} :=
    ⟨R, rfl, fun ℓ j h => net.reach_subset Γ D _ (hsupp ℓ j (by rwa [hsub] at h))⟩
  exact ⟨(Nat.sInf_le hmem1).trans hrank, (Nat.sInf_le hmem2).trans hrank⟩

open Classical in
/-- **Theorem `D_lin` at one size.** If the ball system `B^D` has minrank at least `(ρ - η) L`, with
`η = (ρ - ε)/2`, then no genie of cost `β |Γ| ≤ ε L` makes every output of a transposing network
linearly `D`-shallow. -/
theorem dlin_step (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L) (β : ℕ) (Γ : Finset ℕ) (D : ℕ) {ε ρ : ℝ} (hερ : ε < ρ) (hL : 1 ≤ L)
    (hcrux : (ρ - (ρ - ε) / 2) * L ≤ minrank F tpos (fun ℓ => net.reach ∅ D (tout ℓ)))
    (hcost : (β * Γ.card : ℝ) ≤ ε * L)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ))
    (hval : ∀ s ∈ Γ, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (hdepth : ∀ ℓ, ∀ j ∉ net.reach Γ D (tout ℓ), φ ℓ ⬝ᵥ net.C Γ (tout ℓ) j = 0) : False := by
  have h := (net.minrank_le tout φ φc tpos β Γ D htrans hval hdepth).2
  have h' : (minrank F tpos (fun ℓ => net.reach ∅ D (tout ℓ)) : ℝ) ≤ β * Γ.card := by
    exact_mod_cast h
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith

end LinNet

end BoundedNesting
