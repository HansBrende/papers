import MergeDepth.Charging

/-!
# The coordinate network of a linear data path

A linear network `net` of width `m` (the data path of an oblivious machine, as in the eighth paper)
has a *coordinate network* `coordNet net hm` of width one: vertex `t * m + i` is coordinate `i` of
step `t`. It has an edge to coordinate `i'` of an out-neighbour `s` of `t` exactly when the
coefficient `A t s i i'` is nonzero, and it reads the position read by step `t` exactly when its input
coefficient `a t i` is nonzero.

* `coord_val`: the coordinate network computes the coordinates of the step values.
* `coord_paths`: its paths project to paths of `net` (divide by `m`), with the same length.
* `coord_reach_subset`: hence its balls lie in the balls of `net`.
-/

namespace MergeDepth

open Finset Matrix Module BoundedNesting BoundedNesting.LinNet

variable {F : Type*} [Field F] {L m : ℕ}

/-- The coordinate of a vertex of the coordinate network. -/
def crd (hm : 0 < m) (u : ℕ) : Fin m := ⟨u % m, Nat.mod_lt _ hm⟩

theorem div_mul_add_crd (hm : 0 < m) (u : ℕ) : u / m * m + (crd hm u : ℕ) = u := by
  simp only [crd]
  rw [mul_comm]
  exact Nat.div_add_mod u m

theorem enc_div (hm : 0 < m) (t : ℕ) (i : Fin m) : (t * m + i) / m = t := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt i.2, zero_add]

theorem crd_enc (hm : 0 < m) (t : ℕ) (i : Fin m) : crd hm (t * m + i) = i := by
  ext
  simp only [crd]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.2]

theorem enc_lt_of_lt {s t : ℕ} (hst : s < t) (i' : Fin m) (u : ℕ) (hu : u / m = t) :
    s * m + i' < u := by
  have h1 : s * m + i' < (s + 1) * m := by rw [Nat.succ_mul]; have := i'.2; omega
  have h2 : (s + 1) * m ≤ t * m := Nat.mul_le_mul_right _ hst
  have h3 : t * m ≤ u := by rw [← hu]; exact Nat.div_mul_le_self u m
  omega

open Classical in
/-- The out-neighbours of coordinate vertex `u`. -/
noncomputable def coordOut (net : LinNet F L m) (hm : 0 < m) (u : ℕ) : Finset ℕ :=
  (net.out (u / m)).biUnion fun s =>
    ((univ : Finset (Fin m)).filter fun i' : Fin m => net.A (u / m) s (crd hm u) i' ≠ 0).image
      fun i' : Fin m => s * m + (i' : ℕ)

theorem mem_coordOut {net : LinNet F L m} {hm : 0 < m} {u v : ℕ} :
    v ∈ coordOut net hm u ↔ v / m ∈ net.out (u / m) ∧
      net.A (u / m) (v / m) (crd hm u) (crd hm v) ≠ 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨s, hs, hv⟩ := mem_biUnion.mp hv
    obtain ⟨i', hi', rfl⟩ := mem_image.mp hv
    rw [enc_div hm, crd_enc hm]
    exact ⟨hs, (mem_filter.mp hi').2⟩
  · rintro ⟨hs, hA⟩
    refine mem_biUnion.mpr ⟨v / m, hs, mem_image.mpr ⟨crd hm v, mem_filter.mpr ⟨mem_univ _, hA⟩, ?_⟩⟩
    exact div_mul_add_crd hm v

open Classical in
/-- **The coordinate network** of a linear network of width `m ≥ 1`. -/
noncomputable def coordNet (net : LinNet F L m) (hm : 0 < m) : LinNet F L 1 where
  out := coordOut net hm
  out_lt u v hv := by
    obtain ⟨hs, -⟩ := mem_coordOut.mp hv
    have := enc_lt_of_lt (net.out_lt _ _ hs) (crd hm v) u rfl
    rwa [div_mul_add_crd hm v] at this
  c u := fun _ => net.c (u / m) (crd hm u)
  A u v := fun _ _ => net.A (u / m) (v / m) (crd hm u) (crd hm v)
  a u := fun _ => net.a (u / m) (crd hm u)
  rd u := if net.a (u / m) (crd hm u) ≠ 0 then net.rd (u / m) else none

/-- **The coordinate network computes the coordinates of the step values.** -/
theorem coord_val (net : LinNet F L m) (hm : 0 < m) (w : Fin L → F) :
    ∀ u, (coordNet net hm).val w u 0 = net.val w (u / m) (crd hm u) := by
  classical
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    have hsum : (∑ v ∈ (coordNet net hm).out u,
        (coordNet net hm).A u v *ᵥ (coordNet net hm).val w v) 0 =
        (∑ s ∈ net.out (u / m), net.A (u / m) s *ᵥ net.val w s) (crd hm u) := by
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      change ∑ v ∈ coordOut net hm u, net.A (u / m) (v / m) (crd hm u) (crd hm v) *
          (coordNet net hm).val w v 0 = _
      unfold coordOut
      rw [sum_biUnion]
      · refine sum_congr rfl fun s hs => ?_
        rw [sum_image (fun i _ j _ h => Fin.ext (by simpa using h))]
        rw [sum_filter]
        refine sum_congr rfl fun i' _ => ?_
        have hlt : s * m + i' < u := enc_lt_of_lt (net.out_lt _ _ hs) i' u rfl
        rw [ih _ hlt, enc_div hm, crd_enc hm]
        split_ifs with h
        · rfl
        · push Not at h
          rw [h, zero_mul]
      · intro s _ s' _ hne
        simp only [Function.onFun]
        rw [disjoint_left]
        intro v h1 h2
        obtain ⟨i, -, rfl⟩ := mem_image.mp h1
        obtain ⟨i', -, he⟩ := mem_image.mp h2
        have := congr_arg (· / m) he
        simp only [enc_div hm] at this
        exact hne this.symm
    have hinp : (coordNet net hm).inp w u 0 = net.inp w (u / m) (crd hm u) := by
      simp only [LinNet.inp, coordNet]
      by_cases ha : net.a (u / m) (crd hm u) = 0
      · simp only [ha, ne_eq, not_true_eq_false, ↓reduceIte, Pi.zero_apply]
        cases net.rd (u / m) <;> simp [ha]
      · simp only [ha, ne_eq, not_false_eq_true, ↓reduceIte]
        cases net.rd (u / m) <;> simp
    rw [(coordNet net hm).val_eq w u, net.val_eq w (u / m)]
    simp only [Pi.add_apply, hsum, hinp]
    rfl

theorem coord_out {net : LinNet F L m} {hm : 0 < m} {u v : ℕ} (h : v ∈ (coordNet net hm).out u) :
    v / m ∈ net.out (u / m) :=
  (mem_coordOut.mp h).1

/-- **Coordinate paths project to step paths** of the same length. -/
theorem coord_paths (net : LinNet F L m) (hm : 0 < m) :
    ∀ (π : List ℕ) (u : ℕ), π ∈ (coordNet net hm).paths u → π.map (· / m) ∈ net.paths (u / m)
  | [], u, h => by
    obtain ⟨π', hπ'⟩ := (coordNet net hm).mem_paths_head h
    simp at hπ'
  | [v], u, h => by
    have := head_eq_of_mem_paths h
    subst this
    exact singleton_mem_paths _ _
  | v :: v' :: π, u, h => by
    have := head_eq_of_mem_paths h
    subst this
    obtain ⟨hv', hπ⟩ := cons_cons_mem_paths.mp h
    exact cons_cons_mem_paths.mpr ⟨coord_out hv', coord_paths net hm (v' :: π) v' hπ⟩

/-- The coordinates of the steps of a genie. -/
def coordGenie (m : ℕ) (Γ : Finset ℕ) : Finset ℕ :=
  Γ.biUnion fun t => (univ : Finset (Fin m)).image fun i : Fin m => t * m + (i : ℕ)

theorem mem_coordGenie (hm : 0 < m) {Γ : Finset ℕ} {u : ℕ} : u ∈ coordGenie m Γ ↔ u / m ∈ Γ := by
  constructor
  · intro h
    obtain ⟨t, ht, h⟩ := mem_biUnion.mp h
    obtain ⟨i, -, rfl⟩ := mem_image.mp h
    rwa [enc_div hm]
  · intro h
    exact mem_biUnion.mpr ⟨u / m, h, mem_image.mpr ⟨crd hm u, mem_univ _, div_mul_add_crd hm u⟩⟩

theorem card_coordGenie_le (Γ : Finset ℕ) : (coordGenie m Γ).card ≤ m * Γ.card := by
  unfold coordGenie
  refine card_biUnion_le.trans ?_
  calc ∑ t ∈ Γ, ((univ : Finset (Fin m)).image fun i : Fin m => t * m + (i : ℕ)).card
      ≤ ∑ _t ∈ Γ, m := sum_le_sum fun t _ => card_image_le.trans (by simp)
    _ = m * Γ.card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem gfree_coord (hm : 0 < m) {Γ : Finset ℕ} {π : List ℕ} :
    LinNet.GFree (coordGenie m Γ) π ↔ LinNet.GFree Γ (π.map (· / m)) := by
  cases π with
  | nil => simp [LinNet.GFree]
  | cons v π =>
    simp only [LinNet.GFree, List.tail_cons, List.map_cons, List.mem_map, mem_coordGenie hm]
    constructor
    · rintro h _ ⟨x, hx, rfl⟩
      exact h x hx
    · intro h x hx
      exact h _ ⟨x, hx, rfl⟩

theorem rCount_coord (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] :
    ∀ π : List ℕ, rCount (fun u v => Rr (u / m) (v / m)) π = rCount Rr (π.map (· / m))
  | [] => rfl
  | [_] => rfl
  | u :: v :: π => by
    simp only [rCount, List.map_cons]
    rw [rCount_coord Rr (v :: π)]
    rfl

theorem getLastD_map (f : ℕ → ℕ) (π : List ℕ) (u : ℕ) :
    (π.map f).getLastD (f u) = f (π.getLastD u) := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map]
  cases π.getLast? <;> rfl

/-- **Coordinate balls lie in step balls.** -/
theorem coord_reach_subset (net : LinNet F L m) (hm : 0 < m) (D u : ℕ) :
    (coordNet net hm).reach ∅ D u ⊆ net.reach ∅ D (u / m) := by
  classical
  intro j hj
  simp only [LinNet.reach, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, -, hlen, hrd⟩ := hj
  refine ⟨π.map (· / m), coord_paths net hm π u hπ, fun v _ => Finset.notMem_empty v, by simpa using hlen,
    ?_⟩
  rw [getLastD_map (· / m) π u]
  simp only [coordNet] at hrd
  split_ifs at hrd with ha
  · exact hrd

end MergeDepth
