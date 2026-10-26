import MotionDepthCodes.Polymatroid

/-!
# Relative elimination with nested outside charges (Lemma E)

This file proves the engine of the decomposition theorem (Lemma E of the paper): the exact
partition identity of the circular memo of the series' fourth paper (*Conditional Elimination
and Circular Storage Codes*), extended by closure through one outside vertex and by a nesting
condition on the steps charged to the same outside vertex.

* `elim_defect` (E0): along any elimination list, `2 g H` is at most the sum of the part
  records plus the total *defect* `Σ_t g(v_t | S_t ∪ P_{b(t)})`. No disjointness of the parts
  is needed; each step needs only `v_t ∈ P_{a(t)}` and `a(t) ≠ b(t)`.
* `totalDefect_le` (E1): if every defect is either zero or explained by one outside vertex
  `w`, and the steps charged to the same `w` are nested, the total defect is at most
  `Σ_w I(w; H)`.
* `nested_elimination` (Lemma E): the combination.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V]

section Defect

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The defect of eliminating `v` with revealed set `S` and supplying record `R`:
the conditional value `g(v | S ∪ R)`. -/
def defect (g : Finset V → ℝ) (S R : Finset V) (v : V) : ℝ :=
  g (insert v (S ∪ R)) - g (S ∪ R)

/-- The total defect along an elimination list, starting from the revealed set `S`. -/
def totalDefect (g : Finset V → ℝ) (P : ι → Finset V) (b : V → ι) : Finset V → List V → ℝ
  | _, [] => 0
  | S, v :: l => defect g S (P (b v)) v + totalDefect g P b (insert v S) l

/-- Adding one element to the revealed set raises any record by at most its increment. -/
theorem record_increment {g : Finset V → ℝ} (hg : IsPolymatroid g) (S R : Finset V) (v : V) :
    g (insert v S ∪ R) - g (S ∪ R) ≤ g (insert v S) - g S := by
  have h := hg.elemental (A := S ∪ R) (B := insert v S) (U := insert v S ∪ R) (I := S)
    (by ext x; simp only [mem_union, mem_insert]; tauto)
    (subset_inter subset_union_left (subset_insert v S))
  linarith

/-- The one-step inequality of the partition identity: when `v` (in its own record `P a`) is
revealed, the sum of the records grows by at most the defect for the supplying record `P b`
plus `(card ι - 2)` times the growth of the revealed set. -/
theorem sum_records_step {g : Finset V → ℝ} (hg : IsPolymatroid g) (P : ι → Finset V)
    (S : Finset V) (v : V) (a b : ι) (hva : v ∈ P a) (hne : a ≠ b) :
    ∑ i, g (insert v S ∪ P i) - ∑ i, g (S ∪ P i) ≤
      defect g S (P b) v + ((Fintype.card ι : ℝ) - 2) * (g (insert v S) - g S) := by
  set δ := g (insert v S) - g S with hδ
  have hΔa : g (insert v S ∪ P a) = g (S ∪ P a) := by
    rw [insert_union, insert_eq_of_mem (mem_union_right S hva)]
  have hΔb : g (insert v S ∪ P b) - g (S ∪ P b) = defect g S (P b) v := by
    simp [defect, insert_union]
  have hother : ∀ i, g (insert v S ∪ P i) - g (S ∪ P i) ≤ δ := fun i =>
    record_increment hg S (P i) v
  have hb_mem : b ∈ (univ : Finset ι).erase a := by simp [Ne.symm hne]
  rw [← sum_sub_distrib, ← add_sum_erase _ _ (mem_univ a), hΔa, sub_self, zero_add,
    ← add_sum_erase _ _ hb_mem, hΔb]
  have hcard : (((univ : Finset ι).erase a).erase b).card = Fintype.card ι - 2 := by
    rw [card_erase_of_mem hb_mem, card_erase_of_mem (mem_univ _), card_univ]; omega
  have hcard2 : 2 ≤ Fintype.card ι := by
    have : ({a, b} : Finset ι).card ≤ Fintype.card ι := card_le_univ _
    rwa [card_pair hne] at this
  have hle : ∑ i ∈ ((univ : Finset ι).erase a).erase b, (g (insert v S ∪ P i) - g (S ∪ P i)) ≤
      ∑ i ∈ ((univ : Finset ι).erase a).erase b, δ := sum_le_sum fun i _ => hother i
  rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_sub hcard2] at hle
  push_cast at hle
  linarith

/-- **E0 (defect form of the partition identity).** -/
theorem elim_defect {g : Finset V → ℝ} (hg : IsPolymatroid g) (P : ι → Finset V)
    (a b : V → ι) (H : Finset V) (hPH : ∀ i, P i ⊆ H) :
    ∀ (l : List V) (S : Finset V), S ⊆ H → S ∪ l.toFinset = H →
      (∀ v ∈ l, v ∈ P (a v)) → (∀ v ∈ l, a v ≠ b v) →
      2 * g H + ((Fintype.card ι : ℝ) - 2) * g S ≤
        ∑ i, g (S ∪ P i) + totalDefect g P b S l := by
  intro l
  induction l with
  | nil =>
    intro S _ hSl _ _
    have hS : S = H := by simpa using hSl
    subst hS
    have hu : ∀ i, S ∪ P i = S := fun i => union_eq_left.mpr (hPH i)
    simp only [hu, sum_const, card_univ, nsmul_eq_mul, totalDefect]
    linarith
  | cons v l ih =>
    intro S hSH hSl hown hab
    have hvH : v ∈ H := by
      rw [← hSl]; simp
    have hSH' : insert v S ⊆ H := insert_subset hvH hSH
    have hSl' : insert v S ∪ l.toFinset = H := by
      rw [← hSl]; ext x; simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]; tauto
    have ih' := ih (insert v S) hSH' hSl' (fun u hu => hown u (List.mem_cons_of_mem v hu))
      (fun u hu => hab u (List.mem_cons_of_mem v hu))
    have hva : v ∈ P (a v) := hown v (List.mem_cons_self)
    have hne : a v ≠ b v := hab v (List.mem_cons_self)
    -- the key step: Σ_i Δ_i ≤ defect + (card ι - 2) δ
    set δ := g (insert v S) - g S with hδ
    have hΔa : g (insert v S ∪ P (a v)) = g (S ∪ P (a v)) := by
      rw [insert_union, insert_eq_of_mem (mem_union_right S hva)]
    have hΔb : g (insert v S ∪ P (b v)) - g (S ∪ P (b v)) = defect g S (P (b v)) v := by
      simp [defect, insert_union]
    have hother : ∀ i, g (insert v S ∪ P i) - g (S ∪ P i) ≤ δ := fun i =>
      record_increment hg S (P i) v
    have hsplit : ∑ i, (g (insert v S ∪ P i) - g (S ∪ P i)) ≤
        defect g S (P (b v)) v + ((Fintype.card ι : ℝ) - 2) * δ := by
      have hb_mem : b v ∈ (univ : Finset ι).erase (a v) := by simp [Ne.symm hne]
      rw [← add_sum_erase _ _ (mem_univ (a v)), hΔa, sub_self, zero_add,
        ← add_sum_erase _ _ hb_mem, hΔb]
      have hcard : (((univ : Finset ι).erase (a v)).erase (b v)).card =
          Fintype.card ι - 2 := by
        rw [card_erase_of_mem hb_mem, card_erase_of_mem (mem_univ _), card_univ]; omega
      have hcard2 : 2 ≤ Fintype.card ι := by
        have : ({a v, b v} : Finset ι).card ≤ Fintype.card ι := card_le_univ _
        rwa [card_pair hne] at this
      have hle : ∑ i ∈ ((univ : Finset ι).erase (a v)).erase (b v),
          (g (insert v S ∪ P i) - g (S ∪ P i)) ≤
          ∑ i ∈ ((univ : Finset ι).erase (a v)).erase (b v), δ := sum_le_sum fun i _ => hother i
      rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_sub hcard2] at hle
      push_cast at hle
      linarith
    have hsum : ∑ i, g (insert v S ∪ P i) - ∑ i, g (S ∪ P i) =
        ∑ i, (g (insert v S ∪ P i) - g (S ∪ P i)) := by rw [sum_sub_distrib]
    simp only [totalDefect]
    nlinarith [hsplit, hsum, ih']

end Defect

section Charges

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The information `I(w; X) = g{w} + g X - g(X ∪ {w})`. -/
def mi (g : Finset V → ℝ) (w : V) (X : Finset V) : ℝ := g {w} + g X - g (insert w X)

theorem mi_empty {g : Finset V → ℝ} (hg : IsPolymatroid g) (w : V) : mi g w ∅ = 0 := by
  simp [mi, hg.empty]

theorem mi_mono {g : Finset V → ℝ} (hg : IsPolymatroid g) (w : V) {X Y : Finset V}
    (hXY : X ⊆ Y) : mi g w X ≤ mi g w Y := by
  have h := hg.elemental (A := Y) (B := insert w X) (U := insert w Y) (I := X)
    (by rw [union_insert, union_eq_left.mpr hXY])
    (subset_inter hXY (subset_insert w X))
  simp only [mi]; linarith

/-- A defect explained by the outside vertex `w` is an increment of `I(w; ·)`. -/
theorem defect_eq_mi {g : Finset V → ℝ} (S R : Finset V) (v w : V)
    (hdep : g (insert v (insert w (S ∪ R))) = g (insert w (S ∪ R))) :
    defect g S R v = mi g w (insert v (S ∪ R)) - mi g w (S ∪ R) := by
  have hc : insert w (insert v (S ∪ R)) = insert v (insert w (S ∪ R)) := insert_comm w v _
  simp only [defect, mi, hc, hdep]; ring

/-- The per-step charging conditions along an elimination list. `L w` is the current lower
set for the outside vertex `w`: every later step charged to `w` must contain it in its
supplying set (nesting); after a step charged to `w` it becomes that step's set plus `v`. -/
def Charged (g : Finset V → ℝ) (P : ι → Finset V) (b : V → ι) (par : V → Option V)
    (W : Finset V) : Finset V → (V → Finset V) → List V → Prop
  | _, _, [] => True
  | S, L, v :: l =>
      match par v with
      | none => g (insert v (S ∪ P (b v))) = g (S ∪ P (b v)) ∧
          Charged g P b par W (insert v S) L l
      | some w => w ∈ W ∧ g (insert v (insert w (S ∪ P (b v)))) = g (insert w (S ∪ P (b v))) ∧
          L w ⊆ S ∪ P (b v) ∧
          Charged g P b par W (insert v S) (Function.update L w (insert v (S ∪ P (b v)))) l

omit [Fintype ι] [DecidableEq ι] in
/-- **E1 (charging).** -/
theorem totalDefect_le {g : Finset V → ℝ} (hg : IsPolymatroid g) (P : ι → Finset V)
    (b : V → ι) (par : V → Option V) (H W : Finset V) (hPH : ∀ i, P i ⊆ H) :
    ∀ (l : List V) (S : Finset V) (L : V → Finset V), S ⊆ H → (∀ v ∈ l, v ∈ H) →
      (∀ w, L w ⊆ H) → Charged g P b par W S L l →
      totalDefect g P b S l ≤ ∑ w ∈ W, (mi g w H - mi g w (L w)) := by
  intro l
  induction l with
  | nil =>
    intro S L _ _ hL _
    simp only [totalDefect]
    exact sum_nonneg fun w _ => sub_nonneg.mpr (mi_mono hg w (hL w))
  | cons v l ih =>
    intro S L hSH hlH hL hch
    have hvH : v ∈ H := hlH v List.mem_cons_self
    have hlH' : ∀ u ∈ l, u ∈ H := fun u hu => hlH u (List.mem_cons_of_mem v hu)
    have hSH' : insert v S ⊆ H := insert_subset hvH hSH
    have hQH : insert v (S ∪ P (b v)) ⊆ H :=
      insert_subset hvH (union_subset hSH (hPH (b v)))
    simp only [totalDefect]
    cases hp : par v with
    | none =>
      simp only [Charged, hp] at hch
      obtain ⟨hdep, hrest⟩ := hch
      have hd : defect g S (P (b v)) v = 0 := by simp [defect, hdep]
      have := ih (insert v S) L hSH' hlH' hL hrest
      linarith
    | some w =>
      simp only [Charged, hp] at hch
      obtain ⟨hwW, hdep, hLw, hrest⟩ := hch
      set Q := S ∪ P (b v) with hQ
      have hL' : ∀ u, Function.update L w (insert v Q) u ⊆ H := by
        intro u; by_cases hu : u = w
        · subst hu; simpa using hQH
        · simpa [Function.update_of_ne hu] using hL u
      have hih := ih (insert v S) _ hSH' hlH' hL' hrest
      have hd := defect_eq_mi S (P (b v)) v w hdep
      have hupd : ∑ u ∈ W, (mi g u H - mi g u (Function.update L w (insert v Q) u)) =
          ∑ u ∈ W, (mi g u H - mi g u (L u)) + mi g w (L w) - mi g w (insert v Q) := by
        rw [← add_sum_erase _ _ hwW, ← add_sum_erase _ _ hwW]
        have hrest_eq : ∑ u ∈ W.erase w, (mi g u H - mi g u (Function.update L w (insert v Q) u))
            = ∑ u ∈ W.erase w, (mi g u H - mi g u (L u)) := by
          apply sum_congr rfl; intro u hu
          rw [Function.update_of_ne (ne_of_mem_erase hu)]
        rw [hrest_eq, Function.update_self]; ring
      have hmono := mi_mono hg w hLw
      rw [hupd] at hih
      linarith

end Charges

section LemmaE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma E (relative elimination with nested outside charges).** Along an elimination
list `l` of the piece `H` (each `v` in its own record `P (a v)`, supplied by `P (b v)`,
`a v ≠ b v`), if every step is either determined by the revealed set and its supplying
record, or additionally by one outside vertex `w ∈ W`, with nested charges, then
`2 g H ≤ Σ_i g(P_i) + Σ_{w ∈ W} I(w; H)`. -/
theorem nested_elimination {g : Finset V → ℝ} (hg : IsPolymatroid g) (P : ι → Finset V)
    (a b : V → ι) (par : V → Option V) (H W : Finset V) (hPH : ∀ i, P i ⊆ H)
    (l : List V) (hl : l.toFinset = H) (hown : ∀ v ∈ l, v ∈ P (a v))
    (hab : ∀ v ∈ l, a v ≠ b v) (hch : Charged g P b par W ∅ (fun _ => ∅) l) :
    2 * g H ≤ ∑ i, g (P i) + ∑ w ∈ W, mi g w H := by
  have h0 := elim_defect hg P a b H hPH l ∅ (empty_subset H) (by simpa using hl) hown hab
  have hlH : ∀ v ∈ l, v ∈ H := fun v hv => by rw [← hl]; exact List.mem_toFinset.mpr hv
  have h1 := totalDefect_le hg P b par H W hPH l ∅ (fun _ => ∅) (empty_subset H) hlH
    (fun _ => empty_subset H) hch
  simp only [empty_union, hg.empty, mul_zero, add_zero, mi_empty hg, sub_zero] at h0 h1
  linarith

end LemmaE

end HalfRate
