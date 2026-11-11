import AdaptiveTransfer.GeometryMenus
import LeanMachine.SparseBinomial
import LeanMachine.PolynomialMenus

/-! Uniform sparse-cut costs for both exact geometry menus. A single binomial
menu dominates every small selection parameter, so no monotonicity restriction
such as r ≤ T/2 is needed. -/

namespace AdaptiveTransfer
open LeanMachine Finset
open scoped BigOperators

/-- Common binomial support menu for all records with at most r cuts. -/
def geometrySparseMenu (P T r N : ℕ) : ℕ :=
  ∑ j ∈ range (4*r+2*N+2+1), (P+T+(4*r+2*N+2)).choose j

theorem geometrySparseMenu_pos (P T r N : ℕ) : 1 ≤ geometrySparseMenu P T r N := by
  have h := single_le_sum (f := fun j => (P+T+(4*r+2*N+2)).choose j)
    (fun j _ => Nat.zero_le _) (show 0 ∈ range (4*r+2*N+2+1) by simp)
  simpa [geometrySparseMenu] using h

theorem choose_le_geometrySparseMenu {P T r N n j : ℕ}
    (hn : n ≤ P+T+(4*r+2*N+2)) (hj : j ≤ 4*r+2*N+2) :
    n.choose j ≤ geometrySparseMenu P T r N := by
  apply (Nat.choose_le_choose j hn).trans
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))

def geometryPayloadAlphabet (k β : ℕ) : ℕ := 6^(k+1) * 2^β

theorem globalGeometryTerm_le {k β P T r s N : ℕ} (hs : s ≤ r) :
    globalGeometryMenuSize k P T s * 2^(β*s) ≤
      (T+1) * geometryPayloadAlphabet k β ^ r * geometrySparseMenu P T r N ^ (k+5) := by
  let V := geometrySparseMenu P T r N
  have h₁ : T.choose s ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₂ : (T+(s+1)).choose (s+1) ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₃ : (T+s).choose s ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₄ : (T+2*(s+1)).choose (2*(s+1)) ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₅ : (P+4*s+2).choose (4*s+2) ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have hh : globalGeometryMenuSize k P T s * 2^(β*s) ≤
      (T+1) * V * V * (6^s * V)^(k+1) * V * V * 2^(β*s) := by
    unfold globalGeometryMenuSize
    gcongr
  have he : (T+1) * V * V * (6^s * V)^(k+1) * V * V * 2^(β*s) =
      (T+1) * geometryPayloadAlphabet k β ^ s * V ^ (k+5) := by
    simp only [geometryPayloadAlphabet, mul_pow, ← pow_mul, pow_add]
    rw [Nat.mul_comm s k]
    simp only [Nat.mul_one, Nat.one_mul, pow_one]
    ring
  rw [he] at hh
  apply hh.trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by unfold geometryPayloadAlphabet; positivity) hs))

theorem localGeometryTerm_le {k β P T r s N : ℕ} (hs : s ≤ r) :
    localGeometryMenuSize k P T N s * 2^(β*s) ≤
      (T+1) * geometryPayloadAlphabet k β ^ r * geometrySparseMenu P T r N ^ (k+5) := by
  let V := geometrySparseMenu P T r N
  have h₁ : T.choose s ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₂ : (T+N+s).choose (N+s) ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₃ : (T+s).choose s ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have h₄ : (P+4*s+2*N).choose (4*s+2*N) ≤ V := choose_le_geometrySparseMenu (by omega) (by omega)
  have hh : localGeometryMenuSize k P T N s * 2^(β*s) ≤
      (T+1) * V * V * (6^s * V)^(k+1) * V * 2^(β*s) := by
    unfold localGeometryMenuSize
    gcongr
  have he : (T+1) * V * V * (6^s * V)^(k+1) * V * 2^(β*s) =
      (T+1) * geometryPayloadAlphabet k β ^ s * V ^ (k+4) := by
    simp only [geometryPayloadAlphabet, mul_pow, ← pow_mul, pow_add]
    rw [Nat.mul_comm s k]
    simp only [Nat.mul_one, Nat.one_mul, pow_one]
    ring
  rw [he] at hh
  apply hh.trans
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by unfold geometryPayloadAlphabet; positivity) hs)
  · exact Nat.pow_le_pow_right (show 0 < V from geometrySparseMenu_pos P T r N)
      (show k+4 ≤ k+5 by omega)

def globalCutMenu (k β P T r : ℕ) : ℕ :=
  ∑ s ∈ range (min r T + 1), globalGeometryMenuSize k P T s * 2^(β*s)

def localCutMenu (k β P T N r : ℕ) : ℕ :=
  ∑ s ∈ range (min r T + 1), localGeometryMenuSize k P T N s * 2^(β*s)

def geometryMenuEnvelope (k β P T N r : ℕ) : ℕ :=
  (r+1) * (T+1) * geometryPayloadAlphabet k β ^ r * geometrySparseMenu P T r N ^ (k+5)

theorem globalCutMenu_le_envelope (k β P T N r : ℕ) :
    globalCutMenu k β P T r ≤ geometryMenuEnvelope k β P T N r := by
  apply (sum_le_sum (fun s hs => globalGeometryTerm_le (N := N)
    (show s ≤ r by have := mem_range.mp hs; omega))).trans
  rw [sum_const, card_range, nsmul_eq_mul]
  unfold geometryMenuEnvelope
  calc
    _ ≤ (r+1) * ((T+1) * geometryPayloadAlphabet k β ^ r * geometrySparseMenu P T r N ^ (k+5)) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.min_le_left r T) 1)
    _ = _ := by ring

theorem localCutMenu_le_envelope (k β P T N r : ℕ) :
    localCutMenu k β P T N r ≤ geometryMenuEnvelope k β P T N r := by
  apply (sum_le_sum (fun s hs => localGeometryTerm_le
    (show s ≤ r by have := mem_range.mp hs; omega))).trans
  rw [sum_const, card_range, nsmul_eq_mul]
  unfold geometryMenuEnvelope
  calc
    _ ≤ (r+1) * ((T+1) * geometryPayloadAlphabet k β ^ r * geometrySparseMenu P T r N ^ (k+5)) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.min_le_left r T) 1)
    _ = _ := by ring

/-- The exact global and localized menus have arbitrarily small information
per input bit at a sufficiently small fixed cut density. The length threshold
absorbs only fixed N, not the entry width. -/
theorem geometryMenuEnvelope_log_small (k β N K : ℕ) (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P₀ : ℕ, ∀ P T r : ℕ, P₀ ≤ P →
      T ≤ K*(P+1) → (r : ℝ) ≤ δ*P →
      Real.log (geometryMenuEnvelope k β P T N r : ℕ) ≤ ε*P := by
  let A := geometryPayloadAlphabet k β
  have hA : 0 < A := by unfold A geometryPayloadAlphabet; positivity
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  let L := Real.log A
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hA)
  have hk5 : (0 : ℝ) < k+5 := by positivity
  obtain ⟨γ, hγ, hsparse⟩ := weightedSparseMenu_log_small_density
    (C := 2*K+9) (A := (1 : ℝ)) (ε := ε/(3*(k+5))) (by positivity) (by norm_num) (by positivity)
  obtain ⟨P₁, hpoly⟩ := polynomial_menu_log_small (A := 1) (B := K+1) (e := 2)
    (by omega) (by omega) (show 0 < ε/3 by positivity)
  let δ := min 1 (min (γ/8) (ε/(3*(L+1))))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  refine ⟨δ, hδ, max P₁ (max (N+1) ⌈4*((N : ℝ)+1)/γ⌉₊), ?_⟩
  intro P T r hP hT hr
  have hP₁ : P₁ ≤ P := (le_max_left _ _).trans hP
  have hNP : N+1 ≤ P := (le_max_left _ _).trans ((le_max_right _ _).trans hP)
  have hceil : ⌈4*((N : ℝ)+1)/γ⌉₊ ≤ P :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hP)
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδγ : δ ≤ γ/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/(3*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hrP : r ≤ P := by
    have hh : (r : ℝ) ≤ P := hr.trans (by nlinarith)
    exact_mod_cast hh
  have hJ : (4*r+2*N+2 : ℕ) ≤ γ*(P : ℝ) := by
    have hc : 4*((N : ℝ)+1)/γ ≤ (P : ℝ) :=
      (Nat.le_ceil (4*((N : ℝ)+1)/γ)).trans (by exact_mod_cast hceil)
    have hc' := (div_le_iff₀ hγ).mp hc
    have hrγ := hr.trans (mul_le_mul_of_nonneg_right hδγ hPr.le)
    push_cast at hc' ⊢
    nlinarith
  have hslots : (P+T+(4*r+2*N+2) : ℕ) ≤ (2*K+9 : ℝ)*P := by
    have ht' : T ≤ 2*K*P := by nlinarith
    have hn' : P+T+(4*r+2*N+2) ≤ (2*K+9)*P := by nlinarith
    exact_mod_cast hn'
  have hmenu := hsparse (P+T+(4*r+2*N+2)) (4*r+2*N+2) P hPr.le hslots hJ
  have hmenu' : Real.log (geometrySparseMenu P T r N : ℕ) ≤ ε/(3*(k+5 : ℝ))*P := by
    simpa only [geometrySparseMenu, weightedSparseMenu, min_eq_right (show 4*r+2*N+2 ≤
      P+T+(4*r+2*N+2) by omega), one_pow, mul_one, Nat.cast_sum] using hmenu
  have hpre : (r+1)*(T+1) ≤ 1*((K+1)*(P+1))^2 := by
    have h1 : r+1 ≤ (K+1)*(P+1) := by nlinarith
    have h2 : T+1 ≤ (K+1)*(P+1) := by nlinarith
    nlinarith [Nat.mul_le_mul h1 h2]
  have hpref := hpoly P hP₁ ((r+1)*(T+1)) (by nlinarith) hpre
  have hexp : (r : ℝ)*L ≤ ε/3*P := by
    have he := (le_div_iff₀ (show 0 < 3*(L+1) by positivity)).mp hδε
    have hb := mul_le_mul_of_nonneg_right hr hL
    nlinarith
  have hslog : (k+5 : ℝ)*Real.log (geometrySparseMenu P T r N : ℕ) ≤ ε/3*P := by
    have hh := mul_le_mul_of_nonneg_left hmenu' hk5.le
    convert hh using 1
    field_simp
  have hV : (0 : ℝ) < (geometrySparseMenu P T r N : ℕ) := by
    exact_mod_cast geometrySparseMenu_pos P T r N
  have he : (geometryMenuEnvelope k β P T N r : ℝ) =
      ((r+1)*(T+1) : ℕ) * (A : ℝ)^r * (geometrySparseMenu P T r N : ℝ)^(k+5) := by
    simp only [geometryMenuEnvelope, A, Nat.cast_mul, Nat.cast_pow]
  rw [he]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  change Real.log ((r+1)*(T+1) : ℕ) + (r : ℝ)*L +
    ((k+5 : ℕ) : ℝ)*Real.log (geometrySparseMenu P T r N : ℕ) ≤ ε*P
  push_cast
  push_cast at hslog hpref
  linarith

private theorem nat_log_le_envelope {m n : ℕ} (hn : 0 < n) (hmn : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simpa only [Nat.cast_zero, Real.log_zero] using Real.log_nonneg
      (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hm)) (by exact_mod_cast hmn)

theorem geometryMenuEnvelope_pos (k β P T N r : ℕ) : 0 < geometryMenuEnvelope k β P T N r := by
  have hV : 0 < geometrySparseMenu P T r N := geometrySparseMenu_pos P T r N
  unfold geometryMenuEnvelope geometryPayloadAlphabet
  positivity

/-- Simultaneous finite bit-cost bounds for the two exact menus, with the
same density and length threshold. There is no r≤T/2 side condition. -/
theorem geometry_cut_menus_logb_small (k β N K : ℕ) (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P₀ : ℕ, ∀ P T r : ℕ, P₀ ≤ P →
      T ≤ K*(P+1) → (r : ℝ) ≤ δ*P →
      Real.logb 2 (globalCutMenu k β P T r : ℕ) ≤ ε*P ∧
      Real.logb 2 (localCutMenu k β P T N r : ℕ) ≤ ε*P := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨δ,hδ,P₀,hbound⟩ := geometryMenuEnvelope_log_small k β N K hK (mul_pos hε hlog2)
  refine ⟨δ,hδ,P₀,?_⟩
  intro P T r hP hT hr
  have hh := hbound P T r hP hT hr
  have hg := nat_log_le_envelope (geometryMenuEnvelope_pos k β P T N r)
    (globalCutMenu_le_envelope k β P T N r)
  have hl := nat_log_le_envelope (geometryMenuEnvelope_pos k β P T N r)
    (localCutMenu_le_envelope k β P T N r)
  constructor <;> rw [Real.logb, div_le_iff₀ hlog2] <;> nlinarith

end AdaptiveTransfer
