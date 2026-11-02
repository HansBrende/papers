import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

/-!
# Fast kernel checks of matrix identities over `𝔽₃` (Kronecker substitution)

For certificates checked by `decide +kernel`.

A row `y₀, …, y_{r-1}` with entries in `{0, 1, 2}` is packed as the natural number `Σ_j y_j 512^j` (`pk`). For a
row `x` with entries in `{0, 1, 2}` and packed rows `Ŷ₀, …, Ŷ_{q-1}` (`q ≤ 127`), the number `Σ_k x_k Ŷ_k` has
base-512 digits `Σ_k x_k Y_{kj} ≤ 4q < 512`, so no digit carries. `prodOK X Ŷ Z` compares these digits mod 3
with the rows of `Z`. It uses only natural-number operations that the kernel evaluates natively
(`*`, `+`, `/`, `%`, `^` on literals): one small-by-big product per term instead of `q · r` operations in
`ZMod 3`.

Kernel-friendliness: every recursion is over a list. A recursion over a counter that passes `n / 512` down
unevaluated re-evaluates the whole chain of divisions at every level, so digits are read directly (`dg`).

`prodOK_sound` turns a successful check into `Σ_k X_{ik} Y_{kj} = Z_{ij}` in `ZMod 3`, with `Y_{kj}` the digit
`j` of `Ŷ_k`.
-/

namespace LeanMachine.PackedCheck

open Finset

/-- Digit `j` of `n` in base 512. -/
def dg (n j : ℕ) : ℕ := n / 512 ^ j % 512

/-- Pack a list of digits in base 512 (little-endian). -/
def pk (l : List ℕ) : ℕ := l.foldr (fun d acc => d + 512 * acc) 0

/-- `Σ_k x_k y_k` (truncated to the shorter list). -/
def dotP : List ℕ → List ℕ → ℕ
  | x :: xs, y :: ys => x * y + dotP xs ys
  | _, _ => 0

/-- The base-512 digits of `s`, reduced mod 3, are `z` (lowest digit first). -/
def digOK : ℕ → List ℕ → Bool
  | _, [] => true
  | s, z :: zs => (s % 512 % 3 == z) && digOK (s / 512) zs

/-- `n < 512 ^ r` and its `r` base-512 digits are at most 2. -/
def smallDigits (n r : ℕ) : Bool := n.blt (512 ^ r) && (List.range r).all fun j => (dg n j).ble 2

/-- The rows (of length `r`) of a matrix given by packed rows. -/
def rowsOf (Ypk : List ℕ) (r : ℕ) : List (List ℕ) := Ypk.map fun y => (List.range r).map (dg y)

/-- `X · Y ≡ Z (mod 3)`, where `Ypk` lists the packed rows of `Y`. -/
def prodOK (X : List (List ℕ)) (Ypk : List ℕ) (Z : List (List ℕ)) : Bool :=
  X.length == Z.length && (X.zip Z).all fun p => digOK (dotP p.1 Ypk) p.2

/-- The `m × n` zero matrix and the `n × n` identity, as digit lists. -/
def zeros (m n : ℕ) : List (List ℕ) := List.replicate m (List.replicate n 0)
def ident (n : ℕ) : List (List ℕ) :=
  (List.range n).map fun a => (List.range n).map fun c => if a = c then 1 else 0

/-- `q` packed rows, each `< 512 ^ r` with `r` digits at most 2. -/
def PackedSmall (Ypk : List ℕ) (q r : ℕ) : Prop :=
  Ypk.length = q ∧ ∀ k < q, Ypk.getD k 0 < 512 ^ r ∧ ∀ j < r, dg (Ypk.getD k 0) j ≤ 2

/-- Rows of length `q` with entries at most 2. -/
def RowsSmall (X : List (List ℕ)) (q : ℕ) : Prop :=
  ∀ i < X.length, (X.getD i []).length = q ∧ ∀ k < q, (X.getD i []).getD k 0 ≤ 2

/-! ### Digits -/

theorem dg_zero (n : ℕ) : dg n 0 = n % 512 := by simp [dg]

theorem dg_succ (n j : ℕ) : dg n (j + 1) = dg (n / 512) j := by
  simp only [dg, pow_succ', Nat.div_div_eq_div_mul]

theorem digOK_spec : ∀ (s : ℕ) (z : List ℕ), digOK s z = true →
    ∀ j < z.length, dg s j % 3 = z.getD j 0
  | _, [], _, j, hj => absurd hj (by simp)
  | s, z :: zs, h, j, hj => by
    simp only [digOK, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa [dg_zero] using h.1
    | succ j =>
      rw [dg_succ]
      simpa using digOK_spec (s / 512) zs h.2 j (by simpa using hj)

theorem smallDigits_spec {n r : ℕ} (h : smallDigits n r = true) : n < 512 ^ r ∧ ∀ j < r, dg n j ≤ 2 := by
  simp only [smallDigits, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, List.mem_range,
    Nat.ble_eq] at h
  exact h

/-! ### Base-512 expansions -/

/-- `Σ_{j<r} d_j 512^j`. -/
def expand (d : ℕ → ℕ) (r : ℕ) : ℕ := ∑ j ∈ range r, d j * 512 ^ j

theorem expand_succ (d : ℕ → ℕ) (r : ℕ) :
    expand d (r + 1) = d 0 + 512 * expand (fun j => d (j + 1)) r := by
  simp only [expand, sum_range_succ', pow_zero, mul_one, mul_sum]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  ring

theorem expand_lt : ∀ (d : ℕ → ℕ) (r : ℕ), (∀ j < r, d j < 512) → expand d r < 512 ^ r
  | _, 0, _ => by simp [expand]
  | d, r + 1, hd => by
    rw [expand_succ, pow_succ']
    have h0 := hd 0 (by omega)
    have := expand_lt (fun j => d (j + 1)) r (fun j hj => hd (j + 1) (by omega))
    omega

theorem expand_dg : ∀ (n r : ℕ), n < 512 ^ r → expand (dg n) r = n
  | n, 0, h => by simp [expand]; omega
  | n, r + 1, h => by
    rw [expand_succ]
    have hdiv : n / 512 < 512 ^ r := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      simpa [pow_succ] using h
    have := expand_dg (n / 512) r hdiv
    simp only [dg_succ] at this ⊢
    rw [this, dg_zero]
    omega

theorem dg_expand : ∀ (d : ℕ → ℕ) (r : ℕ), (∀ j < r, d j < 512) → ∀ j < r, dg (expand d r) j = d j
  | _, 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | d, r + 1, hd, j, hj => by
    rw [expand_succ]
    have h0 : d 0 < 512 := hd 0 (by omega)
    cases j with
    | zero => rw [dg_zero]; omega
    | succ j =>
      rw [dg_succ]
      have hq : (d 0 + 512 * expand (fun j => d (j + 1)) r) / 512 = expand (fun j => d (j + 1)) r := by
        omega
      rw [hq]
      exact dg_expand (fun j => d (j + 1)) r (fun i hi => hd (i + 1) (by omega)) j (by omega)

/-! ### Packing a list -/

theorem pk_eq_expand : ∀ l : List ℕ, pk l = expand (fun j => l.getD j 0) l.length
  | [] => by simp [pk, expand]
  | d :: ds => by
    rw [List.length_cons, expand_succ]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [← pk_eq_expand ds]
    simp [pk, List.foldr_cons]

/-- A list with entries `≤ 2` packs to `< 512 ^ length` with exactly these digits. -/
theorem pk_spec (l : List ℕ) (hl : ∀ j < l.length, l.getD j 0 ≤ 2) :
    pk l < 512 ^ l.length ∧ ∀ j < l.length, dg (pk l) j = l.getD j 0 := by
  have h512 : ∀ j < l.length, l.getD j 0 < 512 := fun j hj => by have := hl j hj; omega
  rw [pk_eq_expand]
  exact ⟨expand_lt _ _ h512, dg_expand _ _ h512⟩

/-! ### Products -/

theorem dotP_eq_sum : ∀ (q : ℕ) (x y : List ℕ), x.length = q → y.length = q →
    dotP x y = ∑ k : Fin q, x.getD k 0 * y.getD k 0
  | 0, [], [], _, _ => by simp [dotP]
  | q + 1, a :: as, b :: bs, h₁, h₂ => by
    rw [Fin.sum_univ_succ, dotP, dotP_eq_sum q as bs (by simpa using h₁) (by simpa using h₂)]
    simp
  | 0, _ :: _, _, h₁, _ => by simp at h₁
  | 0, [], _ :: _, _, h₂ => by simp at h₂
  | _ + 1, [], _, h₁, _ => by simp at h₁
  | _ + 1, _ :: _, [], _, h₂ => by simp at h₂

/-- The digits of `Σ_k x_k Ŷ_k` are `Σ_k x_k Y_{kj}`. -/
theorem dg_dotP {q r : ℕ} (hq : q ≤ 127) {x Ypk : List ℕ} (hx : x.length = q)
    (hxs : ∀ k < q, x.getD k 0 ≤ 2) (hY : PackedSmall Ypk q r) (j : ℕ) (hj : j < r) :
    dg (dotP x Ypk) j = ∑ k : Fin q, x.getD k 0 * dg (Ypk.getD k 0) j := by
  obtain ⟨hYlen, hYs⟩ := hY
  have hexp : ∀ k : Fin q, Ypk.getD k 0 = expand (dg (Ypk.getD k 0)) r := fun k =>
    (expand_dg _ r (hYs k k.2).1).symm
  have hsum : dotP x Ypk = expand (fun j => ∑ k : Fin q, x.getD k 0 * dg (Ypk.getD k 0) j) r := by
    rw [dotP_eq_sum q x Ypk hx hYlen]
    calc ∑ k : Fin q, x.getD k 0 * Ypk.getD k 0
        = ∑ k : Fin q, x.getD k 0 * expand (dg (Ypk.getD k 0)) r :=
          sum_congr rfl fun k _ => by rw [← hexp k]
      _ = expand (fun j => ∑ k : Fin q, x.getD k 0 * dg (Ypk.getD k 0) j) r := by
          simp only [expand, mul_sum, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
          ring
  rw [hsum]
  refine dg_expand _ r (fun i hi => ?_) j hj
  calc ∑ k : Fin q, x.getD k 0 * dg (Ypk.getD k 0) i ≤ ∑ _k : Fin q, 2 * 2 :=
        sum_le_sum fun k _ => Nat.mul_le_mul (hxs k k.2) ((hYs k k.2).2 i hi)
    _ = 4 * q := by simp [mul_comm]
    _ < 512 := by omega

/-- **Soundness of `prodOK`**: `Σ_k X_{ik} Y_{kj} = Z_{ij}` in `ZMod 3`, with `Y_{kj}` the digit `j` of `Ŷ_k`. -/
theorem prodOK_sound {X : List (List ℕ)} {Ypk : List ℕ} {Z : List (List ℕ)} {q r : ℕ} (hq : q ≤ 127)
    (hX : RowsSmall X q) (hY : PackedSmall Ypk q r) (hZ : ∀ i < Z.length, (Z.getD i []).length = r)
    (h : prodOK X Ypk Z = true) (i : ℕ) (hi : i < X.length) (j : ℕ) (hj : j < r) :
    ∑ k : Fin q, (((X.getD i []).getD k 0 : ℕ) : ZMod 3) * ((dg (Ypk.getD k 0) j : ℕ) : ZMod 3) =
      (((Z.getD i []).getD j 0 : ℕ) : ZMod 3) := by
  simp only [prodOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hiZ : i < Z.length := hlen ▸ hi
  have hmem : (X[i], Z[i]) ∈ X.zip Z := by
    have hiz : i < (X.zip Z).length := by rw [List.length_zip]; omega
    have := List.getElem_mem hiz
    rwa [List.getElem_zip] at this
  have hrow := hall _ hmem
  obtain ⟨hXlen, hXs⟩ := hX i hi
  have hZi := hZ i hiZ
  rw [List.getD_eq_getElem _ _ hi] at hXlen hXs
  rw [List.getD_eq_getElem _ _ hiZ] at hZi
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hiZ]
  have hdig := digOK_spec _ _ hrow j (by show j < Z[i].length; omega)
  rw [← hdig, dg_dotP hq hXlen hXs hY j hj, ZMod.natCast_mod]
  push_cast
  rfl

/-! ### Establishing the hypotheses -/

theorem getD_rowsOf (Ypk : List ℕ) (r i k : ℕ) (hk : k < r) :
    ((rowsOf Ypk r).getD i []).getD k 0 = dg (Ypk.getD i 0) k := by
  by_cases hi : i < Ypk.length
  · rw [List.getD_eq_getElem (rowsOf Ypk r) [] (by simpa [rowsOf] using hi),
      List.getD_eq_getElem Ypk 0 hi]
    simp only [rowsOf, List.getElem_map]
    rw [List.getD_eq_getElem _ 0 (by simpa using hk)]
    simp
  · have h1 : (rowsOf Ypk r).getD i [] = [] := by
      rw [List.getD_eq_default]; simpa [rowsOf] using hi
    rw [h1, List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by omega)]
    simp [dg]

theorem length_getD_rowsOf (Ypk : List ℕ) (r i : ℕ) (hi : i < Ypk.length) :
    ((rowsOf Ypk r).getD i []).length = r := by
  rw [List.getD_eq_getElem _ _ (by simpa [rowsOf] using hi)]
  simp [rowsOf]

/-- Rows read from small packed rows are small. -/
theorem rowsSmall_rowsOf {Ypk : List ℕ} {m r : ℕ} (h : PackedSmall Ypk m r) :
    RowsSmall (rowsOf Ypk r) r := by
  intro i hi
  have hi' : i < Ypk.length := by simpa [rowsOf] using hi
  refine ⟨length_getD_rowsOf Ypk r i hi', fun k hk => ?_⟩
  rw [getD_rowsOf _ _ _ _ hk]
  exact (h.2 i (h.1 ▸ hi')).2 k hk

/-- A Boolean check gives `PackedSmall`. -/
theorem packedSmall_of_check {Ypk : List ℕ} {q r : ℕ}
    (h : (Ypk.length == q && Ypk.all fun y => smallDigits y r) = true) : PackedSmall Ypk q r := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [List.getD_eq_getElem _ _ (h.1 ▸ hk)]
  exact smallDigits_spec (h.2 _ (List.getElem_mem _))

/-- Packed rows of small digit rows. -/
theorem packedSmall_map_pk {rows : List (List ℕ)} {r : ℕ} (hr : RowsSmall rows r) :
    PackedSmall (rows.map pk) rows.length r := by
  refine ⟨by simp, fun k hk => ?_⟩
  obtain ⟨hlen, hs⟩ := hr k hk
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  rw [List.getD_eq_getElem _ _ hk] at hlen hs
  obtain ⟨hlt, hdg⟩ := pk_spec _ (fun j hj => hs j (hlen ▸ hj))
  refine ⟨hlen ▸ hlt, fun j hj => ?_⟩
  rw [hdg j (hlen ▸ hj)]
  exact hs j hj

theorem dg_getD_map_pk {rows : List (List ℕ)} {r : ℕ} (hr : RowsSmall rows r) (k j : ℕ)
    (hk : k < rows.length) (hj : j < r) :
    dg ((rows.map pk).getD k 0) j = (rows.getD k []).getD j 0 := by
  obtain ⟨hlen, hs⟩ := hr k hk
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  rw [List.getD_eq_getElem _ _ hk] at hlen hs ⊢
  exact (pk_spec _ (fun i hi => hs i (hlen ▸ hi))).2 j (hlen ▸ hj)

theorem zeros_rows (m n : ℕ) : ∀ i < (zeros m n).length, ((zeros m n).getD i []).length = n := by
  intro i hi
  rw [List.getD_eq_getElem _ _ hi]
  simp [zeros]

theorem getD_zeros (m n i j : ℕ) : ((zeros m n).getD i []).getD j 0 = 0 := by
  by_cases hi : i < m
  · rw [List.getD_eq_getElem (zeros m n) [] (by simpa [zeros] using hi)]
    simp [zeros]
  · rw [List.getD_eq_default (zeros m n) [] (by simpa [zeros] using hi)]
    simp

theorem ident_rows (n : ℕ) : ∀ i < (ident n).length, ((ident n).getD i []).length = n := by
  intro i hi
  rw [List.getD_eq_getElem _ _ hi]
  simp [ident]

theorem getD_ident (n i j : ℕ) (hi : i < n) (hj : j < n) :
    ((ident n).getD i []).getD j 0 = if i = j then 1 else 0 := by
  rw [List.getD_eq_getElem (ident n) [] (by simpa [ident] using hi)]
  simp only [ident, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ 0 (by simpa using hj)]
  simp

end LeanMachine.PackedCheck
