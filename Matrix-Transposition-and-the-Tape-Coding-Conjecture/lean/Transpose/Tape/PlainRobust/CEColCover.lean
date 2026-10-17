import Transpose.Tape.PlainRobust.CEDecomp
import Transpose.Tape.PlainRobust.CESyndrome

/-!
# Column covers: copies on locally computable inputs, one copy per output column

Generalizes the column-respecting case of the decomposition (`CEDecomp`, masked copies with XOR-ed
outputs). Run `K` copies of a code for `F` side by side (`kfoldTapes`), copy `κ` on the input
`Φ κ x`, where `Φ κ` is **locally computable** (each node computes the copy's visible input from its
own visible input) and keeps the input columns of class `κ`. The output of column `j` is read from
copy `cls j`. If every `Φ κ x` lies in `F`, this solves every input (`colCover_solves`), so plain
rules out codes on `F` (`noCode_colCover_of_noCode`).

* Row maps (`applyRows`) are locally computable, since a node sees whole rows (`rowMapVis_visible`):
  `noCode_rowMapCover_of_noCode`.
* **Duplication** (`noCode_colAggregate_of_noCode`): for even `n`, any set containing
  `{x : Σ_j v(column j of x) = 0}`, with the same `v` for every column (any number of GF(2)
  constraints), carries no code under plain. The inputs `[x_left | x_left]` and
  `[x_right | x_right]` satisfy every such constraint, since each term appears twice.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### Copies on mapped inputs -/

section MapCode

variable {k : ℕ} (D : TSDiagram k) (n G : ℕ)

/-- `C` run on the visible input transformed by `τ κ` at every node. The decoder of output `o`
transforms the visible input of the node appending `o`. -/
noncomputable def mapCode (C : NetCode) (τ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool) (κ : ℕ) : NetCode where
  enc e f v := C.enc e f (τ κ e.1 v)
  dec o f v := C.dec o f (τ κ (D.outNode (blockSize G n) o) v)

theorem inVals_mapCode (C : NetCode) (τ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool) (κ : ℕ)
    (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) :
    ∀ u, (mapCode D n G C τ κ).inVals E vis u = C.inVals E (fun y => τ κ y (vis y)) u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]; rfl
  · rfl

/-- **`K` codes side by side**, the clamped values packed in base `2^c`; output `o` is decoded by
copy `sel o`. -/
noncomputable def sideCode (K : ℕ) (codes : ℕ → NetCode) (sel : ℕ → ℕ) : NetCode where
  enc e f v := packK (D.profileCap n G e) K
    (fun j => (clampCode D n G (codes j)).enc e (fun e' => digit D n G j e' (f e')) v)
  dec o f v := (codes (sel o)).dec o (fun e' => digit D n G (sel o) e' (f e')) v

/-- **Each digit carries its own copy.** -/
theorem sideCode_digits (K : ℕ) (codes : ℕ → NetCode) (sel : ℕ → ℕ) (E : Finset (ℕ × ℕ))
    (vis : ℕ → ℕ → Bool) :
    ∀ u, ∀ j < K, (fun e' => digit D n G j e' ((sideCode D n G K codes sel).inVals E vis u e')) =
      (clampCode D n G (codes j)).inVals E vis u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro j hj
  funext e'
  rw [inVals_eq (clampCode D n G (codes j))]
  by_cases hc : e' ∈ E ∧ e'.2 = u ∧ e'.1 < u
  · rw [ite_eq_left hc, inVals_eq, ite_eq_left hc]
    show digit D n G j e' (packK (D.profileCap n G e') K (fun j' =>
      (clampCode D n G (codes j')).enc e' (fun e'' => digit D n G j' e''
        ((sideCode D n G K codes sel).inVals E vis e'.1 e'')) (vis e'.1))) = _
    have hdig : ∀ v : ℕ → ℕ, (∀ a < K, v a < 2 ^ D.profileCap n G e') →
        digit D n G j e' (packK (D.profileCap n G e') K v) = v j :=
      fun v hv => digit_packK hv hj
    rw [hdig _ (fun b _ => clamp_lt D n G _ _ _ _), ih e'.1 hc.2.2 j hj]
  · rw [ite_eq_right hc, inVals_eq, ite_eq_right hc]
    simp [digit]

end MapCode

/-- **Column cover.** Let `C` solve complete exchange on `F` at the profile capacities of `D`, and
let `K` input maps `Φ κ` be locally computable (`τ κ u` turns the visible input of node `u` on `x`
into that on `Φ κ x`), keep the input columns of class `κ`, and map every input into `F`. Then `K`
copies side by side, reading output column `j` from copy `cls j`, solve **every** input on
`kfoldTapes D K`. -/
theorem colCover_solves {k : ℕ} (D : TSDiagram k) {n G K : ℕ} (hK : 1 ≤ K)
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode}
    (hsol : D.Solves n G (D.profileCap n G) F C) (cls : ℕ → ℕ)
    (Φ : ℕ → (Fin (n * n * entryBits n) → Bool) → (Fin (n * n * entryBits n) → Bool))
    (τ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool)
    (hτ : ∀ κ < K, ∀ x u, τ κ u (D.visible n (entryBits n) (blockSize G n) u x) =
      D.visible n (entryBits n) (blockSize G n) u (Φ κ x))
    (hkeep : ∀ x (d : Fin (n * n * entryBits n)), Φ (cls ((d : ℕ) / entryBits n % n)) x d = x d)
    (hcls : ∀ j < n, cls j < K) (hF : ∀ κ < K, ∀ x, Φ κ x ∈ F) :
    (kfoldTapes D K).Solves n G ((kfoldTapes D K).profileCap n G) Set.univ
      (sideCode D n G K (mapCode D n G C τ) (fun o => cls (o / (n * entryBits n)))) := by
  intro x _
  have hE : (kfoldTapes D K).edges (blockSize G n) = D.edges (blockSize G n) := edges_kfold D K hK _
  have hvis : (fun y => (kfoldTapes D K).visible n (entryBits n) (blockSize G n) y x) =
      fun y => D.visible n (entryBits n) (blockSize G n) y x := rfl
  rw [hE, hvis]
  -- copy `κ` computes `C` on `Φ κ x`
  have hin : ∀ κ < K, ∀ u, (mapCode D n G C τ κ).inVals (D.edges (blockSize G n))
      (fun y => D.visible n (entryBits n) (blockSize G n) y x) u =
      C.inVals (D.edges (blockSize G n))
        (fun y => D.visible n (entryBits n) (blockSize G n) y (Φ κ x)) u := by
    intro κ hκ u
    rw [inVals_mapCode]
    congr 1
    funext y
    exact hτ κ hκ x y
  have hcopy : ∀ κ < K,
      (∀ e ∈ D.edges (blockSize G n), (mapCode D n G C τ κ).edgeVal (D.edges (blockSize G n))
        (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) ∧
      ∀ (d : ℕ) (hd : d < n * n * entryBits n),
        (mapCode D n G C τ κ).outVal (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x)
          (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) =
            Φ κ x ⟨d, hd⟩ := by
    intro κ hκ
    obtain ⟨hc, ho⟩ := hsol (Φ κ x) (hF κ hκ x)
    refine ⟨fun e he => ?_, fun d hd => ?_⟩
    · show C.enc e ((mapCode D n G C τ κ).inVals _ _ e.1)
        (τ κ e.1 (D.visible n (entryBits n) (blockSize G n) e.1 x)) < _
      rw [hin κ hκ, hτ κ hκ]
      exact hc e he
    · show C.dec _ ((mapCode D n G C τ κ).inVals _ _ _)
        (τ κ (D.outNode (blockSize G n) (tpos n (entryBits n) d))
          (D.visible n (entryBits n) (blockSize G n)
            (D.outNode (blockSize G n) (tpos n (entryBits n) d)) x)) = _
      rw [hin κ hκ, hτ κ hκ]
      exact ho d hd
  refine ⟨fun e _ => ?_, fun d hd => ?_⟩
  · rw [profileCap_kfold D K hK]
    exact packK_lt (fun j _ => clamp_lt D n G _ _ _ _)
  · -- the copy of `d`'s column
    have hcol : (tpos n (entryBits n) d) / (n * entryBits n) = d / entryBits n % n := tpos_div hd
    have hκ : cls (d / entryBits n % n) < K := hcls _ (Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hd
      · exact h))
    show (mapCode D n G C τ (cls ((tpos n (entryBits n) d) / (n * entryBits n)))).dec
      (tpos n (entryBits n) d)
      (fun e' => digit D n G (cls ((tpos n (entryBits n) d) / (n * entryBits n))) e'
        ((sideCode D n G K (mapCode D n G C τ) (fun o => cls (o / (n * entryBits n)))).inVals
          (D.edges (blockSize G n)) (fun y => D.visible n (entryBits n) (blockSize G n) y x)
          (D.outNode (blockSize G n) (tpos n (entryBits n) d)) e'))
      (D.visible n (entryBits n) (blockSize G n)
        (D.outNode (blockSize G n) (tpos n (entryBits n) d)) x) = _
    rw [hcol, sideCode_digits D n G K _ _ _ _ _ _ hκ]
    obtain ⟨hc, ho⟩ := hcopy _ hκ
    rw [clamp_inVals D n G _ _ _ hc]
    have := ho d hd
    simp only [NetCode.outVal] at this
    rw [this]
    exact hkeep x ⟨d, hd⟩

/-- **Plain ⟹ no code on a set covered by `K` locally computable column-keeping maps.** Under
`NoCode_TM`, for every constant `K` and all large `n`: let `cls` give each column a class `< K`, and
let input maps `Φ κ` be locally computable (`τ κ u` turns the visible input of node `u` on `x` into
that on `Φ κ x`) and keep the input columns of class `κ`. Then no code solves complete exchange at
the profile capacities on a set `F` containing every `Φ κ x`. -/
theorem noCode_colCover_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cls : ℕ → ℕ), (∀ j < n, cls j < K) →
      ∀ (Φ : ℕ → (Fin (n * n * entryBits n) → Bool) → (Fin (n * n * entryBits n) → Bool))
        (τ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool),
        (∀ κ < K, ∀ x u, τ κ u (D.visible n (entryBits n) (blockSize G n) u x) =
          D.visible n (entryBits n) (blockSize G n) u (Φ κ x)) →
        (∀ x (d : Fin (n * n * entryBits n)), Φ (cls ((d : ℕ) / entryBits n % n)) x d = x d) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)), (∀ κ < K, ∀ x, Φ κ x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := h (K * k) G c hG
  refine ⟨n₀, fun n hn D hD hT cls hcls Φ τ hτ hkeep F hF code hsol => ?_⟩
  exact hn₀ n hn (kfoldTapes D K) (valid_kfold D K hD) hT _
    (colCover_solves D hK hsol cls Φ τ hτ hkeep hcls hF)

/-! ### Row maps are locally computable -/

/-- Row `i` of a bit vector (positions `[i n w, (i+1) n w)`), indexed by the position `< n w`
within the row (`false` beyond). -/
def rowBits (n w : ℕ) (v : ℕ → Bool) (i : ℕ) : ℕ → Bool :=
  fun p => if p < n * w then v (i * (n * w) + p) else false

/-- **The input with a row map applied**: bit `d` (row `i = d / (n w)`, position `p = d % (n w)`
within the row) is `ψ i (row i) p`. -/
def applyRows (n w : ℕ) (ψ : ℕ → (ℕ → Bool) → ℕ → Bool) {L : ℕ} (x : Fin L → Bool) :
    Fin L → Bool :=
  fun d => ψ ((d : ℕ) / (n * w)) (rowBits n w (xbits x) ((d : ℕ) / (n * w))) ((d : ℕ) % (n * w))

/-- The local version of a row map: each node applies `ψ` to its visible rows. -/
noncomputable def rowMapVis {k : ℕ} (D : TSDiagram k) (n w r L : ℕ)
    (ψ : ℕ → (ℕ → Bool) → ℕ → Bool) (u : ℕ) (v : ℕ → Bool) : ℕ → Bool :=
  fun d => if d < L ∧ d / (n * w) ∈ D.rowsAt n w r u then
    ψ (d / (n * w)) (rowBits n w v (d / (n * w))) (d % (n * w)) else false

theorem div_of_row_pos {n w i p : ℕ} (hp : p < n * w) : (i * (n * w) + p) / (n * w) = i := by
  have hpos : 0 < n * w := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hp, Nat.zero_add]

/-- **Row maps are locally computable**: applying `ψ` to the visible rows of `x` gives the visible
rows of `applyRows ψ x`. -/
theorem rowMapVis_visible {k : ℕ} (D : TSDiagram k) (n w r : ℕ) (ψ : ℕ → (ℕ → Bool) → ℕ → Bool)
    (u : ℕ) (x : Fin (n * n * w) → Bool) :
    rowMapVis D n w r (n * n * w) ψ u (D.visible n w r u x) =
      D.visible n w r u (applyRows n w ψ x) := by
  funext d
  by_cases hd : d < n * n * w
  · by_cases hrow : d / (n * w) ∈ D.rowsAt n w r u
    · have hnw : 0 < n * w := by
        rcases Nat.eq_zero_or_pos (n * w) with h0 | h0
        · rw [Nat.mul_assoc, h0, Nat.mul_zero] at hd; omega
        · exact h0
      have hi : d / (n * w) < n := by
        rw [Nat.div_lt_iff_lt_mul hnw]
        calc d < n * n * w := hd
          _ = n * (n * w) := by ring
      simp only [rowMapVis, TSDiagram.visible, dite_eq_left hd, ite_eq_left hrow,
        ite_eq_left (show d < n * n * w ∧ d / (n * w) ∈ D.rowsAt n w r u from ⟨hd, hrow⟩)]
      simp only [applyRows]
      congr 1
      funext p
      simp only [rowBits]
      split_ifs with hp
      · have hlt : d / (n * w) * (n * w) + p < n * n * w := by
          calc d / (n * w) * (n * w) + p < d / (n * w) * (n * w) + n * w := by omega
            _ = (d / (n * w) + 1) * (n * w) := by ring
            _ ≤ n * (n * w) := Nat.mul_le_mul_right _ hi
            _ = n * n * w := by ring
        simp only [TSDiagram.visible, dite_eq_left hlt, div_of_row_pos hp, ite_eq_left hrow, xbits]
      · rfl
    · simp only [rowMapVis, TSDiagram.visible, dite_eq_left hd, ite_eq_right hrow]
      rw [ite_eq_right (fun h => hrow h.2)]
  · simp only [rowMapVis, TSDiagram.visible, dite_eq_right hd]
    rw [ite_eq_right (fun h => hd h.1)]

/-- **Plain ⟹ no code on a set covered by `K` column-keeping row maps.** Under `NoCode_TM`, for
every constant `K` and all large `n`: let `cls` give each column a class `< K`, and let the row maps
`ψ κ` keep, within every row, the positions of the columns of class `κ`. Then no code solves complete
exchange at the profile capacities on a set containing every `applyRows (ψ κ) x`. -/
theorem noCode_rowMapCover_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cls : ℕ → ℕ), (∀ j < n, cls j < K) →
      ∀ (ψ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool),
        (∀ κ i (ρ : ℕ → Bool) p, p < n * entryBits n → cls (p / entryBits n) = κ →
          ψ κ i ρ p = ρ p) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        (∀ κ < K, ∀ x, applyRows n (entryBits n) (ψ κ) x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := noCode_colCover_of_noCode h k G c K hG hK
  refine ⟨n₀, fun n hn D hD hT cls hcls ψ hψ F hF => ?_⟩
  refine hn₀ n hn D hD hT cls hcls (fun κ x => applyRows n (entryBits n) (ψ κ) x)
    (fun κ => rowMapVis D n (entryBits n) (blockSize G n) (n * n * entryBits n) (ψ κ))
    (fun κ _ x u => rowMapVis_visible D n (entryBits n) (blockSize G n) (ψ κ) u x)
    (fun x d => ?_) F hF
  -- the copy of `d`'s column keeps `d`
  have hw : 0 < entryBits n := by unfold entryBits; omega
  have hdL : (d : ℕ) < n * n * entryBits n := d.2
  have hnw : 0 < n * entryBits n := by
    rcases Nat.eq_zero_or_pos (n * entryBits n) with h0 | h0
    · have : n * n * entryBits n = 0 := by rw [Nat.mul_assoc, h0, Nat.mul_zero]
      omega
    · exact h0
  have key1 : ∀ dd : ℕ, dd % (n * entryBits n) / entryBits n = dd / entryBits n % n := fun dd => by
    rw [Nat.mul_comm n (entryBits n), Nat.mod_mul_right_div_self]
  have key2 : ∀ dd : ℕ,
      dd / (n * entryBits n) * (n * entryBits n) + dd % (n * entryBits n) = dd := fun dd => by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have hp : (d : ℕ) % (n * entryBits n) < n * entryBits n := Nat.mod_lt _ hnw
  show ψ _ _ _ _ = _
  rw [hψ _ _ _ _ hp (by rw [key1])]
  simp only [rowBits, ite_eq_left hp]
  rw [key2]
  simp only [xbits, dite_eq_left hdL]

/-! ### Duplication: uniform column aggregates -/

/-- Column `j` of `x`, indexed by `i w + t` (bit `t` of entry `(i, j)`), `false` beyond `n w`. -/
def colBits (n w : ℕ) {L : ℕ} (x : Fin L → Bool) (j : ℕ) : ℕ → Bool :=
  fun p => if p < n * w then xbits x ((p / w * n + j) * w + p % w) else false

/-- Copy the left half of a row (positions `< h w`) onto its right half. -/
def dupLeft (h w : ℕ) (_i : ℕ) (ρ : ℕ → Bool) (p : ℕ) : Bool :=
  ρ (if p < h * w then p else p - h * w)

/-- Copy the right half of a row onto its left half. -/
def dupRight (h w : ℕ) (_i : ℕ) (ρ : ℕ → Bool) (p : ℕ) : Bool :=
  ρ (if p < h * w then p + h * w else p)

/-- A column of a row-mapped input, read through the row map. -/
theorem colBits_applyRows {n w : ℕ} (ψ : ℕ → (ℕ → Bool) → ℕ → Bool)
    (x : Fin (n * n * w) → Bool) {j : ℕ} (hj : j < n) {p : ℕ} (hp : p < n * w) :
    colBits n w (applyRows n w ψ x) j p =
      ψ (p / w) (rowBits n w (xbits x) (p / w)) (j * w + p % w) := by
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; simp at hp
    · exact h0
  have hi : p / w < n := by rw [Nat.div_lt_iff_lt_mul hw]; exact hp
  have hjt : j * w + p % w < n * w := by
    have := Nat.mod_lt p hw
    calc j * w + p % w < j * w + w := by omega
      _ = (j + 1) * w := by ring
      _ ≤ n * w := Nat.mul_le_mul_right _ hj
  have e : (p / w * n + j) * w + p % w = p / w * (n * w) + (j * w + p % w) := by ring
  have hd : (p / w * n + j) * w + p % w < n * n * w := by
    rw [e]
    calc p / w * (n * w) + (j * w + p % w) < p / w * (n * w) + n * w := by omega
      _ = (p / w + 1) * (n * w) := by ring
      _ ≤ n * (n * w) := Nat.mul_le_mul_right _ hi
      _ = n * n * w := by ring
  simp only [colBits, ite_eq_left hp, xbits, dite_eq_left hd, applyRows]
  have hdiv : ((p / w * n + j) * w + p % w) / (n * w) = p / w := by
    rw [e]; exact div_of_row_pos hjt
  have hmod : ((p / w * n + j) * w + p % w) % (n * w) = j * w + p % w := by
    rw [e, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjt]
  rw [hdiv, hmod]

/-- After `dupLeft`, column `h + j` equals column `j`. -/
theorem colBits_dupLeft {h w : ℕ} (x : Fin ((h + h) * (h + h) * w) → Bool) {j : ℕ} (hj : j < h) :
    colBits (h + h) w (applyRows (h + h) w (dupLeft h w) x) (h + j) =
      colBits (h + h) w (applyRows (h + h) w (dupLeft h w) x) j := by
  funext p
  by_cases hp : p < (h + h) * w
  · rw [colBits_applyRows _ x (by omega) hp, colBits_applyRows _ x (by omega) hp]
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · subst h0; simp at hp
      · exact h0
    have ht := Nat.mod_lt p hw
    simp only [dupLeft]
    have e1 : (h + j) * w = h * w + j * w := by ring
    have e2 : (j + 1) * w = j * w + w := by ring
    have e3 : (j + 1) * w ≤ h * w := Nat.mul_le_mul_right _ hj
    have h1 : ¬ (h + j) * w + p % w < h * w := by omega
    have h2 : j * w + p % w < h * w := by omega
    rw [ite_eq_right h1, ite_eq_left h2]
    congr 1
    have : (h + j) * w = h * w + j * w := by ring
    omega
  · simp only [colBits, ite_eq_right hp]

/-- After `dupRight`, column `h + j` equals column `j`. -/
theorem colBits_dupRight {h w : ℕ} (x : Fin ((h + h) * (h + h) * w) → Bool) {j : ℕ} (hj : j < h) :
    colBits (h + h) w (applyRows (h + h) w (dupRight h w) x) (h + j) =
      colBits (h + h) w (applyRows (h + h) w (dupRight h w) x) j := by
  funext p
  by_cases hp : p < (h + h) * w
  · rw [colBits_applyRows _ x (by omega) hp, colBits_applyRows _ x (by omega) hp]
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · subst h0; simp at hp
      · exact h0
    have ht := Nat.mod_lt p hw
    simp only [dupRight]
    have e1 : (h + j) * w = h * w + j * w := by ring
    have e2 : (j + 1) * w = j * w + w := by ring
    have e3 : (j + 1) * w ≤ h * w := Nat.mul_le_mul_right _ hj
    have h1 : ¬ (h + j) * w + p % w < h * w := by omega
    have h2 : j * w + p % w < h * w := by omega
    rw [ite_eq_right h1, ite_eq_left h2]
    congr 1
    ring
  · simp only [colBits, ite_eq_right hp]

/-- A column aggregate vanishes when column `h + j` equals column `j` for every `j < h`. -/
theorem colAgg_zero {h m : ℕ} (v : (ℕ → Bool) → (Fin m → ZMod 2)) (col : ℕ → ℕ → Bool)
    (hcol : ∀ j < h, col (h + j) = col j) :
    ∑ j ∈ Finset.range (h + h), v (col j) = 0 := by
  rw [Finset.sum_range_add]
  have e : ∑ x ∈ Finset.range h, v (col (h + x)) = ∑ x ∈ Finset.range h, v (col x) :=
    Finset.sum_congr rfl (fun j hj => by rw [hcol j (Finset.mem_range.1 hj)])
  rw [e]
  exact zmod2_vec_add_self _

/-- **Plain ⟹ no code on a set containing a uniform column aggregate's zero set (duplication).**
Under `NoCode_TM`, for all large even `n`: no code solves complete exchange at the profile capacities
on a set `F` containing `{x : Σ_j v(column j of x) = 0}`, for any `v` (the same for every column)
with values in `GF(2)^m`, any `m`. The inputs `[x_left | x_left]` and `[x_right | x_right]` lie in
the zero set (each term appears twice), and two copies, reading each output column from the copy
that keeps it, transpose every input. -/
theorem noCode_colAggregate_of_noCode (h : NoCode_TM) (k G c : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Even n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (m : ℕ) (v : (ℕ → Bool) → (Fin m → ZMod 2)) (F : Set (Fin (n * n * entryBits n) → Bool)),
        (∀ x, ∑ j ∈ Finset.range n, v (colBits n (entryBits n) x j) = 0 → x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := noCode_rowMapCover_of_noCode h k G c 2 hG (by norm_num)
  refine ⟨n₀, fun n hn hev D hD hT m v F hF code hsol => ?_⟩
  obtain ⟨h₂, rfl⟩ := hev
  have hw : 0 < entryBits (h₂ + h₂) := by unfold entryBits; omega
  refine hn₀ (h₂ + h₂) hn D hD hT (fun j => if j < h₂ then 0 else 1)
    (fun j _ => by split_ifs <;> norm_num)
    (fun κ => if κ = 0 then dupLeft h₂ (entryBits (h₂ + h₂)) else dupRight h₂ (entryBits (h₂ + h₂)))
    (fun κ i ρ p hp hcls => ?_) F (fun κ hκ x => ?_) code hsol
  · -- the row maps keep their own columns
    by_cases hlt : p / entryBits (h₂ + h₂) < h₂
    · rw [ite_eq_left hlt] at hcls
      subst hcls
      have : p < h₂ * entryBits (h₂ + h₂) := by rwa [Nat.div_lt_iff_lt_mul hw] at hlt
      simp only [ite_true, dupLeft, ite_eq_left this]
    · rw [ite_eq_right hlt] at hcls
      subst hcls
      have : ¬ p < h₂ * entryBits (h₂ + h₂) := by
        intro hp'; exact hlt ((Nat.div_lt_iff_lt_mul hw).2 hp')
      simp only [one_ne_zero, ite_false, dupRight, ite_eq_right this]
  · -- both duplicated inputs lie in `F`
    interval_cases κ
    · exact hF _ (colAgg_zero v _ (fun j hj => colBits_dupLeft x hj))
    · exact hF _ (colAgg_zero v _ (fun j hj => colBits_dupRight x hj))

end Transpose.Tape.Impl
