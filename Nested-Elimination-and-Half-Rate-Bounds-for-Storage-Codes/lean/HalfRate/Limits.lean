import HalfRate.Circulant
import HalfRate.Positional
import HalfRate.N3
import MotionDepthCodes.Petersen

/-!
# The explicit examples of the limits section

* `no_private_piece` (Proposition 7.1): in `Cay(Z₉, {1, -1, 3})` no set `∅ ≠ H ≠ Z₉` has
  private outside parents, by exhaustion over the 512 subsets.
* `ex72_decomp` (Example 7.2): the piece `{0, 1, 2, 3, 5, 6}` with co-supplied shared outside
  parents, followed by `{4}` and `{7, 8}`, is a decomposition.
* `z9_elimOn`, `x15_elimOn`, `c13_elimOn`: the global elimination certificates printed in the
  text for `Cay(Z₉, {1, -1, 3})`, for the 15-vertex relation `X₁₅` and for the chorded
  13-cycle, checked by `elimOn_ofFn`; hence the weighted half bound for each
  (`rateBound_of_elimOn_univ`).
* `cyc1`, …, `cyc11`: the other eleven chorded cycles of Remark 7.4, each a loopless TT-free
  chorded digon cycle (`IsChordedCycle`) with a three-record global elimination certificate.
* `x15_props`, `x15_oneWay_parents`, `x15_cores`: `X₁₅` is loopless and TT-free with in- and
  out-degrees at most three, vertex `6` has two one-way parents, and its unique minimum nonempty
  core is the hexagon `{0, …, 5}`.
-/

namespace HalfRate

open Finset MotionDepthCodes

section General

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- A global elimination certificate gives the weighted half bound. -/
theorem rateBound_of_elimOn_univ (c : ElimOn N univ) : RateBound N (1 / 2) := by
  obtain ⟨p⟩ := c.piece (R := univ) (fun _ _ _ _ _ _ _ _ h => absurd (mem_univ _) h)
    (fun _ h => absurd (mem_univ _) h)
  rw [sdiff_self] at p
  exact rateBound_of_decomp (pcs := [univ]) ⟨disjoint_empty_left _, ⟨p⟩, by simp [Decomp]⟩

end General

section Decide

variable {V : Type*} [DecidableEq V] [Fintype V]

instance (N : V → Finset V) : Decidable (TTFree N) := by
  unfold TTFree; infer_instance

end Decide

/-- A loopless TT-free chorded digon cycle on `Fin L`: `v - 1` and `v + 1` are parents of `v`, every
vertex has at most one further parent (a chord into it) and is the tail of at most one chord. -/
def IsChordedCycle {L : ℕ} [NeZero L] (N : Fin L → Finset (Fin L)) : Prop :=
  (∀ v, v ∉ N v) ∧ TTFree N ∧ (∀ v, v - 1 ∈ N v ∧ v + 1 ∈ N v) ∧ (∀ v, (N v).card ≤ 3) ∧
    ∀ v, (univ.filter (fun w => v ∈ N w)).card ≤ 3

instance {L : ℕ} [NeZero L] (N : Fin L → Finset (Fin L)) : Decidable (IsChordedCycle N) := by
  unfold IsChordedCycle; infer_instance

/-- The relation of `Cay(Z₉, {1, -1, 3})`: `N(q) = {q - 1, q + 1, q - 3}`. -/
def cay9 : ZMod 9 → Finset (ZMod 9) := fun q => {q - 1, q + 1, q - 3}

/-- **Proposition 7.1.** No set `H` with `∅ ≠ H ≠ Z₉` has (a) at most one parent outside `H` at
every vertex of `H` and (b) at most one child in `H` at every vertex outside `H`. -/
theorem no_private_piece : ∀ H : Finset (ZMod 9), H ≠ ∅ → H ≠ univ →
    ¬ ((∀ v ∈ H, ((cay9 v).filter (· ∉ H)).card ≤ 1) ∧
      ∀ w ∉ H, (H.filter (fun v => w ∈ cay9 v)).card ≤ 1) := by
  decide +kernel

/-- The global elimination certificate of `Cay(Z₉, {1, -1, 3})`: records `{0, 4}`,
`{1, 3, 6, 8}`, `{2, 5, 7}` and the list `0, 1, 2, 3, 4, 7, 5, 6, 8`. -/
theorem z9_elimOn : Nonempty (ElimOn cay9 univ) := by
  let f : Fin 9 → ZMod 9 := ![0, 1, 2, 3, 4, 7, 5, 6, 8]
  let col : ℕ → Fin 3 := fun i => ([0, 1, 2, 1, 0, 2, 2, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 2, 1, 0, 2, 1, 1, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 9, f i ∈ cay9 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cay9) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

/-- The weighted half bound for `Cay(Z₉, {1, -1, 3})` from its global certificate. -/
theorem rateBound_cay9 : RateBound cay9 (1 / 2) := by
  obtain ⟨c⟩ := z9_elimOn
  exact rateBound_of_elimOn_univ c

/-- The 15-vertex relation `X₁₅` of Remark 7.3. -/
def x15 : Fin 15 → Finset (Fin 15) :=
  ![{5, 1, 6}, {0, 2, 7}, {1, 3, 8}, {2, 4, 6}, {3, 5, 7}, {4, 0, 8}, {14, 0, 10}, {13, 4, 9},
    {9, 14, 5}, {6, 11, 7}, {9, 12}, {2, 13, 12}, {14, 11}, {1, 8, 11}, {3, 13, 12}]

/-- The global elimination certificate of `X₁₅` with three records: the records
`0,1,0,1,0,1,1,1,0,0,0,1,0,0,2` of the vertices `0, …, 14` and the list
`0,4,5,7,1,9,8,2,11,12,10,6,3,13,14`. -/
theorem x15_elimOn : Nonempty (ElimOn x15 univ) := by
  let f : Fin 15 → Fin 15 := ![0, 4, 5, 7, 1, 9, 8, 2, 11, 12, 10, 6, 3, 13, 14]
  let col : ℕ → Fin 3 := fun i =>
    ([0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 2] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i =>
    ([1, 1, 0, 0, 0, 1, 2, 1, 0, 2, 1, 2, 2, 1, 0] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ x15 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := x15) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

/-- **The weighted half bound for `X₁₅`.** -/
theorem rateBound_x15 : RateBound x15 (1 / 2) := by
  obtain ⟨c⟩ := x15_elimOn
  exact rateBound_of_elimOn_univ c

/-- The chorded digon 13-cycle of Remark 7.4: `v ± 1 → v` and the chords
`0→8, 1→6, 3→11, 4→0, 5→10, 6→9, 7→3, 8→4, 9→12, 10→1, 11→7, 12→2`. -/
def c13 : Fin 13 → Finset (Fin 13) :=
  ![{1, 4, 12}, {0, 2, 10}, {1, 3, 12}, {2, 4, 7}, {3, 5, 8}, {4, 6}, {1, 5, 7}, {6, 8, 11},
    {0, 7, 9}, {6, 8, 10}, {5, 9, 11}, {3, 10, 12}, {0, 9, 11}]

/-- `c13` is the stated cycle: its parents are the two cycle neighbours and the chord tails. -/
theorem c13_spec : ∀ v : Fin 13, c13 v =
    ({v - 1, v + 1} : Finset (Fin 13)) ∪
      ((([(0, 8), (1, 6), (3, 11), (4, 0), (5, 10), (6, 9), (7, 3), (8, 4), (9, 12), (10, 1),
        (11, 7), (12, 2)] : List (Fin 13 × Fin 13)).filter (fun e => e.2 = v)).map Prod.fst).toFinset := by
  decide

/-- The global elimination certificate of the chorded 13-cycle: the records
`0,2,0,1,0,2,1,2,1,2,1,2,1` of the vertices `0, …, 12` and the list
`11,9,7,6,5,4,10,1,2,0,8,3,12`. -/
theorem c13_elimOn : Nonempty (ElimOn c13 univ) := by
  let f : Fin 13 → Fin 13 := ![11, 9, 7, 6, 5, 4, 10, 1, 2, 0, 8, 3, 12]
  let col : ℕ → Fin 3 := fun i => ([2, 2, 2, 1, 2, 0, 1, 2, 0, 0, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 1, 2, 0, 1, 2, 0, 1, 1, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 13, f i ∈ c13 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := c13) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

/-- The displayed 13-cycle is a loopless TT-free chorded digon cycle. -/
theorem c13_isChordedCycle : IsChordedCycle c13 := by
  decide

/-- The weighted half bound for the displayed 13-cycle. -/
theorem rateBound_c13 : RateBound c13 (1 / 2) := by
  obtain ⟨c⟩ := c13_elimOn
  exact rateBound_of_elimOn_univ c

/-! ### The twelve chorded cycles of Remark 7.4

Each is a loopless TT-free chorded digon cycle (`IsChordedCycle`) with a three-record global
elimination certificate. -/

/-- Chorded cycle 1 of Remark 7.4 (length 13). -/
def cyc1 : Fin 13 → Finset (Fin 13) :=
  ![{1, 8, 12}, {0, 2, 5}, {1, 3, 7}, {0, 2, 4}, {3, 5, 12}, {4, 6, 10}, {3, 5, 7}, {6, 8, 11}, {4, 7, 9}, {6, 8, 10}, {1, 9, 11}, {2, 10, 12}, {0, 11}]

theorem cyc1_isChordedCycle : IsChordedCycle cyc1 := by
  decide

theorem cyc1_elimOn : Nonempty (ElimOn cyc1 univ) := by
  let f : Fin 13 → Fin 13 := ![0, 5, 1, 2, 11, 3, 9, 7, 6, 10, 12, 4, 8]
  let col : ℕ → Fin 3 := fun i => ([0, 2, 1, 0, 2, 2, 2, 2, 1, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 0, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 13, f i ∈ cyc1 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc1) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc1 : RateBound cyc1 (1 / 2) := by
  obtain ⟨c⟩ := cyc1_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 2 of Remark 7.4 (length 13). -/
def cyc2 : Fin 13 → Finset (Fin 13) :=
  ![{1, 9, 12}, {0, 2, 4}, {1, 3, 10}, {2, 4, 8}, {3, 5, 7}, {0, 4, 6}, {2, 5, 7}, {6, 8, 12}, {7, 9, 11}, {5, 8, 10}, {6, 9, 11}, {1, 10, 12}, {0, 3, 11}]

theorem cyc2_isChordedCycle : IsChordedCycle cyc2 := by
  decide

theorem cyc2_elimOn : Nonempty (ElimOn cyc2 univ) := by
  let f : Fin 13 → Fin 13 := ![11, 7, 2, 6, 5, 9, 0, 8, 3, 4, 1, 10, 12]
  let col : ℕ → Fin 3 := fun i => ([2, 2, 0, 1, 2, 2, 0, 1, 1, 0, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 1, 2, 0, 1, 1, 2, 0, 1, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 13, f i ∈ cyc2 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc2) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc2 : RateBound cyc2 (1 / 2) := by
  obtain ⟨c⟩ := cyc2_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 3 of Remark 7.4 (length 15). -/
def cyc3 : Fin 15 → Finset (Fin 15) :=
  ![{1, 6, 14}, {0, 2, 11}, {1, 3, 5}, {2, 4, 9}, {3, 5, 14}, {4, 6, 13}, {5, 7}, {3, 6, 8}, {1, 7, 9}, {0, 8, 10}, {9, 11}, {4, 10, 12}, {8, 11, 13}, {2, 12, 14}, {0, 7, 13}]

theorem cyc3_isChordedCycle : IsChordedCycle cyc3 := by
  decide

theorem cyc3_elimOn : Nonempty (ElimOn cyc3 univ) := by
  let f : Fin 15 → Fin 15 := ![0, 11, 9, 1, 2, 3, 7, 8, 10, 13, 5, 6, 12, 14, 4]
  let col : ℕ → Fin 3 := fun i => ([0, 2, 2, 1, 0, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 1, 0, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ cyc3 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc3) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc3 : RateBound cyc3 (1 / 2) := by
  obtain ⟨c⟩ := cyc3_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 4 of Remark 7.4 (length 15). -/
def cyc4 : Fin 15 → Finset (Fin 15) :=
  ![{1, 14}, {0, 2, 6}, {1, 3, 11}, {2, 4}, {3, 5, 9}, {4, 6, 14}, {5, 7, 13}, {6, 8, 12}, {2, 7, 9}, {1, 8, 10}, {9, 11}, {5, 10, 12}, {4, 11, 13}, {12, 14}, {0, 8, 13}]

theorem cyc4_isChordedCycle : IsChordedCycle cyc4 := by
  decide

theorem cyc4_elimOn : Nonempty (ElimOn cyc4 univ) := by
  let f : Fin 15 → Fin 15 := ![3, 2, 7, 13, 5, 6, 11, 1, 0, 9, 4, 8, 10, 12, 14]
  let col : ℕ → Fin 3 := fun i => ([2, 1, 2, 2, 2, 1, 2, 2, 0, 2, 1, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 2, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ cyc4 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc4) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc4 : RateBound cyc4 (1 / 2) := by
  obtain ⟨c⟩ := cyc4_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 5 of Remark 7.4 (length 15). -/
def cyc5 : Fin 15 → Finset (Fin 15) :=
  ![{1, 10, 14}, {0, 2, 9}, {1, 3, 8}, {2, 4, 14}, {3, 5, 12}, {4, 6, 11}, {5, 7}, {0, 6, 8}, {4, 7, 9}, {8, 10, 13}, {3, 9, 11}, {2, 10, 12}, {7, 11, 13}, {6, 12, 14}, {0, 5, 13}]

theorem cyc5_isChordedCycle : IsChordedCycle cyc5 := by
  decide

theorem cyc5_elimOn : Nonempty (ElimOn cyc5 univ) := by
  let f : Fin 15 → Fin 15 := ![0, 2, 11, 12, 4, 5, 6, 13, 9, 7, 1, 14, 3, 8, 10]
  let col : ℕ → Fin 3 := fun i => ([0, 2, 2, 1, 2, 1, 0, 2, 2, 2, 1, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 1, 2, 1, 0, 2, 1, 1, 1, 2, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ cyc5 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc5) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc5 : RateBound cyc5 (1 / 2) := by
  obtain ⟨c⟩ := cyc5_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 6 of Remark 7.4 (length 15). -/
def cyc6 : Fin 15 → Finset (Fin 15) :=
  ![{1, 9, 14}, {0, 2, 8}, {1, 3}, {2, 4, 12}, {3, 5, 11}, {2, 4, 6}, {0, 5, 7}, {6, 8}, {7, 9, 13}, {3, 8, 10}, {9, 11}, {1, 10, 12}, {6, 11, 13}, {5, 12, 14}, {0, 4, 13}]

theorem cyc6_isChordedCycle : IsChordedCycle cyc6 := by
  decide

theorem cyc6_elimOn : Nonempty (ElimOn cyc6 univ) := by
  let f : Fin 15 → Fin 15 := ![3, 2, 9, 5, 13, 7, 8, 1, 0, 6, 11, 4, 10, 12, 14]
  let col : ℕ → Fin 3 := fun i => ([2, 1, 2, 2, 2, 2, 1, 2, 0, 1, 2, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 2, 1, 1, 1, 1, 2, 0, 1, 2, 1, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ cyc6 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc6) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc6 : RateBound cyc6 (1 / 2) := by
  obtain ⟨c⟩ := cyc6_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 7 of Remark 7.4 (length 15). -/
def cyc7 : Fin 15 → Finset (Fin 15) :=
  ![{1, 9, 14}, {0, 2, 8}, {1, 3, 7}, {2, 4, 12}, {3, 5, 11}, {4, 6, 10}, {0, 5, 7}, {6, 8, 14}, {7, 9, 13}, {3, 8, 10}, {2, 9, 11}, {10, 12}, {6, 11, 13}, {12, 14}, {0, 4, 13}]

theorem cyc7_isChordedCycle : IsChordedCycle cyc7 := by
  decide

theorem cyc7_elimOn : Nonempty (ElimOn cyc7 univ) := by
  let f : Fin 15 → Fin 15 := ![3, 2, 9, 5, 13, 7, 8, 1, 0, 6, 11, 4, 10, 12, 14]
  let col : ℕ → Fin 3 := fun i => ([2, 1, 2, 2, 2, 2, 1, 2, 0, 1, 2, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 2, 1, 1, 1, 1, 2, 0, 1, 2, 1, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ cyc7 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc7) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc7 : RateBound cyc7 (1 / 2) := by
  obtain ⟨c⟩ := cyc7_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 8 of Remark 7.4 (length 15). -/
def cyc8 : Fin 15 → Finset (Fin 15) :=
  ![{1, 8, 14}, {0, 2, 7}, {1, 3, 12}, {2, 4, 6}, {3, 5, 10}, {0, 4, 6}, {5, 7, 14}, {6, 8}, {4, 7, 9}, {2, 8, 10}, {1, 9, 11}, {10, 12}, {5, 11, 13}, {9, 12, 14}, {0, 3, 13}]

theorem cyc8_isChordedCycle : IsChordedCycle cyc8 := by
  decide

theorem cyc8_elimOn : Nonempty (ElimOn cyc8 univ) := by
  let f : Fin 15 → Fin 15 := ![3, 2, 9, 13, 11, 5, 4, 12, 0, 14, 6, 7, 1, 10, 8]
  let col : ℕ → Fin 3 := fun i => ([2, 0, 2, 2, 2, 2, 0, 1, 0, 1, 0, 2, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([0, 1, 1, 1, 1, 0, 1, 2, 1, 2, 2, 1, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 15, f i ∈ cyc8 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc8) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc8 : RateBound cyc8 (1 / 2) := by
  obtain ⟨c⟩ := cyc8_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 9 of Remark 7.4 (length 16). -/
def cyc9 : Fin 16 → Finset (Fin 16) :=
  ![{1, 3, 15}, {0, 2, 9}, {1, 3, 7}, {2, 4, 13}, {3, 5}, {1, 4, 6}, {5, 7, 12}, {6, 8, 15}, {4, 7, 9}, {8, 10, 14}, {9, 11}, {2, 10, 12}, {8, 11, 13}, {0, 12, 14}, {5, 13, 15}, {0, 11, 14}]

theorem cyc9_isChordedCycle : IsChordedCycle cyc9 := by
  decide

theorem cyc9_elimOn : Nonempty (ElimOn cyc9 univ) := by
  let f : Fin 16 → Fin 16 := ![0, 4, 10, 14, 8, 9, 12, 2, 1, 11, 13, 3, 15, 6, 5, 7]
  let col : ℕ → Fin 3 := fun i => ([0, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 16, f i ∈ cyc9 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc9) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc9 : RateBound cyc9 (1 / 2) := by
  obtain ⟨c⟩ := cyc9_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 10 of Remark 7.4 (length 16). -/
def cyc10 : Fin 16 → Finset (Fin 16) :=
  ![{1, 7, 15}, {0, 2, 13}, {1, 3, 11}, {2, 4, 10}, {3, 5}, {4, 6, 15}, {5, 7, 14}, {6, 8, 12}, {7, 9}, {1, 8, 10}, {0, 9, 11}, {5, 10, 12}, {4, 11, 13}, {9, 12, 14}, {3, 13, 15}, {0, 8, 14}]

theorem cyc10_isChordedCycle : IsChordedCycle cyc10 := by
  decide

theorem cyc10_elimOn : Nonempty (ElimOn cyc10 univ) := by
  let f : Fin 16 → Fin 16 := ![8, 9, 14, 4, 12, 6, 7, 13, 1, 2, 0, 10, 3, 15, 5, 11]
  let col : ℕ → Fin 3 := fun i => ([2, 1, 2, 2, 2, 2, 1, 1, 2, 0, 0, 2, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 2, 1, 1, 1, 1, 2, 2, 0, 1, 1, 1, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 16, f i ∈ cyc10 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc10) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc10 : RateBound cyc10 (1 / 2) := by
  obtain ⟨c⟩ := cyc10_elimOn
  exact rateBound_of_elimOn_univ c

/-- Chorded cycle 11 of Remark 7.4 (length 16). -/
def cyc11 : Fin 16 → Finset (Fin 16) :=
  ![{1, 7, 15}, {0, 2, 11}, {1, 3, 15}, {2, 4, 10}, {3, 5, 9}, {4, 6, 13}, {5, 7, 14}, {6, 8, 12}, {2, 7, 9}, {0, 8, 10}, {6, 9, 11}, {5, 10, 12}, {3, 11, 13}, {1, 12, 14}, {8, 13, 15}, {0, 14}]

theorem cyc11_isChordedCycle : IsChordedCycle cyc11 := by
  decide

theorem cyc11_elimOn : Nonempty (ElimOn cyc11 univ) := by
  let f : Fin 16 → Fin 16 := ![0, 2, 8, 14, 3, 12, 7, 6, 10, 9, 4, 5, 11, 1, 13, 15]
  let col : ℕ → Fin 3 := fun i => ([0, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 0, 1, 1, 1, 1] : List (Fin 3)).getD i 0
  let bcol : ℕ → Fin 3 := fun i => ([1, 1, 1, 1, 2, 1, 2, 0, 1, 2, 0, 1, 2, 2, 2, 2] : List (Fin 3)).getD i 0
  have hstep : ∀ i j : Fin 16, f i ∈ cyc11 (f j) → i.val < j.val ∨ col i.val = bcol j.val := by
    decide
  have h := elimOn_ofFn (N := cyc11) (by norm_num) f (by decide) col bcol (by decide)
    fun i j hi hj h => hstep ⟨i, hi⟩ ⟨j, hj⟩ h
  rwa [show univ.image f = univ by decide] at h

theorem rateBound_cyc11 : RateBound cyc11 (1 / 2) := by
  obtain ⟨c⟩ := cyc11_elimOn
  exact rateBound_of_elimOn_univ c

/-- **The twelve chorded cycles of Remark 7.4.** Each is a loopless TT-free chorded digon cycle
and satisfies the weighted half bound, through its global elimination certificate. -/
theorem twelve_cycles :
    (IsChordedCycle c13 ∧ RateBound c13 (1 / 2)) ∧
    (IsChordedCycle cyc1 ∧ RateBound cyc1 (1 / 2)) ∧
    (IsChordedCycle cyc2 ∧ RateBound cyc2 (1 / 2)) ∧
    (IsChordedCycle cyc3 ∧ RateBound cyc3 (1 / 2)) ∧
    (IsChordedCycle cyc4 ∧ RateBound cyc4 (1 / 2)) ∧
    (IsChordedCycle cyc5 ∧ RateBound cyc5 (1 / 2)) ∧
    (IsChordedCycle cyc6 ∧ RateBound cyc6 (1 / 2)) ∧
    (IsChordedCycle cyc7 ∧ RateBound cyc7 (1 / 2)) ∧
    (IsChordedCycle cyc8 ∧ RateBound cyc8 (1 / 2)) ∧
    (IsChordedCycle cyc9 ∧ RateBound cyc9 (1 / 2)) ∧
    (IsChordedCycle cyc10 ∧ RateBound cyc10 (1 / 2)) ∧
    (IsChordedCycle cyc11 ∧ RateBound cyc11 (1 / 2)) :=
  ⟨⟨c13_isChordedCycle, rateBound_c13⟩, ⟨cyc1_isChordedCycle, rateBound_cyc1⟩, ⟨cyc2_isChordedCycle, rateBound_cyc2⟩, ⟨cyc3_isChordedCycle, rateBound_cyc3⟩, ⟨cyc4_isChordedCycle, rateBound_cyc4⟩, ⟨cyc5_isChordedCycle, rateBound_cyc5⟩, ⟨cyc6_isChordedCycle, rateBound_cyc6⟩, ⟨cyc7_isChordedCycle, rateBound_cyc7⟩, ⟨cyc8_isChordedCycle, rateBound_cyc8⟩, ⟨cyc9_isChordedCycle, rateBound_cyc9⟩, ⟨cyc10_isChordedCycle, rateBound_cyc10⟩, ⟨cyc11_isChordedCycle, rateBound_cyc11⟩⟩

/-! ### Facts about `X₁₅` -/

/-- `X₁₅` is loopless and TT-free, and every vertex has at most three parents and at most three
children. -/
theorem x15_props : (∀ v, v ∉ x15 v) ∧ TTFree x15 ∧ (∀ v, (x15 v).card ≤ 3) ∧
    ∀ v, (univ.filter (fun w => v ∈ x15 w)).card ≤ 3 := by
  decide

/-- Vertex `6` of `X₁₅` has the two one-way parents `10` and `14`. -/
theorem x15_oneWay_parents : 10 ∈ x15 6 ∧ 6 ∉ x15 10 ∧ 14 ∈ x15 6 ∧ 6 ∉ x15 14 := by
  decide

/-- The hexagon `{0, …, 5}` of `X₁₅`: it is a core (each of its vertices has at most one parent
outside it), its consecutive vertices form digons, and its outside parents `6`, `7`, `8` each have
two antipodal children in it. -/
theorem x15_hexagon :
    (∀ v ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 15)),
      ((x15 v).filter (· ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin 15)))).card ≤ 1) ∧
    (∀ p ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)] : List (Fin 15 × Fin 15)),
      p.1 ∈ x15 p.2 ∧ p.2 ∈ x15 p.1) ∧
    6 ∈ x15 0 ∧ 6 ∈ x15 3 ∧ 7 ∈ x15 1 ∧ 7 ∈ x15 4 ∧ 8 ∈ x15 2 ∧ 8 ∈ x15 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The cores of `X₁₅`.** A nonempty set in which every vertex has at most one parent outside
the set has at least six vertices, and the only one with six is the hexagon `{0, …, 5}`. By kernel
evaluation over all `2¹⁵` subsets (about four minutes). -/
theorem x15_cores : ∀ H : Finset (Fin 15), H.Nonempty →
    (∀ v ∈ H, ((x15 v).filter (· ∉ H)).card ≤ 1) →
      6 ≤ H.card ∧ (H.card = 6 → H = {0, 1, 2, 3, 4, 5}) := by
  decide +kernel

/-- The Petersen graph is triangle-free. -/
theorem petersen_cliqueFree : MotionDepthCodes.petersenGraph.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
  have key : ∀ a b c : Fin 10, b ∈ MotionDepthCodes.petersenNbhd a →
      c ∈ MotionDepthCodes.petersenNbhd a → c ∈ MotionDepthCodes.petersenNbhd b → False := by
    decide
  exact key a b c hab hac hbc

/-- **Theorem N3 decomposes the Petersen graph.** -/
theorem petersen_decomp : ∃ pcs, Decomp (nbhd MotionDepthCodes.petersenGraph) ∅ pcs := by
  have hdeg : ∀ v, (nbhd MotionDepthCodes.petersenGraph v).card ≤ 3 := by
    rw [MotionDepthCodes.nbhd_petersenGraph]
    decide
  obtain ⟨pcs, h⟩ := n3_decomp petersen_cliqueFree hdeg univ
  rw [sdiff_self] at h
  exact ⟨pcs, h⟩

/-! ### Example 7.2 -/

/-- The first piece of Example 7.2. -/
def exH1 : Finset (ZMod 9) := {0, 1, 2, 3, 5, 6}

/-- The piece certificate of Example 7.2: records `X = {0, 2, 6}`, `Y = {1, 3, 5}` and `Z = ∅`, the
list `2, 3, 5, 6, 0, 1` with supplying records `Y, X, X, Z, Y, Z`, and the outside parents `8`
(for `2` and `0`), `4` (for `3` and `5`) and `7` (for `6` and `1`), co-supplied. -/
def ex72Piece : PieceCert cay9 ∅ exH1 where
  m := 3
  P := ![{0, 2, 6}, {1, 3, 5}, ∅]
  disj := by decide
  cover := by decide
  l := [2, 3, 5, 6, 0, 1]
  hl := by decide
  a := fun v => if v ∈ ({0, 2, 6} : Finset (ZMod 9)) then 0 else 1
  b := fun v => if v = 2 ∨ v = 0 then 1 else if v = 3 ∨ v = 5 then 0 else 2
  par := fun v => if v = 2 ∨ v = 0 then some 8 else if v = 3 ∨ v = 5 then some 4
    else if v = 6 ∨ v = 1 then some 7 else none
  own := by decide
  ab := by decide
  charged := by
    refine relCharged_of_cosupply _ _ _ _ _ _ _ ∅ (fun _ => ∅) (by decide) (by decide) ?_
    have key : ∀ v v' w : ZMod 9,
        (if v = 2 ∨ v = 0 then some 8 else if v = 3 ∨ v = 5 then some 4
          else if v = 6 ∨ v = 1 then some 7 else none) = some w →
        (if v' = 2 ∨ v' = 0 then some 8 else if v' = 3 ∨ v' = 5 then some 4
          else if v' = 6 ∨ v' = 1 then some 7 else none) = some w →
        (if v = 2 ∨ v = 0 then (1 : Fin 3) else if v = 3 ∨ v = 5 then 0 else 2) =
          (if v' = 2 ∨ v' = 0 then (1 : Fin 3) else if v' = 3 ∨ v' = 5 then 0 else 2) := by
      decide
    exact fun j j' _ _ w h1 h2 => key _ _ w h1 h2

/-- The single-vertex piece `{4}` in the context `exH1`. -/
def ex72Piece4 : PieceCert cay9 exH1 {4} where
  m := 2
  P := ![{4}, ∅]
  disj := by decide
  cover := by decide
  l := [4]
  hl := by decide
  a := fun _ => 0
  b := fun _ => 1
  par := fun _ => none
  own := by decide
  ab := by decide
  charged := relCharged_of_cosupply _ _ _ _ _ _ _ ∅ (fun _ => ∅) (by decide) (by decide)
    (fun _ _ _ _ _ h _ => absurd h (by simp))

/-- The piece `{7, 8}` in the context `exH1 ∪ {4}`. -/
def ex72Piece78 : PieceCert cay9 (exH1 ∪ {4}) {7, 8} where
  m := 2
  P := ![{7}, {8}]
  disj := by decide
  cover := by decide
  l := [7, 8]
  hl := by decide
  a := fun v => if v = 7 then 0 else 1
  b := fun v => if v = 7 then 1 else 0
  par := fun _ => none
  own := by decide
  ab := by decide
  charged := relCharged_of_cosupply _ _ _ _ _ _ _ ∅ (fun _ => ∅) (by decide) (by decide)
    (fun _ _ _ _ _ h _ => absurd h (by simp))

/-- **Example 7.2.** `exH1`, `{4}`, `{7, 8}` is a decomposition of `Cay(Z₉, {1, -1, 3})` whose first
piece is proper and has shared outside parents. -/
theorem ex72_decomp : Decomp cay9 ∅ [exH1, {4}, {7, 8}] :=
  ⟨by decide, ⟨ex72Piece⟩, by decide, by rw [empty_union]; exact ⟨ex72Piece4⟩, by decide,
    by rw [empty_union]; exact ⟨ex72Piece78⟩,
    show (∅ ∪ exH1 ∪ {4} ∪ {7, 8} : Finset (ZMod 9)) = univ by decide⟩

end HalfRate
