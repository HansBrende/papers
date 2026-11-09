import CascadeObstruction.C5Stages

/-! The exact order and dyadic sizes of Cascade 5.  `K` is the number of
recursive levels, so the matrix dimension is `2^(K+1)`. -/

namespace CascadeObstruction.C5

set_option autoImplicit false

abbrev Key := ℕ × Fin 2

def inputLength (K b : ℕ) : ℕ := 2 ^ (2 * (K + 1)) * b

def size (K b r : ℕ) : ℕ := 2 ^ (2 * (K + 1) - r) * b

theorem inputLength_pos (K : ℕ) {b : ℕ} (hb : 0 < b) : 0 < inputLength K b := by
  unfold inputLength
  positivity

theorem size_pos (K r : ℕ) {b : ℕ} (hb : 0 < b) : 0 < size K b r := by
  unfold size
  positivity

theorem size_factor {K b r : ℕ} (hr : r ≤ 2 * (K + 1)) :
    inputLength K b = 2 ^ r * size K b r := by
  unfold inputLength size
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hr]

/-- The power expression is exactly the source's right shift, with no
rounding loss at the admitted dyadic depths. -/
theorem size_eq_shiftRight {K b r : ℕ} (hr : r ≤ 2 * (K + 1)) :
    size K b r = inputLength K b >>> r := by
  rw [Nat.shiftRight_eq_div_pow, size_factor hr, Nat.mul_div_cancel_left _ (by positivity)]

theorem size_double {K b r : ℕ} (hr : r + 1 ≤ 2 * (K + 1)) :
    size K b r = 2 * size K b (r + 1) := by
  unfold size
  rw [show 2 * (K + 1) - r = 1 + (2 * (K + 1) - (r + 1)) by omega, pow_add]
  simp [mul_assoc]

theorem size_tooth {K b r : ℕ} (hr : 2 * r ≤ 2 * (K + 1)) :
    size K b r = 2 ^ r * size K b (2 * r) := by
  unfold size
  rw [← mul_assoc, ← pow_add]
  congr 2
  omega

theorem half_size_eq_div {K b r : ℕ} (hr : r + 1 ≤ 2 * (K + 1)) :
    size K b (r + 1) = size K b r / 2 := by
  rw [size_double hr, Nat.mul_div_cancel_left _ (by omega)]

theorem tooth_size_eq_div {K b r : ℕ} (hr : 2 * r ≤ 2 * (K + 1)) :
    size K b (2 * r) = size K b r / 2 ^ r := by
  rw [size_tooth hr, Nat.mul_div_cancel_left _ (by positivity)]

theorem half_size_ge_two {K b r : ℕ} (hb : 0 < b) (hr : r ≤ K) :
    2 ≤ size K b (r + 1) := by
  have he : 1 ≤ 2 * (K + 1) - (r + 1) := by omega
  have hp : 2 ^ 1 ≤ 2 ^ (2 * (K + 1) - (r + 1)) := Nat.pow_le_pow_right (by omega) he
  unfold size
  simp only [pow_one] at hp
  nlinarith

/-- Chronological order: root preparation, forward depths 1..K, backward
depths K..1, then root output. -/
def keyAt (K : ℕ) (i : Fin (2 * (K + 1))) : Key :=
  if i.val ≤ K then (i.val, 0) else (2 * K + 1 - i.val, 1)

def keys (K : ℕ) : List Key := List.ofFn (keyAt K)

theorem keyAt_injective (K : ℕ) : Function.Injective (keyAt K) := by
  intro i j hij
  apply Fin.ext
  unfold keyAt at hij
  split_ifs at hij with hi hj hj
  · exact congrArg Prod.fst hij
  · have := congrArg Prod.snd hij
    norm_num at this
  · have := congrArg Prod.snd hij
    norm_num at this
  · have := congrArg Prod.fst hij
    have := i.isLt
    have := j.isLt
    omega

theorem keys_nodup (K : ℕ) : (keys K).Nodup := by
  exact List.nodup_ofFn.mpr (keyAt_injective K)

theorem keyAt_depth_le (K : ℕ) (i : Fin (2 * (K + 1))) : (keyAt K i).1 ≤ K := by
  unfold keyAt
  split_ifs with hi
  · exact hi
  · omega

theorem mem_keys_iff {K : ℕ} {key : Key} : key ∈ keys K ↔ key.1 ≤ K := by
  constructor
  · intro hk
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    exact keyAt_depth_le K i
  · intro hk
    rcases key with ⟨r, j⟩
    fin_cases j
    · apply List.mem_ofFn.mpr
      refine ⟨⟨r, by omega⟩, ?_⟩
      simp [keyAt, hk]
    · apply List.mem_ofFn.mpr
      refine ⟨⟨2 * K + 1 - r, by omega⟩, ?_⟩
      have hn : ¬2 * K + 1 - r ≤ K := by omega
      simp [keyAt, hn]
      omega

def stage (K b : ℕ) (key : Key) : List Block :=
  if key.1 = 0 then
    if key.2 = 0 then preparation (inputLength K b) else output (inputLength K b)
  else if key.2 = 0 then forward (size K b (key.1 + 1))
  else backward (size K b (key.1 + 1)) (2 ^ key.1) (size K b (2 * key.1))

def stages (K b : ℕ) : List (Key × ℕ) :=
  (keys K).map (fun key => (key, blocksDuration (stage K b key)))

def programBlocks (K b : ℕ) : List Block := (keys K).flatMap (stage K b)

/-- The literal finite physical trace. It includes every read/positioning
tick; the data rules attached later may write at every one of them. -/
def trace (K b : ℕ) : List Tick := expand (programBlocks K b)

theorem stage_pair_budget {K b r : ℕ} (hb : 0 < b) (hr : r ≤ K) :
    blocksDuration (stage K b (r, 0)) + blocksDuration (stage K b (r, 1)) ≤
      18 * size K b r := by
  by_cases hzero : r = 0
  · subst r
    have hL := inputLength_pos K hb
    simp only [stage, ↓reduceIte, Fin.isValue, one_ne_zero]
    rw [preparation_duration hL, output_duration hL]
    change 2 * inputLength K b - 1 + inputLength K b ≤ 18 * size K b 0
    have hs : size K b 0 = inputLength K b := by simp [size, inputLength]
    rw [hs]
    omega
  · have hN : 1 ≤ 2 ^ r := by
      have : 0 < 2 ^ r := by positivity
      omega
    have hprod : 2 * size K b (r + 1) = 2 ^ r * size K b (2 * r) := by
      rw [← size_double (by omega), size_tooth (by omega)]
    have h := stage_budget (half_size_ge_two hb hr) hN
      (size_pos K (2 * r) hb) hprod
    rw [← size_double (K := K) (b := b) (r := r) (by omega)] at h
    simpa [stage, hzero] using h

theorem stage_blocks_bound (K b r : ℕ) (j : Fin 2) :
    (stage K b (r, j)).length ≤ 4 * 2 ^ r + 13 := by
  by_cases hzero : r = 0
  · subst r
    fin_cases j <;> simp [stage, preparation, output]
  · have hN : 1 ≤ 2 ^ r := by
      have : 0 < 2 ^ r := by positivity
      omega
    fin_cases j
    · simp [stage, hzero]
    · simp [stage, hzero, backward_blocks hN]

end CascadeObstruction.C5
