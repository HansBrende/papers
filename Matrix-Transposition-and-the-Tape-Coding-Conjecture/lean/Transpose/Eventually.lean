import Transpose.Statement
import Transpose.Basic

/-!
# "Eventually linear" suffices

`LinearTimeTransposable` demands the bound `c * (L + 1)` for *every* `n ≥ 1`. For a correct machine
it is enough to have it for all large `n`: the finitely many small sizes have finitely many inputs,
each with a finite halting time, and `c` can be increased to cover them.
-/

namespace Transpose

/-- `ComputesWithin` is monotone in the time bound. -/
theorem ComputesWithin.mono {M : TM} {w out : List Bool} {t t' : Nat}
    (h : ComputesWithin M w out t) (htt : t ≤ t') : ComputesWithin M w out t' := by
  obtain ⟨s, hs, c, hc, hh, ho⟩ := h
  exact ⟨s, Nat.le_trans hs htt, c, hc, hh, ho⟩

/-- All boolean lists of length `L`. -/
def allBoolLists : Nat → List (List Bool)
  | 0 => [[]]
  | L + 1 => (allBoolLists L).flatMap (fun w => [true :: w, false :: w])

theorem mem_allBoolLists : ∀ (w : List Bool), w ∈ allBoolLists w.length
  | [] => by simp [allBoolLists]
  | b :: w => by
      simp only [List.length_cons, allBoolLists, List.mem_flatMap]
      refine ⟨w, mem_allBoolLists w, ?_⟩
      cases b <;> simp

/-- A finite family of existential time bounds has a uniform bound. -/
theorem exists_uniform_bound (P : List Bool → Nat → Prop)
    (hmono : ∀ w t t', P w t → t ≤ t' → P w t') :
    ∀ (ws : List (List Bool)), (∀ w ∈ ws, ∃ t, P w t) → ∃ T, ∀ w ∈ ws, P w T
  | [], _ => ⟨0, fun _ h => by simp at h⟩
  | w :: ws, h => by
      obtain ⟨t, ht⟩ := h w (by simp)
      obtain ⟨T, hT⟩ := exists_uniform_bound P hmono ws (fun w' hw' => h w' (by simp [hw']))
      refine ⟨max t T, fun w' hw' => ?_⟩
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact hmono _ _ _ ht (Nat.le_max_left _ _)
      · exact hmono _ _ _ (hT w' hw') (Nat.le_max_right _ _)

/-- Two matrices with the same encoding have the same encoded transpose: the machine's required
output is a function of its input word. -/
theorem concatUpTo_congr (f g : Nat → List Bool) :
    ∀ m, (∀ i, i < m → f i = g i) → concatUpTo f m = concatUpTo g m
  | 0, _ => rfl
  | m + 1, h => by
      simp only [concatUpTo]
      rw [concatUpTo_congr f g m (fun i hi => h i (Nat.lt_succ_of_lt hi)), h m (Nat.lt_succ_self m)]

theorem encode_eq_of_pointwise {n b : Nat} {A A' : Matrix}
    (h : ∀ i j t, i < n → j < n → t < b → A i j t = A' i j t) :
    encode n b A = encode n b A' := by
  unfold encode
  apply concatUpTo_congr
  intro i hi
  apply concatUpTo_congr
  intro j hj
  apply concatUpTo_congr
  intro t ht
  rw [h i j t hi hj ht]

/-- `encode` is injective on the relevant entries: position `(i*n + j)*b + t` holds `A i j t`. -/
theorem nth_concatUpTo_append (f : Nat → List Bool) (l : Nat) (hl : ∀ i, (f i).length = l) :
    ∀ m i p, i < m → p < l → nth (concatUpTo f m) (i * l + p) = nth (f i) p
  | 0, i, p, hi, _ => absurd hi (Nat.not_lt_zero _)
  | m + 1, i, p, hi, hp => by
      simp only [concatUpTo]
      have hlen : (concatUpTo f m).length = m * l := Sanity.length_concatUpTo f l hl m
      rcases Nat.lt_or_ge i m with him | him
      · rw [nth_eq_nth_append_left]
        · exact nth_concatUpTo_append f l hl m i p him hp
        · rw [hlen]
          calc i * l + p < i * l + l := Nat.add_lt_add_left hp _
            _ = (i + 1) * l := by rw [Nat.succ_mul]
            _ ≤ m * l := Nat.mul_le_mul_right l him
      · have hi' : i = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) him
        subst hi'
        rw [nth_eq_nth_append_right]
        · rw [hlen, Nat.add_sub_cancel_left]
        · rw [hlen]; exact Nat.le_add_right _ _
where
  nth_eq_nth_append_left (xs ys : List Bool) (p : Nat) (hp : p < xs.length) :
      nth (xs ++ ys) p = nth xs p := by
    induction xs generalizing p with
    | nil => simp at hp
    | cons x xs ih =>
      cases p with
      | zero => rfl
      | succ p => exact ih p (Nat.lt_of_succ_lt_succ hp)
  nth_eq_nth_append_right (xs ys : List Bool) (p : Nat) (hp : xs.length ≤ p) :
      nth (xs ++ ys) p = nth ys (p - xs.length) := by
    induction xs generalizing p with
    | nil => simp
    | cons x xs ih =>
      cases p with
      | zero => simp at hp
      | succ p =>
        show nth (xs ++ ys) p = nth ys (p + 1 - (xs.length + 1))
        rw [Nat.add_sub_add_right]
        exact ih p (Nat.le_of_succ_le_succ hp)

theorem nth_encode {n b : Nat} (A : Matrix) (i j t : Nat) (hi : i < n) (hj : j < n) (ht : t < b) :
    nth (encode n b A) ((i * n + j) * b + t) = some (A i j t) := by
  unfold encode
  have h1 : ∀ i, (concatUpTo (fun j => concatUpTo (fun t => [A i j t]) b) n).length = n * b :=
    fun i => Sanity.length_concatUpTo _ b (fun j => Sanity.length_concatUpTo _ 1 (fun _ => rfl) b |>.trans (Nat.mul_one b)) n
  have h2 : ∀ j, (concatUpTo (fun t => [A i j t]) b).length = b :=
    fun j => (Sanity.length_concatUpTo _ 1 (fun _ => rfl) b).trans (Nat.mul_one b)
  have e : (i * n + j) * b + t = i * (n * b) + (j * b + t) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  rw [e, nth_concatUpTo_append _ (n * b) h1 n i _ hi
        (by calc j * b + t < j * b + b := Nat.add_lt_add_left ht _
              _ = (j + 1) * b := by rw [Nat.succ_mul]
              _ ≤ n * b := Nat.mul_le_mul_right b hj),
      nth_concatUpTo_append _ b h2 n j t hj ht]
  show nth (concatUpTo (fun t => [A i j t]) b) t = some (A i j t)
  have h3 := nth_concatUpTo_append (fun t => [A i j t]) 1 (fun _ => rfl) b t 0 ht Nat.zero_lt_one
  simp only [Nat.mul_one, Nat.add_zero] at h3
  rw [h3]
  rfl

theorem pointwise_of_encode_eq {n b : Nat} {A A' : Matrix} (h : encode n b A = encode n b A') :
    ∀ i j t, i < n → j < n → t < b → A i j t = A' i j t := by
  intro i j t hi hj ht
  have this : nth (encode n b A) ((i * n + j) * b + t) = nth (encode n b A') ((i * n + j) * b + t) :=
    congrArg (fun w => nth w ((i * n + j) * b + t)) h
  rw [nth_encode A i j t hi hj ht, nth_encode A' i j t hi hj ht] at this
  exact Option.some.inj this

theorem encode_transpose_eq_of_encode_eq {n b : Nat} {A A' : Matrix}
    (h : encode n b A = encode n b A') :
    encode n b (transpose A) = encode n b (transpose A') := by
  apply encode_eq_of_pointwise
  intro i j t hi hj ht
  exact pointwise_of_encode_eq h j i t hj hi ht

/-- Main result: a correct machine that is linear-time for all large `n` witnesses
`LinearTimeTransposable`. -/
theorem linearTimeTransposable_of_eventually (M : TM)
    (hcorrect : ∀ n, 1 ≤ n → ∀ A : Matrix, ∃ t,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A)) t)
    (c n₀ : Nat)
    (hlin : ∀ n, n₀ ≤ n → ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A))
        (c * (inputLength n + 1))) :
    LinearTimeTransposable := by
  -- For each small n, a uniform bound over all inputs of that size.
  have hsmall : ∀ n, 1 ≤ n → ∃ T, ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A)) T := by
    intro n hn
    -- P w t: the machine, on input word w, produces the transpose-encoding of *some* matrix
    -- encoding to w, within t steps. Since that output is determined by w, this is well-defined.
    let P : List Bool → Nat → Prop := fun w t =>
      ∀ A : Matrix, encode n (entryBits n) A = w →
        ComputesWithin M w (encode n (entryBits n) (transpose A)) t
    have hmono : ∀ w t t', P w t → t ≤ t' → P w t' :=
      fun w t t' h htt A hA => (h A hA).mono htt
    obtain ⟨T, hT⟩ := exists_uniform_bound P hmono (allBoolLists (inputLength n)) (by
      intro w hw
      -- either some matrix encodes to w, or none does (then P w 0 holds vacuously)
      by_cases hex : ∃ A : Matrix, encode n (entryBits n) A = w
      · obtain ⟨A, hA⟩ := hex
        obtain ⟨t, ht⟩ := hcorrect n hn A
        refine ⟨t, fun A' hA' => ?_⟩
        have := encode_transpose_eq_of_encode_eq (hA.trans hA'.symm)
        rw [← this, ← hA]
        exact ht
      · exact ⟨0, fun A hA => absurd ⟨A, hA⟩ hex⟩)
    refine ⟨T, fun A => ?_⟩
    have hw : encode n (entryBits n) A ∈ allBoolLists (inputLength n) := by
      have := mem_allBoolLists (encode n (entryBits n) A)
      rwa [Sanity.length_encode] at this
    exact hT _ hw A rfl
  -- Collect the bounds for n < n₀ into one constant.
  have hall : ∀ m, ∃ C, ∀ n, 1 ≤ n → n < m → ∀ A : Matrix,
      ComputesWithin M (encode n (entryBits n) A) (encode n (entryBits n) (transpose A))
        (C * (inputLength n + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨0, fun n _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨C, hC⟩ := ih
      by_cases hm : 1 ≤ m
      · obtain ⟨T, hT⟩ := hsmall m hm
        refine ⟨max C T, fun n hn hnm A => ?_⟩
        rcases Nat.lt_or_ge n m with h | h
        · exact (hC n hn h A).mono (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
        · have : n = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hnm) h
          subst this
          exact (hT A).mono (by
            calc T ≤ T * (inputLength n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
              _ ≤ max C T * (inputLength n + 1) := Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
      · refine ⟨C, fun n hn hnm A => ?_⟩
        have : n < m := by omega
        exact hC n hn this A
  obtain ⟨C, hC⟩ := hall n₀
  refine ⟨M, max C c, ?_⟩
  intro n hn A
  rcases Nat.lt_or_ge n n₀ with h | h
  · exact (hC n hn h A).mono (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · exact (hlin n h A).mono (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))

end Transpose
