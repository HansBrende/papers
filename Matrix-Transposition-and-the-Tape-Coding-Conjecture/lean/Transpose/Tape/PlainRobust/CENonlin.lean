import Transpose.Tape.PlainRobust.CELinear

/-!
# Plain ⟹ robust for codes that are linear outside a small set of edges

A code is **linear outside `E_N`** (`NetCode.IsLinearExcept`) if every decoder, and the encoder of
every edge not in `E_N`, is XOR-linear; the values on `E_N` may be arbitrary functions of the values
into their tails. If `E_N` carries `O(n w)` bits at the profile capacities, the nonlinear values form
an internally computed hint of `O(n w)` bits:
* `hintedCode C E_N cap h` replaces the values on `E_N` by constants `h` and masks every value to its
  capacity. It is affine in the input (`hinted_decomp`), it agrees with `C` on every input within the
  capacities when `h` is `C`'s own values there (`hinted_agree`), and for `h = 0` it is linear;
* by pigeonhole, a `2^{-|E_N|}` fraction of the inputs on which `C` is correct share their values on
  `E_N`; XOR-ing them with one of them gives inputs on which `hintedCode C E_N cap 0` is correct
  (`hinted_zero_correct`);
* `noCode_linear_of_noCode` then applies (`noCode_linearExcept_of_noCode`).

This argument looks inside the code (which edges compute nonlinearly). A counterexample to plain ⟹
robust needs nonlinearity on `ω(n w)` bits of edge capacity.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-- A code is **linear outside the edges `E_N`**: every decoder, and the encoder of every edge not in
`E_N`, is XOR-linear in its inputs (in-values and visible bits). -/
def _root_.Transpose.Tape.NetCode.IsLinearExcept (C : NetCode) (EN : Finset (ℕ × ℕ)) : Prop :=
  (∀ e, e ∉ EN → ∀ (f f' : ℕ × ℕ → ℕ) (v v' : ℕ → Bool),
    C.enc e (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) = C.enc e f v ^^^ C.enc e f' v') ∧
  (∀ o (f f' : ℕ × ℕ → ℕ) (v v' : ℕ → Bool),
    C.dec o (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) =
      xor (C.dec o f v) (C.dec o f' v'))

/-- `C` with the values on `E_N` replaced by the constants `h`, and every value masked to `cap`. -/
def hintedCode (C : NetCode) (EN : Finset (ℕ × ℕ)) (cap : ℕ × ℕ → ℕ) (h : ℕ × ℕ → ℕ) :
    NetCode where
  enc e f v := (if e ∈ EN then h e else C.enc e f v) % 2 ^ cap e
  dec := C.dec

section Hinted

variable {C : NetCode} {EN : Finset (ℕ × ℕ)} (cap : ℕ × ℕ → ℕ)

theorem hinted_lt (h : ℕ × ℕ → ℕ) (e : ℕ × ℕ) (f : ℕ × ℕ → ℕ) (v : ℕ → Bool) :
    (hintedCode C EN cap h).enc e f v < 2 ^ cap e :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- With the constants `0` on `E_N`, the masked code is linear. -/
theorem hinted_zero_linear (hC : C.IsLinearExcept EN) :
    (hintedCode C EN cap (fun _ => 0)).IsLinear := by
  refine ⟨fun e f f' v v' => ?_, fun o f f' v v' => hC.2 o f f' v v'⟩
  show (if e ∈ EN then 0 else C.enc e _ _) % 2 ^ cap e =
    (if e ∈ EN then 0 else C.enc e f v) % 2 ^ cap e ^^^
      (if e ∈ EN then 0 else C.enc e f' v') % 2 ^ cap e
  by_cases he : e ∈ EN
  · simp [he]
  · rw [ite_eq_right he, ite_eq_right he, ite_eq_right he, hC.1 e he, Nat.xor_mod_two_pow]

/-- **The masked code is affine in the input**: its values with constants `h` on input `vis ⊕ vis'`
are its values with constants `0` on `vis`, XOR its values with constants `h` on `vis'`. -/
theorem hinted_decomp (hC : C.IsLinearExcept EN) (h : ℕ × ℕ → ℕ) (E : Finset (ℕ × ℕ))
    (vis vis' : ℕ → ℕ → Bool) :
    ∀ u, (hintedCode C EN cap h).inVals E (fun y d => xor (vis y d) (vis' y d)) u =
      fun e => (hintedCode C EN cap (fun _ => 0)).inVals E vis u e ^^^
        (hintedCode C EN cap h).inVals E vis' u e := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]
    show (if e ∈ EN then h e else C.enc e _ _) % 2 ^ cap e =
      (if e ∈ EN then 0 else C.enc e _ _) % 2 ^ cap e ^^^
        (if e ∈ EN then h e else C.enc e _ _) % 2 ^ cap e
    by_cases he : e ∈ EN
    · simp [he]
    · rw [ite_eq_right he, ite_eq_right he, ite_eq_right he, hC.1 e he, Nat.xor_mod_two_pow]
  · rfl

/-- **The masked code agrees with `C`** on an input within the capacities, when its constants on
`E_N` are `C`'s own values there (modulo the capacity). -/
theorem hinted_agree (h : ℕ × ℕ → ℕ) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool)
    (hcap : ∀ e ∈ E, C.edgeVal E vis e < 2 ^ cap e)
    (hh : ∀ e ∈ E, e ∈ EN → h e % 2 ^ cap e = C.edgeVal E vis e) :
    ∀ u, (hintedCode C EN cap h).inVals E vis u = C.inVals E vis u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]
    show (if e ∈ EN then h e else C.enc e _ _) % 2 ^ cap e = _
    by_cases he : e ∈ EN
    · rw [ite_eq_left he, hh e hc.1 he]
      rfl
    · rw [ite_eq_right he]
      exact Nat.mod_eq_of_lt (hcap e hc.1)
  · rfl

end Hinted

/-! ### Two inputs with the same nonlinear values -/

theorem bool_xor_cancel (a b k : Bool) : xor a b = xor (xor a k) (xor b k) := by
  cases a <;> cases b <;> cases k <;> rfl

section Same

variable {k : ℕ} (D : TSDiagram k) {n G : ℕ} {C : NetCode} {EN : Finset (ℕ × ℕ)}

/-- **The XOR of two inputs with the same nonlinear values is solved by the linear part.** If `C`
solves `x` and `x₀` at the profile capacities and its values on `E_N` agree on them modulo the
capacities, then `hintedCode C E_N cap 0` solves `x ⊕ x₀`. -/
theorem hinted_zero_correct (hC : C.IsLinearExcept EN) {x x₀ : Fin (n * n * entryBits n) → Bool}
    (hx : D.Solves n G (D.profileCap n G) {x} C) (hx₀ : D.Solves n G (D.profileCap n G) {x₀} C)
    (hsame : ∀ e ∈ EN,
      C.edgeVal (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x) e % 2 ^ D.profileCap n G e =
        C.edgeVal (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x₀) e % 2 ^ D.profileCap n G e) :
    D.Solves n G (D.profileCap n G) {xorVec x x₀} (hintedCode C EN (D.profileCap n G) (fun _ => 0)) := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨hcx, hox⟩ := hx x (Set.mem_singleton x)
  obtain ⟨hcx₀, hox₀⟩ := hx₀ x₀ (Set.mem_singleton x₀)
  set E := D.edges (blockSize G n)
  set cap := D.profileCap n G
  set visx := fun y => D.visible n (entryBits n) (blockSize G n) y x
  set visx₀ := fun y => D.visible n (entryBits n) (blockSize G n) y x₀
  set vis0 : ℕ → ℕ → Bool := fun _ _ => false
  -- the constants: `C`'s values on `x₀`
  set h : ℕ × ℕ → ℕ := fun e => C.edgeVal E visx₀ e
  have hagx : ∀ u, (hintedCode C EN cap h).inVals E visx u = C.inVals E visx u :=
    hinted_agree cap h E visx hcx (fun e he heN => by
      show C.edgeVal E visx₀ e % 2 ^ cap e = C.edgeVal E visx e
      rw [← hsame e heN, Nat.mod_eq_of_lt (hcx e he)])
  have hagx₀ : ∀ u, (hintedCode C EN cap h).inVals E visx₀ u = C.inVals E visx₀ u :=
    hinted_agree cap h E visx₀ hcx₀ (fun e he _ => Nat.mod_eq_of_lt (hcx₀ e he))
  -- affine decomposition
  have hv : ∀ vis : ℕ → ℕ → Bool, (fun y d => xor (vis y d) (vis0 y d)) = vis := by
    intro vis; funext y d; simp [vis0]
  have hdx : ∀ u, C.inVals E visx u = fun e =>
      (hintedCode C EN cap (fun _ => 0)).inVals E visx u e ^^^
        (hintedCode C EN cap h).inVals E vis0 u e := by
    intro u
    rw [← hagx u]
    have := hinted_decomp cap hC h E visx vis0 u
    rwa [hv] at this
  have hdx₀ : ∀ u, C.inVals E visx₀ u = fun e =>
      (hintedCode C EN cap (fun _ => 0)).inVals E visx₀ u e ^^^
        (hintedCode C EN cap h).inVals E vis0 u e := by
    intro u
    rw [← hagx₀ u]
    have := hinted_decomp cap hC h E visx₀ vis0 u
    rwa [hv] at this
  -- the linear part on `x ⊕ x₀`
  have hlin := hinted_zero_linear cap hC
  have hvisxor : (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x₀)) =
      fun y d => xor (visx y d) (visx₀ y d) := by
    funext y; exact visible_xorVec D _ _ _ y x x₀
  have hin := inVals_xor hlin E visx visx₀
  refine ⟨fun e _ => hinted_lt cap _ e _ _, fun d hd => ?_⟩
  show (hintedCode C EN cap (fun _ => 0)).dec _
      ((hintedCode C EN cap (fun _ => 0)).inVals E
        (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x₀)) _)
      ((fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x₀)) _) = _
  rw [hvisxor, hin]
  beta_reduce
  rw [hlin.2]
  -- `C`'s outputs on `x` and `x₀`, decomposed
  have hdec : ∀ o (f f' : ℕ × ℕ → ℕ) (v : ℕ → Bool),
      C.dec o (fun e => f e ^^^ f' e) v = xor (C.dec o f v) (C.dec o f' (fun _ => false)) := by
    intro o f f' v
    have := hC.2 o f f' v (fun _ => false)
    simp only [Bool.xor_false] at this
    exact this
  have h1 := hox d hd
  have h2 := hox₀ d hd
  simp only [NetCode.outVal] at h1 h2
  rw [hdx, hdec] at h1
  rw [hdx₀, hdec] at h2
  show xor (C.dec _ _ _) (C.dec _ _ _) = xorVec x x₀ ⟨d, hd⟩
  simp only [xorVec]
  rw [← h1, ← h2]
  exact bool_xor_cancel _ _ _

end Same

/-! ### Counting -/

/-- **Pigeonhole with powers of two.** If `2^a ≤ 2^b |s|` and `f` maps `s` into a set of at most `2^c`
values, some fiber `T` of `f` has `2^a ≤ 2^{b+c} |T|`. -/
theorem pigeon_pow {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) {a b c : ℕ} (hs : 2 ^ a ≤ 2 ^ b * s.card) (ht : t.card ≤ 2 ^ c) :
    ∃ y ∈ t, 2 ^ a ≤ 2 ^ (b + c) * (s.filter (fun x => f x = y)).card := by
  have hspos : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h0 | h0
    · rw [h0, Nat.mul_zero] at hs
      exact absurd hs (Nat.not_le.2 (Nat.two_pow_pos _))
    · exact h0
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hspos
  have htne : t.Nonempty := ⟨f a₀, hf a₀ ha₀⟩
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image t
    (fun y => (s.filter (fun x => f x = y)).card) htne
  refine ⟨y, hy, ?_⟩
  have hsum : s.card = ∑ y' ∈ t, (s.filter (fun x => f x = y')).card :=
    Finset.card_eq_sum_card_fiberwise hf
  have hle : ∑ y' ∈ t, (s.filter (fun x => f x = y')).card ≤
      t.card * (s.filter (fun x => f x = y)).card := by
    calc ∑ y' ∈ t, (s.filter (fun x => f x = y')).card
        ≤ ∑ _y' ∈ t, (s.filter (fun x => f x = y)).card := Finset.sum_le_sum (fun y' hy' => hmax y' hy')
      _ = t.card * (s.filter (fun x => f x = y)).card := by rw [Finset.sum_const, smul_eq_mul]
  calc 2 ^ a ≤ 2 ^ b * s.card := hs
    _ ≤ 2 ^ b * (t.card * (s.filter (fun x => f x = y)).card) := by
        rw [hsum]; exact Nat.mul_le_mul_left _ hle
    _ ≤ 2 ^ b * (2 ^ c * (s.filter (fun x => f x = y)).card) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ht)
    _ = 2 ^ (b + c) * (s.filter (fun x => f x = y)).card := by rw [pow_add]; ring

/-! ### Plain ⟹ no code that is linear outside `O(n w)` bits -/

/-- **Plain ⟹ no code that is linear outside a set of edges carrying `O(n w)` bits.** Under
`NoCode_TM`, for all constants and all large `n`: no code that is linear outside a set `E_N` of edges
with total profile capacity `≤ H n w` solves complete exchange at the profile capacities on a set `F`
of co-entropy `≤ C n w`. -/
theorem noCode_linearExcept_of_noCode (h : NoCode_TM) (k G c C H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ (code : NetCode) (EN : Finset (ℕ × ℕ)), code.IsLinearExcept EN →
        ∑ e ∈ EN, D.profileCap n G e ≤ H * n * entryBits n →
        ¬ D.Solves n G (D.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_linear_of_noCode h k G c (C + H) hG
  refine ⟨n₀, fun n hn D hD hT F hF code EN hlin hEN hsol => ?_⟩
  -- the values on `E_N`, modulo the capacities
  let hv : (Fin (n * n * entryBits n) → Bool) → ((e : EN) → Fin (2 ^ D.profileCap n G e.1)) :=
    fun x e => ⟨code.edgeVal (D.edges (blockSize G n))
      (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1 % 2 ^ D.profileCap n G e.1,
      Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have hcardT : (Finset.univ : Finset ((e : EN) → Fin (2 ^ D.profileCap n G e.1))).card =
      2 ^ ∑ e ∈ EN, D.profileCap n G e := by
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_coe_sort EN (fun e => 2 ^ D.profileCap n G e), Finset.prod_pow_eq_pow_sum]
  have hFcard : F.ncard = F.toFinset.card := Set.ncard_eq_toFinset_card' F
  obtain ⟨y, -, hy⟩ := pigeon_pow F.toFinset Finset.univ hv (fun _ _ => Finset.mem_univ _)
    (a := n * n * entryBits n) (b := C * n * entryBits n) (c := ∑ e ∈ EN, D.profileCap n G e)
    (by rw [← hFcard]; exact hF) (le_of_eq hcardT)
  set T := F.toFinset.filter (fun x => hv x = y) with hTdef
  have hTpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0, Nat.mul_zero] at hy
      exact absurd hy (Nat.not_le.2 (Nat.two_pow_pos _))
    · exact h0
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hTpos
  rw [hTdef, Finset.mem_filter, Set.mem_toFinset] at hx₀
  -- every `x ⊕ x₀`, `x ∈ T`, is solved by the linear part
  have hsolT : D.Solves n G (D.profileCap n G)
      ((T.image (fun x => xorVec x x₀) : Finset _) : Set (Fin (n * n * entryBits n) → Bool))
      (hintedCode code EN (D.profileCap n G) (fun _ => 0)) := by
    rw [solves_iff_forall_singleton]
    intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨x, hxT, rfl⟩ := hz
    rw [hTdef, Finset.mem_filter, Set.mem_toFinset] at hxT
    refine hinted_zero_correct D hlin ((solves_iff_forall_singleton D).1 hsol x hxT.1)
      ((solves_iff_forall_singleton D).1 hsol x₀ hx₀.1) (fun e he => ?_)
    have := congrArg (fun g => ((g ⟨e, he⟩ : Fin _) : ℕ)) (hxT.2.trans hx₀.2.symm)
    exact this
  -- the count
  have hinj : Function.Injective (fun x : Fin (n * n * entryBits n) → Bool => xorVec x x₀) := by
    intro a b hab
    have := congrArg (fun z => xorVec z x₀) hab
    simp only at this
    have e1 : ∀ z : Fin (n * n * entryBits n) → Bool, xorVec (xorVec z x₀) x₀ = z := by
      intro z; funext d; simp only [xorVec]; cases z d <;> cases x₀ d <;> rfl
    rwa [e1, e1] at this
  have hcount : 2 ^ (n * n * entryBits n) ≤ 2 ^ ((C + H) * n * entryBits n) *
      ((T.image (fun x => xorVec x x₀) : Finset _) : Set (Fin (n * n * entryBits n) → Bool)).ncard := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj]
    calc 2 ^ (n * n * entryBits n) ≤
        2 ^ (C * n * entryBits n + ∑ e ∈ EN, D.profileCap n G e) * T.card := hy
      _ ≤ 2 ^ ((C + H) * n * entryBits n) * T.card := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by norm_num)
          have : (C + H) * n * entryBits n = C * n * entryBits n + H * n * entryBits n := by ring
          omega
  exact hn₀ n hn D hD hT _ hcount _ (hinted_zero_linear _ hlin) hsolT

/-! ### Linear codes with few nonlinear correction bits -/

/-- A code is **linear plus the corrections `nl`**: on every edge, `enc ⊕ nl` is XOR-linear, and
every decoder is XOR-linear. With `nl e` of at most `b e` bits, the code is linear up to `Σ b e`
nonlinear bits, which may be spread over all edges. -/
def _root_.Transpose.Tape.NetCode.IsLinearPlus (C : NetCode)
    (nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) : Prop :=
  (∀ e (f f' : ℕ × ℕ → ℕ) (v v' : ℕ → Bool),
    C.enc e (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) ^^^
        nl e (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) =
      (C.enc e f v ^^^ nl e f v) ^^^ (C.enc e f' v' ^^^ nl e f' v')) ∧
  (∀ o (f f' : ℕ × ℕ → ℕ) (v v' : ℕ → Bool),
    C.dec o (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) =
      xor (C.dec o f v) (C.dec o f' v'))

/-- The linear part of `C` (`enc ⊕ nl`) plus the constants `h`, masked to `cap`. -/
def plusCode (C : NetCode) (nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (cap : ℕ × ℕ → ℕ)
    (h : ℕ × ℕ → ℕ) : NetCode where
  enc e f v := (C.enc e f v ^^^ nl e f v ^^^ h e) % 2 ^ cap e
  dec := C.dec

section Plus

variable {C : NetCode} {nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ} (cap : ℕ × ℕ → ℕ)

theorem plus_zero_linear (hC : C.IsLinearPlus nl) : (plusCode C nl cap (fun _ => 0)).IsLinear := by
  refine ⟨fun e f f' v v' => ?_, fun o f f' v v' => hC.2 o f f' v v'⟩
  show (C.enc e _ _ ^^^ nl e _ _ ^^^ 0) % 2 ^ cap e =
    (C.enc e f v ^^^ nl e f v ^^^ 0) % 2 ^ cap e ^^^ (C.enc e f' v' ^^^ nl e f' v' ^^^ 0) % 2 ^ cap e
  simp only [Nat.xor_zero]
  rw [hC.1 e f f' v v', Nat.xor_mod_two_pow]

theorem plus_decomp (hC : C.IsLinearPlus nl) (h : ℕ × ℕ → ℕ) (E : Finset (ℕ × ℕ))
    (vis vis' : ℕ → ℕ → Bool) :
    ∀ u, (plusCode C nl cap h).inVals E (fun y d => xor (vis y d) (vis' y d)) u =
      fun e => (plusCode C nl cap (fun _ => 0)).inVals E vis u e ^^^
        (plusCode C nl cap h).inVals E vis' u e := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]
    show (C.enc e _ _ ^^^ nl e _ _ ^^^ h e) % 2 ^ cap e =
      (C.enc e _ _ ^^^ nl e _ _ ^^^ 0) % 2 ^ cap e ^^^ (C.enc e _ _ ^^^ nl e _ _ ^^^ h e) % 2 ^ cap e
    rw [hC.1 e, Nat.xor_zero, ← Nat.xor_mod_two_pow, Nat.xor_assoc]
  · rfl

theorem plus_agree (h : ℕ × ℕ → ℕ) (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool)
    (hcap : ∀ e ∈ E, C.edgeVal E vis e < 2 ^ cap e)
    (hh : ∀ e ∈ E, h e = nl e (C.inVals E vis e.1) (vis e.1)) :
    ∀ u, (plusCode C nl cap h).inVals E vis u = C.inVals E vis u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]
    show (C.enc e _ _ ^^^ nl e _ _ ^^^ h e) % 2 ^ cap e = _
    rw [hh e hc.1, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact Nat.mod_eq_of_lt (hcap e hc.1)
  · rfl

end Plus

/-- **The XOR of two inputs with the same corrections is solved by the linear part.** -/
theorem plus_zero_correct {k : ℕ} (D : TSDiagram k) {n G : ℕ} {C : NetCode}
    {nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ} (hC : C.IsLinearPlus nl)
    {x x₀ : Fin (n * n * entryBits n) → Bool}
    (hx : D.Solves n G (D.profileCap n G) {x} C) (hx₀ : D.Solves n G (D.profileCap n G) {x₀} C)
    (hsame : ∀ e ∈ D.edges (blockSize G n),
      nl e (C.inVals (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1)
        (D.visible n (entryBits n) (blockSize G n) e.1 x) =
      nl e (C.inVals (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x₀) e.1)
        (D.visible n (entryBits n) (blockSize G n) e.1 x₀)) :
    D.Solves n G (D.profileCap n G) {xorVec x x₀}
      (plusCode C nl (D.profileCap n G) (fun _ => 0)) := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨hcx, hox⟩ := hx x (Set.mem_singleton x)
  obtain ⟨hcx₀, hox₀⟩ := hx₀ x₀ (Set.mem_singleton x₀)
  set E := D.edges (blockSize G n)
  set cap := D.profileCap n G
  set visx := fun y => D.visible n (entryBits n) (blockSize G n) y x
  set visx₀ := fun y => D.visible n (entryBits n) (blockSize G n) y x₀
  set vis0 : ℕ → ℕ → Bool := fun _ _ => false
  set h : ℕ × ℕ → ℕ := fun e => nl e (C.inVals E visx₀ e.1) (visx₀ e.1)
  have hagx : ∀ u, (plusCode C nl cap h).inVals E visx u = C.inVals E visx u :=
    plus_agree cap h E visx hcx (fun e he => (hsame e he).symm)
  have hagx₀ : ∀ u, (plusCode C nl cap h).inVals E visx₀ u = C.inVals E visx₀ u :=
    plus_agree cap h E visx₀ hcx₀ (fun e _ => rfl)
  have hv : ∀ vis : ℕ → ℕ → Bool, (fun y d => xor (vis y d) (vis0 y d)) = vis := by
    intro vis; funext y d; simp [vis0]
  have hdx : ∀ u, C.inVals E visx u = fun e =>
      (plusCode C nl cap (fun _ => 0)).inVals E visx u e ^^^ (plusCode C nl cap h).inVals E vis0 u e := by
    intro u
    rw [← hagx u]
    have := plus_decomp cap hC h E visx vis0 u
    rwa [hv] at this
  have hdx₀ : ∀ u, C.inVals E visx₀ u = fun e =>
      (plusCode C nl cap (fun _ => 0)).inVals E visx₀ u e ^^^ (plusCode C nl cap h).inVals E vis0 u e := by
    intro u
    rw [← hagx₀ u]
    have := plus_decomp cap hC h E visx₀ vis0 u
    rwa [hv] at this
  have hlin := plus_zero_linear cap hC
  have hvisxor : (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x₀)) =
      fun y d => xor (visx y d) (visx₀ y d) := by
    funext y; exact visible_xorVec D _ _ _ y x x₀
  have hin := inVals_xor hlin E visx visx₀
  refine ⟨fun e _ => Nat.mod_lt _ (Nat.two_pow_pos _), fun d hd => ?_⟩
  show (plusCode C nl cap (fun _ => 0)).dec _
      ((plusCode C nl cap (fun _ => 0)).inVals E
        (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x₀)) _)
      ((fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x₀)) _) = _
  rw [hvisxor, hin]
  beta_reduce
  rw [hlin.2]
  have hdec : ∀ o (f f' : ℕ × ℕ → ℕ) (v : ℕ → Bool),
      C.dec o (fun e => f e ^^^ f' e) v = xor (C.dec o f v) (C.dec o f' (fun _ => false)) := by
    intro o f f' v
    have := hC.2 o f f' v (fun _ => false)
    simp only [Bool.xor_false] at this
    exact this
  have h1 := hox d hd
  have h2 := hox₀ d hd
  simp only [NetCode.outVal] at h1 h2
  rw [hdx, hdec] at h1
  rw [hdx₀, hdec] at h2
  show xor (C.dec _ _ _) (C.dec _ _ _) = xorVec x x₀ ⟨d, hd⟩
  simp only [xorVec]
  rw [← h1, ← h2]
  exact bool_xor_cancel _ _ _

/-- **Plain ⟹ no linear code with `O(n w)` nonlinear correction bits.** Under `NoCode_TM`, for all
constants and all large `n`: no code that is linear plus corrections `nl` with `nl e < 2^{b e}` on
every edge of the diagram, `Σ_e b e ≤ H n w`, solves complete exchange at the profile capacities on a
set of co-entropy `≤ C n w`. The corrections may sit on every edge, e.g. `O(w)` nonlinear bits per
node. -/
theorem noCode_linearPlus_of_noCode (h : NoCode_TM) (k G c C H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ (code : NetCode) (nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (b : ℕ × ℕ → ℕ),
        code.IsLinearPlus nl → (∀ e f v, nl e f v < 2 ^ b e) →
        ∑ e ∈ D.edges (blockSize G n), b e ≤ H * n * entryBits n →
        ¬ D.Solves n G (D.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_linear_of_noCode h k G c (C + H) hG
  refine ⟨n₀, fun n hn D hD hT F hF code nl b hlin hnl hb hsol => ?_⟩
  set E := D.edges (blockSize G n)
  -- the corrections on the edges
  let hv : (Fin (n * n * entryBits n) → Bool) → ((e : E) → Fin (2 ^ b e.1)) :=
    fun x e => ⟨nl e.1 (code.inVals E (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1.1)
      (D.visible n (entryBits n) (blockSize G n) e.1.1 x), hnl _ _ _⟩
  have hcardT : (Finset.univ : Finset ((e : E) → Fin (2 ^ b e.1))).card = 2 ^ ∑ e ∈ E, b e := by
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_coe_sort E (fun e => 2 ^ b e), Finset.prod_pow_eq_pow_sum]
  have hFcard : F.ncard = F.toFinset.card := Set.ncard_eq_toFinset_card' F
  obtain ⟨y, -, hy⟩ := pigeon_pow F.toFinset Finset.univ hv (fun _ _ => Finset.mem_univ _)
    (a := n * n * entryBits n) (b := C * n * entryBits n) (c := ∑ e ∈ E, b e)
    (by rw [← hFcard]; exact hF) (le_of_eq hcardT)
  set T := F.toFinset.filter (fun x => hv x = y) with hTdef
  have hTpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0, Nat.mul_zero] at hy
      exact absurd hy (Nat.not_le.2 (Nat.two_pow_pos _))
    · exact h0
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hTpos
  rw [hTdef, Finset.mem_filter, Set.mem_toFinset] at hx₀
  have hsolT : D.Solves n G (D.profileCap n G)
      ((T.image (fun x => xorVec x x₀) : Finset _) : Set (Fin (n * n * entryBits n) → Bool))
      (plusCode code nl (D.profileCap n G) (fun _ => 0)) := by
    rw [solves_iff_forall_singleton]
    intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨x, hxT, rfl⟩ := hz
    rw [hTdef, Finset.mem_filter, Set.mem_toFinset] at hxT
    refine plus_zero_correct D hlin ((solves_iff_forall_singleton D).1 hsol x hxT.1)
      ((solves_iff_forall_singleton D).1 hsol x₀ hx₀.1) (fun e he => ?_)
    have := congrArg (fun g => ((g ⟨e, he⟩ : Fin _) : ℕ)) (hxT.2.trans hx₀.2.symm)
    exact this
  have hinj : Function.Injective (fun x : Fin (n * n * entryBits n) → Bool => xorVec x x₀) := by
    intro a b' hab
    have := congrArg (fun z => xorVec z x₀) hab
    simp only at this
    have e1 : ∀ z : Fin (n * n * entryBits n) → Bool, xorVec (xorVec z x₀) x₀ = z := by
      intro z; funext d; simp only [xorVec]; cases z d <;> cases x₀ d <;> rfl
    rwa [e1, e1] at this
  have hcount : 2 ^ (n * n * entryBits n) ≤ 2 ^ ((C + H) * n * entryBits n) *
      ((T.image (fun x => xorVec x x₀) : Finset _) : Set (Fin (n * n * entryBits n) → Bool)).ncard := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj]
    calc 2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n + ∑ e ∈ E, b e) * T.card := hy
      _ ≤ 2 ^ ((C + H) * n * entryBits n) * T.card := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by norm_num)
          have : (C + H) * n * entryBits n = C * n * entryBits n + H * n * entryBits n := by ring
          omega
  exact hn₀ n hn D hD hT _ hcount _ (plus_zero_linear _ hlin) hsolT

/-- **Plain ⟹ no linear code whose corrections take few values.** Under `NoCode_TM`, for all
constants and all large `n`: no code that is linear plus corrections `nl` (`NetCode.IsLinearPlus`),
whose correction vector (the corrections on the edges of the diagram) takes at most `2^{H n w}`
values on `F`, solves complete exchange at the profile capacities on a set `F` of co-entropy
`≤ C n w`. The corrections may be wide, as long as they have few patterns on `F`: for example, they
may be any functions of `O(1)` rows. -/
theorem noCode_linearPlusImage_of_noCode (h : NoCode_TM) (k G c C H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ (code : NetCode) (nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ),
        code.IsLinearPlus nl →
        ∀ (Tv : Finset (ℕ × ℕ → ℕ)), Tv.card ≤ 2 ^ (H * n * entryBits n) →
        (∀ x ∈ F, (fun e => if e ∈ D.edges (blockSize G n) then
            nl e (code.inVals (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1)
              (D.visible n (entryBits n) (blockSize G n) e.1 x) else 0) ∈ Tv) →
        ¬ D.Solves n G (D.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_linear_of_noCode h k G c (C + H) hG
  refine ⟨n₀, fun n hn D hD hT F hF code nl hlin Tv hTv hmem hsol => ?_⟩
  set E := D.edges (blockSize G n)
  let hv : (Fin (n * n * entryBits n) → Bool) → (ℕ × ℕ → ℕ) := fun x e =>
    if e ∈ E then nl e (code.inVals E (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1)
      (D.visible n (entryBits n) (blockSize G n) e.1 x) else 0
  have hFcard : F.ncard = F.toFinset.card := Set.ncard_eq_toFinset_card' F
  obtain ⟨y, -, hy⟩ := pigeon_pow F.toFinset Tv hv
    (fun x hx => hmem x (Set.mem_toFinset.1 hx))
    (a := n * n * entryBits n) (b := C * n * entryBits n) (c := H * n * entryBits n)
    (by rw [← hFcard]; exact hF) hTv
  set T := F.toFinset.filter (fun x => hv x = y) with hTdef
  have hTpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0, Nat.mul_zero] at hy
      exact absurd hy (Nat.not_le.2 (Nat.two_pow_pos _))
    · exact h0
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hTpos
  rw [hTdef, Finset.mem_filter, Set.mem_toFinset] at hx₀
  have hsolT : D.Solves n G (D.profileCap n G)
      ((T.image (fun x => xorVec x x₀) : Finset _) : Set (Fin (n * n * entryBits n) → Bool))
      (plusCode code nl (D.profileCap n G) (fun _ => 0)) := by
    rw [solves_iff_forall_singleton]
    intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨x, hxT, rfl⟩ := hz
    rw [hTdef, Finset.mem_filter, Set.mem_toFinset] at hxT
    refine plus_zero_correct D hlin ((solves_iff_forall_singleton D).1 hsol x hxT.1)
      ((solves_iff_forall_singleton D).1 hsol x₀ hx₀.1) (fun e he => ?_)
    have := congrFun (hxT.2.trans hx₀.2.symm) e
    simp only [hv] at this
    rwa [ite_eq_left he, ite_eq_left he] at this
  have hinj : Function.Injective (fun x : Fin (n * n * entryBits n) → Bool => xorVec x x₀) := by
    intro a b' hab
    have := congrArg (fun z => xorVec z x₀) hab
    simp only at this
    have e1 : ∀ z : Fin (n * n * entryBits n) → Bool, xorVec (xorVec z x₀) x₀ = z := by
      intro z; funext d; simp only [xorVec]; cases z d <;> cases x₀ d <;> rfl
    rwa [e1, e1] at this
  have hcount : 2 ^ (n * n * entryBits n) ≤ 2 ^ ((C + H) * n * entryBits n) *
      ((T.image (fun x => xorVec x x₀) : Finset _) : Set (Fin (n * n * entryBits n) → Bool)).ncard := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj]
    have e : (C + H) * n * entryBits n = C * n * entryBits n + H * n * entryBits n := by ring
    rw [e]
    exact hy
  exact hn₀ n hn D hD hT _ hcount _ (plus_zero_linear _ hlin) hsolT

end Transpose.Tape.Impl
