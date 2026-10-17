import Transpose.Tape.PlainRobust.CEDegree

/-!
# Decomposition: plain ⟹ no code on a set containing every input supported on a part

Partition the input positions into `K` parts by a colouring `P`. If a set `F` contains every input
supported on a single part, a code `C` correct on `F` gives a code correct on **every** input:
* `kfoldTapes D K`: every work walk of `D` `K` times, so every profile capacity is multiplied by `K`
  (`profileCap_kfold`);
* copy `j` of `C` runs on the input with the positions outside part `j` masked to `0`
  (`maskPosCode`); that input lies in `F`, so copy `j` outputs its transpose;
* the outputs are XOR-ed, since transposition is linear (`sumCode`, `decomp_solves`).

So `NoCode_TM` rules out codes on every such set (`noCode_decomp_of_noCode`). For example, if every
monomial of a family of quadratic constraints joins two different parts, the common zero set contains
every input supported on one part (`noCode_crossQuad_of_noCode`). This covers any family of
constraints `Σ_{i<j} ⟨A_{k,ij} x_ij, x_ji⟩ = 0` with pair-dependent matrices `A_{k,ij}` (so `Θ(n w)`
independent ones exist), whose monomials join the upper and lower triangles. (With one matrix per
constraint, `Σ_{i<j} ⟨A_k x_ij, x_ji⟩` is linear in `A_k`, so such a family spans at most `w²` forms.)
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-! ### `K` copies of every walk -/

/-- Every work walk `K` times. -/
def kfoldTapes {k : ℕ} (D : TSDiagram k) (K : ℕ) : TSDiagram (K * k) where
  T := D.T
  work := fun t => D.work (finProdFinEquiv.symm t).2
  inp := D.inp
  out := D.out

section Kfold

variable {k : ℕ} (D : TSDiagram k) (K : ℕ)

theorem valid_kfold {L : ℕ} (hD : D.Valid L) : (kfoldTapes D K).Valid L :=
  ⟨fun _ => hD.1 _, hD.2⟩

theorem memEdges_kfold (r : ℕ) : (kfoldTapes D K).memEdges r = D.memEdges r := rfl

theorem chordEdges_kfold (hK : 1 ≤ K) (r : ℕ) : (kfoldTapes D K).chordEdges r = D.chordEdges r := by
  classical
  ext e
  rw [mem_chordEdges, mem_chordEdges]
  constructor
  · rintro ⟨h1, h2, t, β, hc⟩
    exact ⟨h1, h2, (finProdFinEquiv.symm t).2, β, hc⟩
  · rintro ⟨h1, h2, t, β, hc⟩
    refine ⟨h1, h2, finProdFinEquiv ((⟨0, hK⟩ : Fin K), t), β, ?_⟩
    show IsChord (pairRes r (D.work (finProdFinEquiv.symm
      (finProdFinEquiv ((⟨0, hK⟩ : Fin K), t))).2) D.T) β e.1 e.2
    rw [Equiv.symm_apply_apply]
    exact hc

theorem edges_kfold (hK : 1 ≤ K) (r : ℕ) : (kfoldTapes D K).edges r = D.edges r := by
  unfold TSDiagram.edges
  rw [memEdges_kfold, chordEdges_kfold D K hK]

theorem sum_kfold (f : Fin k → ℕ) :
    ∑ t : Fin (K * k), f (finProdFinEquiv.symm t).2 = K * ∑ t, f t := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp

theorem profileCap_kfold (hK : 1 ≤ K) (n G : ℕ) (e : ℕ × ℕ) :
    (kfoldTapes D K).profileCap n G e = K * D.profileCap n G e := by
  classical
  unfold TSDiagram.profileCap TSDiagram.blockCap
  beta_reduce
  have hres : ∑ t, (pairRes (blockSize G n) ((kfoldTapes D K).work t) (kfoldTapes D K).T
      e.1).card = K * ∑ t, (pairRes (blockSize G n) (D.work t) D.T e.1).card :=
    sum_kfold K (fun t => (pairRes (blockSize G n) (D.work t) D.T e.1).card)
  have hct : (kfoldTapes D K).chordTapes (blockSize G n) e = K * D.chordTapes (blockSize G n) e := by
    unfold TSDiagram.chordTapes
    rw [Finset.card_filter, Finset.card_filter]
    exact sum_kfold K (fun t => if ∃ β : ℤ, IsChord (pairRes (blockSize G n) (D.work t) D.T) β
      e.1 e.2 then 1 else 0)
  rw [memEdges_kfold, chordEdges_kfold D K hK, hres, hct]
  split_ifs <;> ring

end Kfold

/-! ### Masked copies -/

/-- The input with the positions outside part `j` of the colouring `P` set to `0`. -/
def xpart {L : ℕ} (x : Fin L → Bool) (P : ℕ → ℕ) (j : ℕ) : Fin L → Bool :=
  fun d => if P d = j then x d else false

/-- `C` run on the visible input masked to part `j`. -/
def maskPosCode (C : NetCode) (P : ℕ → ℕ) (j : ℕ) : NetCode where
  enc e f v := C.enc e f (fun d => if P d = j then v d else false)
  dec o f v := C.dec o f (fun d => if P d = j then v d else false)

theorem inVals_maskPos (C : NetCode) (P : ℕ → ℕ) (j : ℕ) (E : Finset (ℕ × ℕ))
    (vis : ℕ → ℕ → Bool) : ∀ u, (maskPosCode C P j).inVals E vis u =
      C.inVals E (fun y d => if P d = j then vis y d else false) u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]; rfl
  · rfl

theorem visible_xpart {k : ℕ} (D : TSDiagram k) (n w r y : ℕ) {L : ℕ} (x : Fin L → Bool)
    (P : ℕ → ℕ) (j : ℕ) :
    (fun d => if P d = j then D.visible n w r y x d else false) =
      D.visible n w r y (xpart x P j) := by
  funext d
  simp only [TSDiagram.visible, xpart]
  split_ifs <;> simp_all

/-! ### `K` masked copies side by side -/

/-- The XOR of `g 0, …, g (K-1)`. -/
def xorUpTo : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | K + 1, g => xor (xorUpTo K g) (g K)

theorem xorUpTo_single {g : ℕ → Bool} {j₀ : ℕ} :
    ∀ K, (∀ j < K, j ≠ j₀ → g j = false) → xorUpTo K g = if j₀ < K then g j₀ else false := by
  intro K
  induction K with
  | zero => intro _; simp [xorUpTo]
  | succ K ih =>
    intro hg
    simp only [xorUpTo, ih (fun j hj hj' => hg j (by omega) hj')]
    by_cases h1 : j₀ < K
    · rw [ite_eq_left h1, ite_eq_left (by omega), hg K (by omega) (by omega)]
      simp
    · by_cases h2 : j₀ = K
      · subst h2
        rw [ite_eq_right h1, ite_eq_left (by omega)]
        simp
      · rw [ite_eq_right h1, ite_eq_right (by omega), hg K (by omega) (Ne.symm (by omega))]
        rfl

section Sum

variable {k : ℕ} (D : TSDiagram k) (n G : ℕ) (P : ℕ → ℕ) (K : ℕ) (C : NetCode)

/-- **`K` masked copies side by side**: the clamped values of the copies are packed in base `2^c`;
every output bit is the XOR of the copies' decoded bits. -/
noncomputable def sumCode : NetCode where
  enc e f v := packK (D.profileCap n G e) K
    (fun j => (clampCode D n G (maskPosCode C P j)).enc e (fun e' => digit D n G j e' (f e')) v)
  dec o f v := xorUpTo K (fun j => (maskPosCode C P j).dec o (fun e' => digit D n G j e' (f e')) v)

/-- **Each digit carries its own copy.** -/
theorem sumCode_digits (E : Finset (ℕ × ℕ)) (vis : ℕ → ℕ → Bool) :
    ∀ u, ∀ j < K, (fun e' => digit D n G j e' ((sumCode D n G P K C).inVals E vis u e')) =
      (clampCode D n G (maskPosCode C P j)).inVals E vis u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro j hj
  funext e'
  rw [inVals_eq (clampCode D n G (maskPosCode C P j))]
  by_cases hc : e' ∈ E ∧ e'.2 = u ∧ e'.1 < u
  · rw [ite_eq_left hc, inVals_eq, ite_eq_left hc]
    show digit D n G j e' (packK (D.profileCap n G e') K (fun j' =>
      (clampCode D n G (maskPosCode C P j')).enc e' (fun e'' => digit D n G j' e''
        ((sumCode D n G P K C).inVals E vis e'.1 e'')) (vis e'.1))) = _
    have hdig : ∀ v : ℕ → ℕ, (∀ a < K, v a < 2 ^ D.profileCap n G e') →
        digit D n G j e' (packK (D.profileCap n G e') K v) = v j :=
      fun v hv => digit_packK hv hj
    rw [hdig _ (fun b _ => clamp_lt D n G _ _ _ _), ih e'.1 hc.2.2 j hj]
  · rw [ite_eq_right hc, inVals_eq, ite_eq_right hc]
    simp [digit]

end Sum

/-- **Decomposition.** If `C` solves complete exchange on `F` at the profile capacities of `D`, and
`F` contains every input supported on a single part of a colouring `P` with parts `< K`, then the
`K` masked copies side by side solve complete exchange on **every** input, on `kfoldTapes D K`. -/
theorem decomp_solves {k : ℕ} (D : TSDiagram k) {n G K : ℕ} (hK : 1 ≤ K) (P : ℕ → ℕ)
    {F : Set (Fin (n * n * entryBits n) → Bool)} {C : NetCode}
    (hsol : D.Solves n G (D.profileCap n G) F C)
    (hP : ∀ d < n * n * entryBits n, P d < K)
    (hF : ∀ j < K, ∀ x : Fin (n * n * entryBits n) → Bool, xpart x P j ∈ F) :
    (kfoldTapes D K).Solves n G ((kfoldTapes D K).profileCap n G) Set.univ (sumCode D n G P K C) := by
  intro x _
  have hE : (kfoldTapes D K).edges (blockSize G n) = D.edges (blockSize G n) := edges_kfold D K hK _
  have hvis : (fun y => (kfoldTapes D K).visible n (entryBits n) (blockSize G n) y x) =
      fun y => D.visible n (entryBits n) (blockSize G n) y x := rfl
  rw [hE, hvis]
  -- each copy, run on its part
  have hcopy : ∀ j < K,
      (∀ e ∈ D.edges (blockSize G n), (maskPosCode C P j).edgeVal (D.edges (blockSize G n))
        (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) ∧
      ∀ (d : ℕ) (hd : d < n * n * entryBits n),
        (maskPosCode C P j).outVal (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x)
          (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) =
            xpart x P j ⟨d, hd⟩ := by
    intro j hj
    obtain ⟨hc, ho⟩ := hsol (xpart x P j) (hF j hj x)
    have hin := inVals_maskPos C P j (D.edges (blockSize G n))
      (fun y => D.visible n (entryBits n) (blockSize G n) y x)
    have hvp : (fun y d => if P d = j then D.visible n (entryBits n) (blockSize G n) y x d
        else false) = fun y => D.visible n (entryBits n) (blockSize G n) y (xpart x P j) := by
      funext y; exact visible_xpart D n (entryBits n) (blockSize G n) y x P j
    refine ⟨fun e he => ?_, fun d hd => ?_⟩
    · show C.enc e ((maskPosCode C P j).inVals _ _ e.1)
        (fun d => if P d = j then D.visible n (entryBits n) (blockSize G n) e.1 x d else false) < _
      rw [hin, hvp, visible_xpart]
      exact hc e he
    · show C.dec _ ((maskPosCode C P j).inVals _ _ _)
        (fun d => if P d = j then D.visible n (entryBits n) (blockSize G n) _ x d else false) = _
      rw [hin, hvp, visible_xpart]
      exact ho d hd
  refine ⟨fun e _ => ?_, fun d hd => ?_⟩
  · rw [profileCap_kfold D K hK]
    exact packK_lt (fun j _ => clamp_lt D n G _ _ _ _)
  · show xorUpTo K (fun j => (maskPosCode C P j).dec _ (fun e' => digit D n G j e'
      ((sumCode D n G P K C).inVals _ _ (D.outNode (blockSize G n) (tpos n (entryBits n) d)) e'))
      (D.visible n (entryBits n) (blockSize G n) (D.outNode (blockSize G n)
        (tpos n (entryBits n) d)) x)) = _
    have hsel : ∀ j < K, (maskPosCode C P j).dec (tpos n (entryBits n) d)
        (fun e' => digit D n G j e' ((sumCode D n G P K C).inVals (D.edges (blockSize G n))
          (fun y => D.visible n (entryBits n) (blockSize G n) y x)
          (D.outNode (blockSize G n) (tpos n (entryBits n) d)) e'))
        (D.visible n (entryBits n) (blockSize G n)
          (D.outNode (blockSize G n) (tpos n (entryBits n) d)) x) =
        xpart x P j ⟨d, hd⟩ := by
      intro j hj
      rw [sumCode_digits D n G P K C _ _ _ j hj]
      obtain ⟨hc, ho⟩ := hcopy j hj
      rw [clamp_inVals D n G _ _ _ hc]
      exact ho d hd
    -- only the copy of `d`'s part contributes
    have hPd := hP d hd
    rw [xorUpTo_single (j₀ := P d) K (fun j hjK hj' => ?_)]
    · rw [ite_eq_left hPd, hsel (P d) hPd]
      simp [xpart]
    · rw [hsel j hjK]
      simp only [xpart]
      rw [ite_eq_right (Ne.symm hj')]

/-- **Plain ⟹ no code on a set containing every input supported on a single part.** Under
`NoCode_TM`, for every constant `K` and all large `n`: if a colouring `P` of the input positions has
parts `< K` and `F` contains every input that vanishes outside one part, no code solves complete
exchange at the profile capacities on `F`. -/
theorem noCode_decomp_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (P : ℕ → ℕ), (∀ d < n * n * entryBits n, P d < K) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        (∀ j < K, ∀ x : Fin (n * n * entryBits n) → Bool,
          (∀ d : Fin (n * n * entryBits n), P d ≠ j → x d = false) → x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  obtain ⟨n₀, hn₀⟩ := h (K * k) G c hG
  refine ⟨n₀, fun n hn D hD hT P hP F hF code hsol => ?_⟩
  have hF' : ∀ j < K, ∀ x, xpart x P j ∈ F := fun j hj x =>
    hF j hj _ (fun d hd => by simp only [xpart]; rw [ite_eq_right hd])
  exact hn₀ n hn (kfoldTapes D K) (valid_kfold D K hD) hT _ (decomp_solves D hK P hsol hP hF')

/-- A fold of `false` terms is `false`. -/
theorem fold_xor_false {α : Type*} [DecidableEq α] (Q : Finset α) (g : α → Bool)
    (hg : ∀ a ∈ Q, g a = false) : Q.fold xor false g = false := by
  induction Q using Finset.induction_on with
  | empty => rfl
  | insert a Q ha ih =>
    rw [Finset.fold_insert ha, hg a (Finset.mem_insert_self a Q),
      ih (fun b hb => hg b (Finset.mem_insert_of_mem hb))]
    rfl

/-- **Plain ⟹ no code on the common zero set of quadratic forms whose monomials cross a fixed
partition.** Under `NoCode_TM`, for every constant `K` and all large `n`: let `P` colour the input
positions with `K` colours, and let every monomial `x_p x_q` of every form `⊕_{(p,q)∈Q} x_p x_q` of a
family join two different colours. Then no code solves complete exchange at the profile capacities
on a set containing the common zero set. Example (`K = 2`, colours "upper triangle with the
diagonal" and "strictly lower triangle"): any family of constraints `Σ_{i<j} ⟨A_{k,ij} x_ij, x_ji⟩ = 0`
with pair-dependent matrices, which couple `x` with `xᵀ`. -/
theorem noCode_crossQuad_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (P : ℕ → ℕ), (∀ d < n * n * entryBits n, P d < K) →
      ∀ (𝒬 : Finset (Finset (Fin (n * n * entryBits n) × Fin (n * n * entryBits n)))),
        (∀ Q ∈ 𝒬, ∀ pq ∈ Q, P pq.1 ≠ P pq.2) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        {x | ∀ Q ∈ 𝒬, Q.fold xor false (fun pq => x pq.1 && x pq.2) = false} ⊆ F →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_decomp_of_noCode h k G c K hG hK
  refine ⟨n₀, fun n hn D hD hT P hP 𝒬 hcross F hF code => ?_⟩
  refine hn₀ n hn D hD hT P hP F (fun j _ x hx => hF ?_) code
  intro Q hQ
  apply fold_xor_false
  intro pq hpq
  have hne := hcross Q hQ pq hpq
  by_cases h1 : P pq.1 = j
  · rw [hx pq.2 (fun h2 => hne (h1.trans h2.symm)), Bool.and_false]
  · rw [hx pq.1 h1, Bool.false_and]

end Transpose.Tape.Impl
