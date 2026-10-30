import MergeDepth.HopFields
import MergeDepth.FieldPruning
import MergeDepth.Formation

set_option autoImplicit false

/-!
# Corollary HC with its quantifiers: the linear crux excludes bounded merge depth

This file states and proves Corollary HC with its quantifiers over machines and sizes, in the frozen
machine model, with the linear crux as a statement about the class `S_ball_{k,C,β,r}` of the eighth
paper.

**Linear data paths** (Definition 7.1 of the eighth paper). `LinDataPath F M L τ₀ T m` is an
`F`-linear data path of width `m` of the machine `M` at length `L`, along a trace `τ₀` before a
horizon `T`, with a representation: encodings `enc t : Value M → F^m` of the step values, vectors
`c t` and `a t`, matrices `A t s`, and affine output functionals `φc ℓ + φ ℓ ⬝ᵥ ·`, none depending
on the input, such that on every binary input the encoded step values satisfy
`enc_t(v_t) = c_t + ∑_{s ∈ out(t)} A_{t,s} enc_s(v_s) + a_t w_{x₀(t)}` at every step `t < T`, where
`out(t)` is the set of dependency steps of `t` (`depOut`: the `s` with `DepStep τ₀.work T t s`, that
is `t - 1` and the last visits `prev_j(t)`) and the input term is present only if the input head
reads a position of `[0, L)` (`inTerm`, `readPos`); and output bit `ℓ`, appended at step
`appendTime τ₀ T ℓ`, is the output functional of the encoded value of that step.
* `LinDataPath.net`: its linear network (the eighth paper's `LinNet`). `val_eq_enc`: on binary
  inputs the network values are the encoded step values (strong induction on `t`).
  `net_depStep`, `val_card_le`, `trans_of_transposer`: the hypotheses `hout`, `hval` (for
  `β ≥ β(M)`) and `htrans` (for an oblivious transposer) of `hop_charging_machine`. `width_pos`: a
  transposer of a nonempty input has no data path of width `0`.
* `IsLineage`, `MergeDepthLE`, `FormationDepthLE`: a lineage assignment for a cold genie on the
  coordinate DAG (`coordNet`), merge depth and formation depth at most `s` at an output position.
  `copy_lineage` is Lemma 3.12 for the coordinate DAG (by `copyForest_lineage`).

**Ball systems and the linear crux** (Definition 7.4 of the eighth paper).
* `ballSystem τ₀ T r d b`: the balls `B^r(ℓ)`, the positions read at the steps reachable from the
  append step of `ℓ` by at most `r` dependency edges (`stepBall`). `reach_subset_stepBall`: the
  balls of the network of a data path lie in them; `minrank_mono`: minrank is antitone in the
  support pattern.
* `SBall k C β D d b`: the class `S_ball_{k,C,β,D}` at size `(d, b)`, `L = d² b`: the ball systems
  of the machines with `k` work tapes and value width at most `β` that are oblivious at length `L`
  (frozen `ObliviousOn`) with halting time `T ≤ C (L + 1)` and append exactly `L` bits.
* `LinCruxOn F B k C β D ρ`: `LinCrux_F(S_ball_{k,C,β,D}, ρ)` at the sizes `(d, b)` with `B d b`;
  `LinCrux`: at the paper's sizes `b = b(d)` (`entryBits`). `LinCruxOn.mono_radius`: the crux is
  antitone in the radius.

**Corollary HC.**
* `minrank_ballSystem_le`, `minrank_ballSystem_le_formation`: Theorems HC′(a) and HC for a data
  path of an oblivious transposer, in minrank form: the ball system of radius `(s + 1) τ D` of the
  machine has minrank at most `ε L + m k C (L + 1)/τ + |X|` over `F` (`hop_charging_machine_real`
  is `hop_charging_machine` for a real constant `C`).
* `not_mergeShallow`: Corollary HC at one size, for a machine.
* `cor_HC_gen`: Corollary HC for every `τ ≥ 1` and depth `D` with `ε + η + m k C/τ < ρ`, at every
  set of sizes `B` with `b ≥ 1`, with a threshold uniform over machines.
* `cor_HC`, `cor_HC_formation`: **Corollary HC as stated**, with `τ = ⌈8mkC/(ρ - ε)⌉` (`hcTau`),
  `D = DF(k, 2V - 1, ε/(4βC)) ⌈4βC/ε⌉` (`coldDepth`), `r = (s + 1) τ D` and `L = d² b(d)`.
  `cor_HC_uniform`, `cor_HC_formation_uniform`: with a threshold uniform over machines and
  `η < 7 (ρ - ε)/8` in place of `η < (ρ - ε)/8`.

`LinDataPath.rigidity_machine` is the eighth paper's Lemma 7.3 for machines, with the translation
from the machine to its network.
-/

namespace MergeDepth

open Finset Matrix Module Transpose Transpose.Tape BoundedNesting BoundedNesting.LinNet

/-! ### The dependency out-neighbours of a step -/

section DepOut

variable {k : ℕ}

open Classical in
/-- The out-neighbours `out(t)` of step `t` in the dependency DAG of the work walks `xs` before
`T`: the steps `s` with `DepStep xs T t s`, that is, `t - 1` (for `1 ≤ t < T`) and the last visits
`prev_j(t)` of the work heads to their cells at time `t`. -/
noncomputable def depOut (xs : Fin k → ℕ → ℤ) (T t : ℕ) : Finset ℕ :=
  (range t).filter fun s => DepStep xs T t s

theorem mem_depOut {xs : Fin k → ℕ → ℤ} {T t s : ℕ} : s ∈ depOut xs T t ↔ DepStep xs T t s := by
  classical
  unfold depOut
  rw [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨(depStep_lt h).1, h⟩⟩

theorem depOut_eq_empty {xs : Fin k → ℕ → ℤ} {T t : ℕ} (ht : T ≤ t) : depOut xs T t = ∅ := by
  ext s
  simp only [mem_depOut, Finset.notMem_empty, iff_false]
  intro h
  have := (depStep_lt h).2
  omega

end DepOut

/-! ### Linear data paths -/

section DataPath

variable {F : Type*} [Field F] {k : ℕ}

/-- A bit as an element of `F`. -/
def bitF (x : Bool) : F := if x then 1 else 0

/-- The bit of an output field as an element of `F`: `1` if a `1` is appended, and `0` otherwise. -/
def outF (o : Option Bool) : F := if o = some true then 1 else 0

/-- A binary input `w ∈ {0,1}^L` as a vector of `F^L`. -/
def binVec {L : ℕ} (w : Fin L → Bool) : Fin L → F := fun j => bitF (w j)

open Classical in
/-- The binary word of a vector of `F^L` (its entries equal to `1`). -/
noncomputable def toBool {L : ℕ} (x : Fin L → F) : Fin L → Bool := fun j => decide (x j = 1)

theorem binVec_toBool {L : ℕ} {x : Fin L → F} (hx : x ∈ binVecs L F) : binVec (toBool x) = x := by
  classical
  funext j
  have h := Fintype.mem_piFinset.mp hx j
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h <;> simp [binVec, bitF, toBool, h]

theorem zero_mem_binVecs (L : ℕ) : (0 : Fin L → F) ∈ binVecs L F := by
  classical
  exact Fintype.mem_piFinset.mpr fun _ => by simp

theorem one_mem_binVecs (L : ℕ) : (1 : Fin L → F) ∈ binVecs L F := by
  classical
  exact Fintype.mem_piFinset.mpr fun _ => by simp

/-- The input term `a_t w_{x₀(t)}` of step `t` of the trace `τ₀`: present only if the input head
reads a position `x₀(t) ∈ [0, L)` at step `t` (`readPos`). -/
def inTerm {m : ℕ} (τ₀ : Trace k) (L t : ℕ) (x : Fin L → F) (a : Fin m → F) : Fin m → F :=
  match readPos τ₀ L t with
  | some j => x j • a
  | none => 0

/-- **An `F`-linear data path of width `m`, with a representation** (Definition 7.1 of the eighth
paper), of the machine `M` at length `L`, along the trace `τ₀` before the horizon `T`. It consists
of maps `enc t` from the values of step `t` to `F^m`, vectors `c t, a t ∈ F^m` and matrices
`A t s ∈ F^{m × m}`, none depending on the input, such that for every binary input `w` and every
step `t < T`
`enc_t(v_t(w)) = c_t + ∑_{s ∈ out(t)} A_{t,s} enc_s(v_s(w)) + a_t w_{x₀(t)}`,
where `v_t(w)` is the value of step `t` (`stepValue`), `out(t)` is the set of dependency steps of
`t` (`depOut`: `t - 1` and the last visits `prev_j(t)`), and the last term is present only if the
input head reads a position of `[0, L)` at step `t` (`inTerm`); and of affine functionals
`φc ℓ + φ ℓ ⬝ᵥ ·` such that output bit `ℓ`, appended at step `t_ℓ = appendTime τ₀ T ℓ`, equals
`φ_ℓ(enc_{t_ℓ}(v_{t_ℓ}(w)))`. -/
structure LinDataPath (F : Type*) [Field F] (M : TM) (L : ℕ) (τ₀ : Trace M.k) (T m : ℕ) where
  /-- The encodings `enc_t` of the step values. -/
  enc : ℕ → Value M → Fin m → F
  /-- The constants `c_t`. -/
  c : ℕ → Fin m → F
  /-- The matrices `A_{t,s}`. -/
  A : ℕ → ℕ → Matrix (Fin m) (Fin m) F
  /-- The input vectors `a_t`. -/
  a : ℕ → Fin m → F
  /-- The linear parts of the output functionals. -/
  φ : Fin L → Fin m → F
  /-- The constants of the output functionals. -/
  φc : Fin L → F
  /-- The recursion of the data path. -/
  recursion : ∀ (w : Fin L → Bool) (t : ℕ), t < T →
    enc t (stepValue M (List.ofFn w) t) =
      c t + (∑ s ∈ depOut τ₀.work T t, A t s *ᵥ enc s (stepValue M (List.ofFn w) s)) +
        inTerm τ₀ L t (binVec w) (a t)
  /-- Output bit `ℓ` is the affine functional `φ_ℓ` of the encoded value of its step. -/
  output : ∀ (w : Fin L → Bool) (ℓ : Fin L),
    φc ℓ + φ ℓ ⬝ᵥ enc (appendTime τ₀ T ℓ) (stepValue M (List.ofFn w) (appendTime τ₀ T ℓ)) =
      outF (outBit M (List.ofFn w) (appendTime τ₀ T ℓ))

namespace LinDataPath

variable {M : TM} {L : ℕ} {τ₀ : Trace M.k} {T m : ℕ} (P : LinDataPath F M L τ₀ T m)

/-- **The linear network of a data path** (the eighth paper's `LinNet`): out-neighbours the
dependency steps of the work walks of `τ₀` before `T`, the data `c, A, a` of the representation,
and the position read by each step `t < T`. -/
noncomputable def net : LinNet F L m where
  out := depOut τ₀.work T
  out_lt _ _ hs := (depStep_lt (mem_depOut.mp hs)).1
  c := P.c
  A := P.A
  a := P.a
  rd t := if t < T then readPos τ₀ L t else none

theorem net_out (t : ℕ) : P.net.out t = depOut τ₀.work T t := rfl

theorem net_rd_of_lt {t : ℕ} (ht : t < T) : P.net.rd t = readPos τ₀ L t := ite_eq_left ht

theorem net_rd_of_le {t : ℕ} (ht : T ≤ t) : P.net.rd t = none := ite_eq_right (not_lt.mpr ht)

theorem net_inp_of_lt (x : Fin L → F) {t : ℕ} (ht : t < T) :
    P.net.inp x t = inTerm τ₀ L t x (P.a t) := by
  unfold LinNet.inp inTerm
  rw [P.net_rd_of_lt ht]
  rfl

/-- From the horizon on, the network values are the constants `c_t`. -/
theorem net_val_of_le (x : Fin L → F) {t : ℕ} (ht : T ≤ t) : P.net.val x t = P.c t := by
  rw [P.net.val_eq, P.net_out, depOut_eq_empty ht, sum_empty, add_zero]
  unfold LinNet.inp
  rw [P.net_rd_of_le ht, add_zero]
  rfl

/-- **On binary inputs the network values are the encoded step values**, at every step before
the horizon (strong induction on `t`). -/
theorem val_eq_enc (w : Fin L → Bool) :
    ∀ t, t < T → P.net.val (binVec w) t = P.enc t (stepValue M (List.ofFn w) t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rw [P.net.val_eq, P.recursion w t ht, P.net_inp_of_lt _ ht]
    congr 2
    refine Finset.sum_congr rfl fun s hs => ?_
    have hst := (depStep_lt (mem_depOut.mp hs)).1
    rw [ih s hst (hst.trans ht)]
    rfl

/-- The edges of the network are dependency steps (`hout` of `hop_charging_machine`). -/
theorem net_depStep : ∀ t, ∀ s ∈ P.net.out t, DepStep τ₀.work T t s :=
  fun _ _ hs => mem_depOut.mp hs

open Classical in
/-- **Steps take at most `2^β` values on binary inputs**, for `β ≥ β(M)` (`hval` of
`hop_charging_machine`): before the horizon the network value is the encoded step value, and from
the horizon on it is constant. -/
theorem val_card_le {β : ℕ} (hβ : valueWidth M ≤ β) (s : ℕ) :
    ((binVecs L F).image fun x => P.net.val x s).card ≤ 2 ^ β := by
  by_cases hs : s < T
  · calc ((binVecs L F).image fun x => P.net.val x s).card
        ≤ ((univ : Finset (Value M)).image (P.enc s)).card := by
          refine card_le_card fun y hy => ?_
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
          refine mem_image.mpr ⟨stepValue M (List.ofFn (toBool x)) s, mem_univ _, ?_⟩
          rw [← P.val_eq_enc _ s hs, binVec_toBool hx]
      _ ≤ Fintype.card (Value M) := card_image_le.trans (by rw [card_univ])
      _ ≤ 2 ^ valueWidth M := card_value_le M
      _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) hβ
  · have hc : ∀ x, P.net.val x s = P.c s := fun x => P.net_val_of_le x (not_lt.mp hs)
    calc ((binVecs L F).image fun x => P.net.val x s).card
        ≤ ({P.c s} : Finset (Fin m → F)).card := card_le_card fun y hy => by
          obtain ⟨x, -, rfl⟩ := mem_image.mp hy
          rw [hc]
          exact mem_singleton_self _
      _ = 1 := card_singleton _
      _ ≤ 2 ^ β := Nat.one_le_two_pow

end LinDataPath

end DataPath

/-! ### The output functionals of a transposer -/

section Transposer

variable {F : Type*} [Field F] {M : TM} {d b : ℕ} {τ₀ : Trace M.k} {T m : ℕ}

namespace LinDataPath

/-- **The output functionals decode the transpose** (`htrans` of `hop_charging_machine`): for an
oblivious transposer along `τ₀` before `T`, the affine functional `φ_ℓ` of the network value at the
append step of output `ℓ` is the input bit at `tpos ℓ`, on every binary input. -/
theorem trans_of_transposer (P : LinDataPath F M (d * d * b) τ₀ T m)
    (hM : ObliviousTransposer M d b τ₀ T) :
    ∀ x ∈ binVecs (d * d * b) F, ∀ ℓ : Fin (d * d * b),
      P.φc ℓ + P.φ ℓ ⬝ᵥ P.net.val x (appendTime τ₀ T ℓ) = x (tposOf d b ℓ) := by
  intro x hx ℓ
  have hlt := Pruning.appendTime_lt_of_transposer hM ℓ
  have hout := (prefix_output hM.appends (hM.follows (toBool x))
    (hM.transposes (toBool x))).2 (tposOf d b ℓ)
  have e : Transpose.Tape.tpos d b ((tposOf d b ℓ : Fin (d * d * b)) : ℕ) = ℓ :=
    Transpose.Tape.Impl.tpos_tpos ℓ.2
  rw [e] at hout
  rw [← binVec_toBool hx, P.val_eq_enc _ _ hlt, P.output, hout]
  simp [outF, binVec, bitF]

/-- **A transposer of a nonempty input has no data path of width `0`**: the outputs of such a
data path are constants. -/
theorem width_pos (P : LinDataPath F M (d * d * b) τ₀ T m) (hM : ObliviousTransposer M d b τ₀ T)
    (hL : 1 ≤ d * d * b) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · exfalso
    have h0 := P.trans_of_transposer hM 0 (zero_mem_binVecs _) ⟨0, hL⟩
    have h1 := P.trans_of_transposer hM 1 (one_mem_binVecs _) ⟨0, hL⟩
    simp only [dotProduct, univ_eq_empty, sum_empty, add_zero, Pi.zero_apply,
      Pi.one_apply] at h0 h1
    exact zero_ne_one (h0.symm.trans h1)
  · exact h

end LinDataPath

end Transposer

/-! ### Ball systems and minrank -/

section Balls

variable {F : Type*} [Field F]

/-- **The ball system of radius `r`** of a trace `τ₀` before `T`, at size `(d, b)`: the ball
`B^r(ℓ)` of output position `ℓ` is the set of input positions read at the steps reachable from its
append step `appendTime τ₀ T ℓ` by dependency paths with at most `r` edges (`stepBall`). -/
noncomputable def ballSystem {k : ℕ} (τ₀ : Trace k) (T r d b : ℕ) :
    Fin (d * d * b) → Finset (Fin (d * d * b)) :=
  fun ℓ => stepBall τ₀.work T (readPos τ₀ (d * d * b)) r (appendTime τ₀ T ℓ)

/-- **The balls of the network of a data path lie in the balls of the dependency DAG.** -/
theorem LinDataPath.reach_subset_stepBall {M : TM} {L : ℕ} {τ₀ : Trace M.k} {T m : ℕ}
    (P : LinDataPath F M L τ₀ T m) (r t : ℕ) :
    P.net.reach ∅ r t ⊆ stepBall τ₀.work T (readPos τ₀ L) r t := by
  intro j hj
  simp only [LinNet.reach, mem_filter, mem_univ, true_and] at hj
  obtain ⟨π, hπ, -, hlen, hrd⟩ := hj
  obtain ⟨π', rfl⟩ := P.net.mem_paths_head hπ
  simp only [stepBall, mem_filter, mem_univ, true_and]
  refine ⟨π', isDepPath_of_paths P.net_depStep _ t hπ, by simpa using hlen, ?_⟩
  by_cases hT : (t :: π').getLastD t < T
  · rwa [P.net_rd_of_lt hT] at hrd
  · rw [P.net_rd_of_le (not_lt.mp hT)] at hrd
    exact absurd hrd (by simp)

/-- The balls grow with the radius. -/
theorem ballSystem_mono {k : ℕ} (τ₀ : Trace k) (T : ℕ) {r r' : ℕ} (hr : r ≤ r') (d b : ℕ)
    (ℓ : Fin (d * d * b)) : ballSystem τ₀ T r d b ℓ ⊆ ballSystem τ₀ T r' d b ℓ := by
  intro j hj
  simp only [ballSystem, stepBall, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨π, hπ, hlen, hrd⟩ := hj
  exact ⟨π, hπ, hlen.trans hr, hrd⟩

/-- **Minrank is antitone in the support pattern**: enlarging the sets of a system can only lower
its minrank. -/
theorem minrank_mono {L : ℕ} (tpos : Fin L → Fin L) {I J : Fin L → Finset (Fin L)}
    (hIJ : ∀ ℓ, I ℓ ⊆ J ℓ) : minrank F tpos J ≤ minrank F tpos I := by
  have hne : {r | ∃ R : Matrix (Fin L) (Fin L) F, R.rank = r ∧
      ∀ ℓ j, (Pmat (F := F) tpos - R) ℓ j ≠ 0 → j ∈ I ℓ}.Nonempty :=
    ⟨_, Pmat tpos, rfl, fun ℓ j h => by simp at h⟩
  obtain ⟨R, hR, hsupp⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨R, hR, fun ℓ j h => hIJ ℓ (hsupp ℓ j h)⟩

end Balls

/-! ### The class `S_ball` and the linear crux -/

section Crux

/-- The trace of `M` at length `L`: the trace of the all-zero input. If `M` is oblivious at length
`L`, every input of length `L` has this trace before the halting time. -/
def traceAt (M : TM) (L : ℕ) : Trace M.k := trace M (List.ofFn fun _ : Fin L => false)

/-- **The class `S_ball_{k,C,β,D}`** of the eighth paper (Definition 7.4), at size `(d, b)` and
length `L = d² b`: the ball systems `(B^D(ℓ))_{ℓ < L}` (`ballSystem`) of the machines `M` with `k`
work tapes and value width at most `β` that are oblivious at length `L` (frozen `ObliviousOn`)
with halting time `T ≤ C (L + 1)` and append exactly `L` bits. The trace is that of any input of
length `L` (`traceAt`). No linear data path and no correctness are required. -/
def SBall (k : ℕ) (C : ℝ) (β D d b : ℕ) : Set (Fin (d * d * b) → Finset (Fin (d * d * b))) :=
  {I | ∃ (M : TM) (T : ℕ), M.k = k ∧ valueWidth M ≤ β ∧
    ObliviousOn M (inputsOfLength (d * d * b)) T ∧ (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) ∧
    (appendList (traceAt M (d * d * b)) T).length = d * d * b ∧
    I = ballSystem (traceAt M (d * d * b)) T D d b}

/-- **The linear crux `LinCrux_F(S_ball_{k,C,β,D}, ρ)`** (Definition 7.4 of the eighth paper), at
the sizes `(d, b)` with `B d b`: for every `η > 0` there is `d₀` such that every system of
`S_ball_{k,C,β,D}` at a size `d ≥ d₀` has minrank at least `(ρ - η) L` over `F`, for the demands
`tpos` of transposition. -/
def LinCruxOn (F : Type*) [Field F] (B : ℕ → ℕ → Prop) (k : ℕ) (C : ℝ) (β D : ℕ) (ρ : ℝ) :
    Prop :=
  ∀ η : ℝ, 0 < η → ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → ∀ I ∈ SBall k C β D d b,
    (ρ - η) * (d * d * b : ℕ) ≤ (minrank F (tposOf d b) I : ℝ)

/-- **The linear crux at the lengths of the paper**, `L = d² b(d)` with `b(d) = max(1, ⌈log₂ d⌉)`
(`entryBits`). -/
abbrev LinCrux (F : Type*) [Field F] (k : ℕ) (C : ℝ) (β D : ℕ) (ρ : ℝ) : Prop :=
  LinCruxOn F (fun d b => b = entryBits d) k C β D ρ

/-- **The linear crux is antitone in the radius**: the crux at radius `D'` implies it at every
radius `D ≤ D'`, since the balls grow with the radius. -/
theorem LinCruxOn.mono_radius {F : Type*} [Field F] {B : ℕ → ℕ → Prop} {k : ℕ} {C : ℝ}
    {β D D' : ℕ} {ρ : ℝ} (hD : D ≤ D') (h : LinCruxOn F B k C β D' ρ) :
    LinCruxOn F B k C β D ρ := by
  intro η hη
  obtain ⟨d₀, hd₀⟩ := h η hη
  refine ⟨d₀, fun d hd b hb I hI => ?_⟩
  obtain ⟨M, T, hk, hβ, hobl, hT, hlen, rfl⟩ := hI
  have h' := hd₀ d hd b hb _ ⟨M, T, hk, hβ, hobl, hT, hlen, rfl⟩
  have hmono :=
    minrank_mono (F := F) (tposOf d b) (ballSystem_mono (traceAt M (d * d * b)) T hD d b)
  exact h'.trans (by exact_mod_cast hmono)

end Crux

/-! ### Theorem HC′(a) with a real constant `C` -/

section RealC

variable {F : Type*} [Field F] {L m k : ℕ}

open Classical in
/-- **Theorem HC′(a)** (`hop_charging_machine`) for a real constant `C`: `T ≤ C (L + 1)` in `ℝ`. -/
theorem hop_charging_machine_real (net : LinNet F L m) (hm : 0 < m) (xs : Fin k → ℕ → ℤ)
    {T V β : ℕ} {C : ℝ} (hT : (T : ℝ) ≤ C * (L + 1)) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := L) xs T V β ε D ΓF)
    (hout : ∀ t, ∀ s ∈ net.out t, DepStep xs T t s)
    (hval : ∀ s ∈ ΓF, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ (coordNet net hm).paths u →
      LinNet.GFree (coordGenie m ΓF) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (u / m) (v / m)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L) (X : Finset (Fin L))
    (hround : ∀ ℓ ∉ X, ∀ i : Fin m, φ ℓ i ≠ 0 → ∀ π, π ∈ (coordNet net hm).paths (tout ℓ * m + i) →
      LinNet.GFree (coordGenie m ΓF) π →
      dm lin (fun u v => DeepStep xs T V (u / m) (v / m)) false π ≤ s)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ)) :
    ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧
      (R.rank : ℝ) ≤ ε * L + m * k * C * (L + 1) / τ + X.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → ℓ ∉ X ∧ j ∈ net.reach ∅ ((s + 1) * τ * D) (tout ℓ) := by
  let Rset : Finset (ℕ × ℕ) := (allHops xs T \ lightHops xs T V).image fun η => (η.2.2, η.2.1)
  have hRset : ∀ a b, DeepStep xs T V a b → (a, b) ∈ Rset := by
    rintro a b ⟨η, hη, he, hl⟩
    refine mem_image.mpr ⟨η, mem_sdiff.mpr ⟨hη, hl⟩, ?_⟩
    rw [he]
  have hRcard : Rset.card ≤ k * T :=
    card_image_le.trans ((card_le_card sdiff_subset).trans (card_allHops_le xs T))
  have hcold' : ∀ t π, π ∈ net.paths t → LinNet.GFree ΓF π → rCount (DeepStep xs T V) π = 0 →
      π.length ≤ D := fun t π hπ hfree hR =>
    hcold.2 π (isDepPath_of_paths hout π t hπ) hfree hR
  obtain ⟨q, R, S, hq, hPRS, hrank, hsupp⟩ := hop_charging_steps net hm (DeepStep xs T V) Rset
    hRset ΓF D β hcold' hval lin hside hτ s tout φ φc tpos X hround htrans
  refine ⟨R, S, hPRS, ?_, hsupp⟩
  have h1 : τ * q ≤ m * (k * T) := hq.trans (Nat.mul_le_mul_left _ hRcard)
  have h1' : (τ * q : ℝ) ≤ m * (k * T) := by exact_mod_cast h1
  have h2 : (m * (k * T) : ℝ) ≤ m * k * C * (L + 1) := by
    calc (m * (k * T) : ℝ) = (m * k) * T := by ring
      _ ≤ (m * k) * (C * (L + 1)) := mul_le_mul_of_nonneg_left hT (by positivity)
      _ = m * k * C * (L + 1) := by ring
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hqr : (q : ℝ) ≤ m * k * C * (L + 1) / τ := by
    rw [le_div_iff₀ hτ']
    linarith
  have hr : (R.rank : ℝ) ≤ β * ΓF.card + q + X.card := by exact_mod_cast hrank
  linarith [hcold.1]

end RealC

/-! ### Merge depth and formation depth of the coordinate DAG -/

section Depths

variable {F : Type*} [Field F] {M : TM} {L : ℕ} {τ₀ : Trace M.k} {T m : ℕ}

namespace LinDataPath

open Classical in
/-- **A lineage assignment for the cold genie `ΓF`** on the coordinate DAG of a data path (the
hypothesis `hside` of `hop_charging_machine`): `lin` chooses lineage edges, and every `ΓF`-free path
whose first edge leaves a continuation `u` by another edge contains no deep edge. Deep edges are the
coordinate edges whose projection is a deep step (`DeepStep`) of the work walks of `τ₀`. -/
def IsLineage (P : LinDataPath F M L τ₀ T m) (hm : 0 < m) (V : ℕ) (ΓF : Finset ℕ)
    (lin : Forest) : Prop :=
  ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ (coordNet P.net hm).paths u →
    LinNet.GFree (coordGenie m ΓF) (u :: v' :: π) →
    rCount (fun u v => DeepStep τ₀.work T V (u / m) (v / m)) (u :: v' :: π) = 0

open Classical in
/-- **Merge depth at most `s` at output position `ℓ`**: every `ΓF`-free path of the coordinate DAG
from an output node `(t_ℓ, i)` of `ℓ` (a coordinate with `(φ_ℓ^lin)_i ≠ 0`) has at most `s` deep
merges for the lineage assignment `lin`. -/
def MergeDepthLE (P : LinDataPath F M L τ₀ T m) (hm : 0 < m) (V : ℕ) (ΓF : Finset ℕ)
    (lin : Forest) (s : ℕ) (ℓ : Fin L) : Prop :=
  ∀ i : Fin m, P.φ ℓ i ≠ 0 → ∀ π, π ∈ (coordNet P.net hm).paths (appendTime τ₀ T ℓ * m + i) →
    LinNet.GFree (coordGenie m ΓF) π →
    dm lin (fun u v => DeepStep τ₀.work T V (u / m) (v / m)) false π ≤ s

open Classical in
/-- **Formation depth at most `s` at output position `ℓ`**: every `ΓF`-free path of the coordinate
DAG from an output node of `ℓ` contains at most `s` deep formations. -/
def FormationDepthLE (P : LinDataPath F M L τ₀ T m) (hm : 0 < m) (V : ℕ) (ΓF : Finset ℕ)
    (s : ℕ) (ℓ : Fin L) : Prop :=
  ∀ i : Fin m, P.φ ℓ i ≠ 0 → ∀ π, π ∈ (coordNet P.net hm).paths (appendTime τ₀ T ℓ * m + i) →
    LinNet.GFree (coordGenie m ΓF) π →
    π.countP (DeepFormation (coordNet P.net hm)
      fun u v => DeepStep τ₀.work T V (u / m) (v / m)) ≤ s

/-- **Lemma 3.12 for the coordinate DAG**: the lineage assignment of the copies is a lineage
assignment for every genie, and its merge depth is at most the formation depth. -/
theorem copy_lineage (P : LinDataPath F M L τ₀ T m) (hm : 0 < m) (V : ℕ) (ΓF : Finset ℕ) :
    P.IsLineage hm V ΓF (copyForest (coordNet P.net hm)) ∧
      ∀ s ℓ, P.FormationDepthLE hm V ΓF s ℓ →
        P.MergeDepthLE hm V ΓF (copyForest (coordNet P.net hm)) s ℓ := by
  classical
  have hcf := copyForest_lineage (coordNet P.net hm) fun u v => DeepStep τ₀.work T V (u / m) (v / m)
  exact ⟨fun u v v' π hn hne hπ _ => absurd hπ (hcf.1 u v v' π hn hne),
    fun s ℓ hF i hi π hπ hfree => (hcf.2 hπ).trans (hF i hi π hπ hfree)⟩

end LinDataPath

end Depths

/-! ### Theorem HC′(a) and Corollary HC at one size, for a machine -/

section OneSize

variable {F : Type*} [Field F] {M : TM} {d b : ℕ} {τ₀ : Trace M.k} {T m : ℕ}

namespace LinDataPath

/-- **Theorem HC′(a) for an `F`-linear data path of an oblivious transposer, minrank form.** Let `M`
be an oblivious transposer along `τ₀` before `T ≤ C (L + 1)`, `β ≥ β(M)`, `P` a data path of width
`m ≥ 1`, `ΓF` a cold genie at `(V, ε)` with depth `D`, `lin` a lineage assignment for it, and `X` a
set of output positions outside which the coordinate DAG has merge depth at most `s`. Then the ball
system of radius `(s + 1) τ D` of the machine has minrank at most
`ε L + m k C (L + 1) / τ + |X|` over `F`. -/
theorem minrank_ballSystem_le (P : LinDataPath F M (d * d * b) τ₀ T m)
    (hM : ObliviousTransposer M d b τ₀ T) {C : ℝ} (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (hm : 0 < m) {V β : ℕ} (hβ : valueWidth M ≤ β) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) {lin : Forest}
    (hlin : P.IsLineage hm V ΓF lin) {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ)
    (X : Finset (Fin (d * d * b))) (hround : ∀ ℓ ∉ X, P.MergeDepthLE hm V ΓF lin s ℓ) :
    (minrank F (tposOf d b) (ballSystem τ₀ T ((s + 1) * τ * D) d b) : ℝ) ≤
      ε * (d * d * b : ℕ) + m * M.k * C * ((d * d * b : ℕ) + 1) / τ + X.card := by
  obtain ⟨R, S, hPRS, hrank, hsupp⟩ := hop_charging_machine_real P.net hm τ₀.work hT hcold
    P.net_depStep (fun s _ => P.val_card_le hβ s) lin hlin hτ s (fun ℓ => appendTime τ₀ T ℓ)
    P.φ P.φc (tposOf d b) X hround (P.trans_of_transposer hM)
  have hmin : minrank F (tposOf d b) (ballSystem τ₀ T ((s + 1) * τ * D) d b) ≤ R.rank := by
    have hsub : Pmat (tposOf d b) - R = S := by rw [hPRS]; abel
    refine Nat.sInf_le ⟨R, rfl, fun ℓ j h => ?_⟩
    rw [hsub] at h
    exact P.reach_subset_stepBall _ _ (hsupp ℓ j h).2
  calc (minrank F (tposOf d b) (ballSystem τ₀ T ((s + 1) * τ * D) d b) : ℝ) ≤ R.rank := by
        exact_mod_cast hmin
    _ ≤ _ := hrank

/-- **Theorem HC(a) for an `F`-linear data path of an oblivious transposer, minrank form**: the
bound of `minrank_ballSystem_le` when the coordinate DAG has formation depth at most `s` outside
`X`. -/
theorem minrank_ballSystem_le_formation (P : LinDataPath F M (d * d * b) τ₀ T m)
    (hM : ObliviousTransposer M d b τ₀ T) {C : ℝ} (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1))
    (hm : 0 < m) {V β : ℕ} (hβ : valueWidth M ≤ β) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := d * d * b) τ₀.work T V β ε D ΓF) {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ)
    (X : Finset (Fin (d * d * b))) (hround : ∀ ℓ ∉ X, P.FormationDepthLE hm V ΓF s ℓ) :
    (minrank F (tposOf d b) (ballSystem τ₀ T ((s + 1) * τ * D) d b) : ℝ) ≤
      ε * (d * d * b : ℕ) + m * M.k * C * ((d * d * b : ℕ) + 1) / τ + X.card :=
  P.minrank_ballSystem_le hM hT hm hβ hcold (P.copy_lineage hm V ΓF).1 hτ s X
    fun ℓ hℓ => (P.copy_lineage hm V ΓF).2 s ℓ (hround ℓ hℓ)

end LinDataPath

/-- **Condition (ii) of Corollary HC**, along the trace `τ₀` before `T`: `M` has an `F`-linear
data path at length `L` with a representation of width at most `m` whose coordinate DAG, for some
cold genie at `(V, ε)` with depth `D` and some lineage assignment for it, has merge depth at most
`s` at all but at most `η L` output positions. (For width `0` the coordinate DAG is empty and only
the representation and the genie are required.) -/
def MergeShallow (F : Type*) [Field F] (M : TM) (L : ℕ) (τ₀ : Trace M.k) (T m V β : ℕ) (ε : ℝ)
    (D s : ℕ) (η : ℝ) : Prop :=
  ∃ m' ≤ m, ∃ P : LinDataPath F M L τ₀ T m', ∃ ΓF : Finset ℕ,
    IsColdGenie (L := L) τ₀.work T V β ε D ΓF ∧
    ∀ hm : 0 < m', ∃ lin : Forest, P.IsLineage hm V ΓF lin ∧
      ∃ X : Finset (Fin L), (X.card : ℝ) ≤ η * L ∧ ∀ ℓ ∉ X, P.MergeDepthLE hm V ΓF lin s ℓ

/-- **Condition (ii) of Corollary HC with formation depth**: as `MergeShallow`, with formation
depth at most `s` (no lineage assignment). -/
def FormationShallow (F : Type*) [Field F] (M : TM) (L : ℕ) (τ₀ : Trace M.k) (T m V β : ℕ)
    (ε : ℝ) (D s : ℕ) (η : ℝ) : Prop :=
  ∃ m' ≤ m, ∃ P : LinDataPath F M L τ₀ T m', ∃ ΓF : Finset ℕ,
    IsColdGenie (L := L) τ₀.work T V β ε D ΓF ∧
    ∀ hm : 0 < m', ∃ X : Finset (Fin L), (X.card : ℝ) ≤ η * L ∧
      ∀ ℓ ∉ X, P.FormationDepthLE hm V ΓF s ℓ

/-- Bounded formation depth implies bounded merge depth (Lemma 3.12, with the lineage assignment
of the copies). -/
theorem FormationShallow.mergeShallow {L : ℕ} {τ₀ : Trace M.k} {T m V β : ℕ} {ε : ℝ} {D s : ℕ}
    {η : ℝ} (h : FormationShallow F M L τ₀ T m V β ε D s η) :
    MergeShallow F M L τ₀ T m V β ε D s η := by
  obtain ⟨m', hm', P, ΓF, hcold, hrest⟩ := h
  refine ⟨m', hm', P, ΓF, hcold, fun hm => ?_⟩
  obtain ⟨X, hX, hround⟩ := hrest hm
  exact ⟨_, (P.copy_lineage hm V ΓF).1, X, hX,
    fun ℓ hℓ => (P.copy_lineage hm V ΓF).2 s ℓ (hround ℓ hℓ)⟩

/-- **Corollary HC at one size.** Let `M` be an oblivious transposer along `τ₀` before
`T ≤ C (L + 1)`, `L = d² b ≥ 1`, with `β ≥ β(M)` and `τ ≥ 1`. If its ball system of radius
`(s + 1) τ D` has minrank at least `ρ' L` and `ε L + m k C (L + 1)/τ + η L < ρ' L`, then condition
(ii) fails: no data path of width at most `m` has, for a cold genie at `(V, ε)` with depth `D` and a
lineage assignment, merge depth at most `s` at all but `η L` output positions. -/
theorem not_mergeShallow (hM : ObliviousTransposer M d b τ₀ T) {C : ℝ}
    (hT : (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1)) (hL : 1 ≤ d * d * b) {V β s τ D : ℕ}
    (hβ : valueWidth M ≤ β) (hτ : 1 ≤ τ) {ε η ρ' : ℝ}
    (hcrux : ρ' * (d * d * b : ℕ) ≤
      (minrank F (tposOf d b) (ballSystem τ₀ T ((s + 1) * τ * D) d b) : ℝ))
    (hgap : ε * (d * d * b : ℕ) + m * M.k * C * ((d * d * b : ℕ) + 1) / τ + η * (d * d * b : ℕ) <
      ρ' * (d * d * b : ℕ)) :
    ¬ MergeShallow F M (d * d * b) τ₀ T m V β ε D s η := by
  rintro ⟨m', hm', P, ΓF, hcold, hrest⟩
  have hm'pos := P.width_pos hM hL
  obtain ⟨lin, hlin, X, hX, hround⟩ := hrest hm'pos
  have h1 := P.minrank_ballSystem_le hM hT hm'pos hβ hcold hlin hτ s X hround
  have hC : 0 ≤ C := by
    by_contra hC
    push Not at hC
    have h0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have : C * (((d * d * b : ℕ) : ℝ) + 1) < 0 := mul_neg_of_neg_of_pos hC (by positivity)
    linarith
  have hkC : (0 : ℝ) ≤ M.k * C * ((d * d * b : ℕ) + 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (by positivity)
  have h2 : (m' : ℝ) * M.k * C * ((d * d * b : ℕ) + 1) / τ ≤
      m * M.k * C * ((d * d * b : ℕ) + 1) / τ := by
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg τ)
    have hm'' : (m' : ℝ) ≤ m := by exact_mod_cast hm'
    calc (m' : ℝ) * M.k * C * ((d * d * b : ℕ) + 1) = m' * (M.k * C * ((d * d * b : ℕ) + 1)) := by
          ring
      _ ≤ m * (M.k * C * ((d * d * b : ℕ) + 1)) := mul_le_mul_of_nonneg_right hm'' hkC
      _ = m * M.k * C * ((d * d * b : ℕ) + 1) := by ring
  linarith

end OneSize

/-! ### Corollary HC -/

section Corollary

/-- **Condition (i) of Corollary HC**, in the frozen model: `M` is oblivious at length `L = d² b`
(`ObliviousOn`) with halting time `T ≤ C (L + 1)` and transposes all `d × d` matrices with `b`-bit
entries (`Transposes`). -/
def ObliviousLinTime (M : TM) (d b : ℕ) (C : ℝ) (T : ℕ) : Prop :=
  ObliviousOn M (inputsOfLength (d * d * b)) T ∧ (T : ℝ) ≤ C * ((d * d * b : ℕ) + 1) ∧
    Transposes M d b

/-- A machine that is oblivious at length `L = d² b` and transposes is an oblivious transposer
along the trace of any input of length `L`, before its halting time, and that trace appends exactly
`L` bits. -/
theorem obliviousTransposer_of_transposes {M : TM} {d b T : ℕ}
    (hobl : ObliviousOn M (inputsOfLength (d * d * b)) T) (htr : Transposes M d b)
    (w₀ : Fin (d * d * b) → Bool) :
    ObliviousTransposer M d b (trace M (List.ofFn w₀)) T ∧
      (appendList (trace M (List.ofFn w₀)) T).length = d * d * b := by
  have hf := followsTrace_of_obliviousOn hobl w₀
  have hout : ∀ X : Fin (d * d * b) → Bool, OutputsTranspose M d b X := by
    intro X
    have hX : List.ofFn X ∈ matrixInputs d b := by
      rw [Transpose.Tape.Impl.matrixInputs_eq]
      exact List.length_ofFn
    obtain ⟨A, hA⟩ := hX
    obtain ⟨t, ht⟩ := htr A
    exact ⟨A, hA, t, hA ▸ ht⟩
  have hlen := appendList_length_of_haltsAt (hf w₀) (hobl.1 _ List.length_ofFn) (hout w₀)
  exact ⟨⟨hf, hlen.ge, hout⟩, hlen⟩

/-- **The size threshold of Corollary HC.** Let `δ = ρ - (ε + η + m k C/τ) > 0`. For every `d₁`
there is `d₀ ≥ d₁` such that at every size `d ≥ d₀` and width `b ≥ 1` (`B d b`), `L = d² b ≥ 1`
and `ε L + m k C (L + 1)/τ + η L < (ρ - δ/2) L`. -/
theorem hc_threshold {B : ℕ → ℕ → Prop} (hB : ∀ d b, B d b → 1 ≤ b) {k m τ : ℕ}
    {C ε ρ η : ℝ} (hgap : ε + η + m * k * C / τ < ρ) (d₁ : ℕ) :
    ∃ d₀ : ℕ, d₁ ≤ d₀ ∧ ∀ d ≥ d₀, ∀ b, B d b → 1 ≤ d * d * b ∧
      ε * (d * d * b : ℕ) + m * k * C * ((d * d * b : ℕ) + 1) / τ + η * (d * d * b : ℕ) <
        (ρ - (ρ - (ε + η + m * k * C / τ)) / 2) * (d * d * b : ℕ) := by
  set a : ℝ := m * k * C / τ with ha
  set δ : ℝ := ρ - (ε + η + a) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine ⟨max (max d₁ 1) (⌈2 * a / δ⌉₊ + 1), (le_max_left _ _).trans (le_max_left _ _),
    fun d hd b hb => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right _ _).trans ((le_max_left _ _).trans hd)
  have hd2 : ⌈2 * a / δ⌉₊ + 1 ≤ d := (le_max_right _ _).trans hd
  have hLd : d ≤ d * d * b := by
    calc d = d * 1 * 1 := by ring
      _ ≤ d * d * b := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd1) (hB d b hb)
  refine ⟨hd1.trans hLd, ?_⟩
  set Lr : ℝ := ((d * d * b : ℕ) : ℝ) with hLr
  have hLa : 2 * a / δ < Lr := by
    have h1 : 2 * a / δ ≤ ⌈2 * a / δ⌉₊ := Nat.le_ceil _
    have h2 : ((⌈2 * a / δ⌉₊ + 1 : ℕ) : ℝ) ≤ Lr := by
      rw [hLr]
      exact_mod_cast hd2.trans hLd
    push_cast at h2
    linarith
  have h2a : 2 * a < Lr * δ := (div_lt_iff₀ hδpos).mp hLa
  have hmk : (m : ℝ) * k * C * (Lr + 1) / τ = a * Lr + a := by
    rw [ha]
    ring
  rw [hmk]
  nlinarith

/-- **Corollary HC, general form, frozen model.** Let `B` be a set of sizes `(d, b)` with `b ≥ 1`
(Corollary HC: `b = b(d)`), `τ ≥ 1` and `D` integers, and `ε + η + m k C/τ < ρ`. If
`LinCrux_F(S_ball_{k,C,β,(s+1)τD}, ρ)` holds at the sizes `B`, there is `d₀` such that at no size
`(d, b) ∈ B` with `d ≥ d₀` does a machine `M` with `k` work tapes and value width at most `β`
satisfy both (i) (oblivious at length `L = d² b` with halting time `T ≤ C (L + 1)`, transposing all
`d × d` matrices) and (ii) (an `F`-linear data path of width at most `m` whose coordinate DAG, for
some cold genie at `(V, ε)` with depth `D` and some lineage assignment, has merge depth at most `s`
at all but at most `η L` output positions). The threshold does not depend on the machine. -/
theorem cor_HC_gen (F : Type*) [Field F] {B : ℕ → ℕ → Prop} (hB : ∀ d b, B d b → 1 ≤ b)
    {k m V β s τ D : ℕ} {C ε ρ η : ℝ} (hτ : 1 ≤ τ) (hgap : ε + η + m * k * C / τ < ρ)
    (hcrux : LinCruxOn F B k C β ((s + 1) * τ * D) ρ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b, B d b → ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ (ObliviousLinTime M d b C T ∧
        MergeShallow F M (d * d * b) (traceAt M (d * d * b)) T m V β ε D s η) := by
  obtain ⟨d₁, hd₁⟩ := hcrux ((ρ - (ε + η + m * k * C / τ)) / 2) (by linarith)
  obtain ⟨d₀, hd₀₁, hd₀⟩ := hc_threshold hB hgap d₁
  refine ⟨d₀, fun d hd b hb M hk hβ T ⟨⟨hobl, hT, htr⟩, hII⟩ => ?_⟩
  obtain ⟨hL, hgap'⟩ := hd₀ d hd b hb
  obtain ⟨hM, hlen⟩ := obliviousTransposer_of_transposes hobl htr (fun _ => false)
  have hcr := hd₁ d (hd₀₁.trans hd) b hb _ (show ballSystem (traceAt M (d * d * b)) T
    ((s + 1) * τ * D) d b ∈ SBall k C β ((s + 1) * τ * D) d b from
      ⟨M, T, hk, hβ, hobl, hT, hlen, rfl⟩)
  subst hk
  exact not_mergeShallow hM hT hL hβ hτ hcr hgap' hII

/-! ### The parameters of the paper -/

/-- `τ = ⌈8 m k C / (ρ - ε)⌉`, the checkpoint spacing of Corollary HC. -/
noncomputable def hcTau (m k : ℕ) (C ε ρ : ℝ) : ℕ := ⌈8 * m * k * C / (ρ - ε)⌉₊

/-- `D = DF(k, 2V - 1, ε/(4βC)) ⌈4βC/ε⌉`, the depth of a cold genie at `(V, ε)` (Lemma 3.1). -/
noncomputable def coldDepth (k V β : ℕ) (C ε : ℝ) : ℕ :=
  DF k (2 * V - 1) (ε / (4 * β * C)) * ⌈4 * β * C / ε⌉₊

theorem one_le_hcTau {m k : ℕ} {C ε ρ : ℝ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hC : 0 < C)
    (hερ : ε < ρ) : 1 ≤ hcTau m k C ε ρ := by
  unfold hcTau
  rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  have : (0 : ℝ) < k := by exact_mod_cast hk
  have : 0 < ρ - ε := by linarith
  positivity

/-- With the paper's `τ = ⌈8mkC/(ρ - ε)⌉`, the gap condition `ε + η + m k C/τ < ρ` holds for every
`η < 7 (ρ - ε)/8` (Corollary HC assumes `η < (ρ - ε)/8`). -/
theorem hcTau_gap {m k : ℕ} {C ε ρ η : ℝ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hC : 0 < C) (hερ : ε < ρ)
    (hη : η < 7 * (ρ - ε) / 8) : ε + η + m * k * C / hcTau m k C ε ρ < ρ := by
  have hτ' : (0 : ℝ) < hcTau m k C ε ρ := by exact_mod_cast one_le_hcTau hk hm hC hερ
  have hρε : 0 < ρ - ε := by linarith
  have hle : 8 * m * k * C / (ρ - ε) ≤ hcTau m k C ε ρ := Nat.le_ceil _
  rw [div_le_iff₀ hρε] at hle
  have h : (m : ℝ) * k * C / hcTau m k C ε ρ ≤ (ρ - ε) / 8 := by
    rw [div_le_iff₀ hτ']
    linarith
  linarith

/-- **Corollary HC, uniformly over machines, with the paper's parameters**: `k, m ≥ 1`, `C > 0`,
`ε < ρ`, `τ = ⌈8mkC/(ρ - ε)⌉`, `D = DF(k, 2V - 1, ε/(4βC)) ⌈4βC/ε⌉` and `r = (s + 1) τ D`. If
`LinCrux_F(S_ball_{k,C,β,r}, ρ)` holds, there is `d₀` such that for every `d ≥ d₀` and every machine
`M` with `k` work tapes and value width at most `β`, conditions (i) and (ii) do not hold together at
`L = d² b(d)`. This needs only `η < 7 (ρ - ε)/8` (Corollary HC: `0 ≤ η < (ρ - ε)/8`). -/
theorem cor_HC_uniform (F : Type*) [Field F] {k m V β s : ℕ} {C ε ρ η : ℝ} (hk : 1 ≤ k)
    (hm : 1 ≤ m) (hC : 0 < C) (hερ : ε < ρ) (hη : η < 7 * (ρ - ε) / 8)
    (hcrux : LinCrux F k C β ((s + 1) * hcTau m k C ε ρ * coldDepth k V β C ε) ρ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ (ObliviousLinTime M d (entryBits d) C T ∧
        MergeShallow F M (d * d * entryBits d) (traceAt M (d * d * entryBits d)) T m V β ε
          (coldDepth k V β C ε) s η) := by
  obtain ⟨d₀, hd₀⟩ := cor_HC_gen F (B := fun d b => b = entryBits d)
    (fun d b h => h ▸ Nat.le_add_left 1 _) (one_le_hcTau hk hm hC hερ) (hcTau_gap hk hm hC hερ hη)
    hcrux
  exact ⟨d₀, fun d hd M hk' hβ T => hd₀ d hd _ rfl M hk' hβ T⟩

/-- **Corollary HC** (the linear crux excludes bounded merge depth), **as stated.** Let
`k, m ≥ 1`, `C > 0`, `ε < ρ`, `η < (ρ - ε)/8`, `τ = ⌈8mkC/(ρ - ε)⌉`,
`D = DF(k, 2V - 1, ε/(4βC)) ⌈4βC/ε⌉` and `r = (s + 1) τ D`, and suppose
`LinCrux_F(S_ball_{k,C,β,r}, ρ)`. Then for every machine `M` with `k` work tapes and value width at
most `β` there is `d₀` such that for no `d ≥ d₀` do the following hold together at `L = d² b(d)`:
(i) `M` is oblivious at length `L` with halting time at most `C (L + 1)` and transposes all `d × d`
matrices; (ii) `M` has an `F`-linear data path at length `L` with a representation of width at most
`m` whose coordinate DAG, for some cold genie at `(V, ε)` and some lineage assignment for it, has
merge depth at most `s` at all but at most `η L` output positions. -/
theorem cor_HC (F : Type*) [Field F] {k m V β s : ℕ} {C ε ρ η : ℝ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hC : 0 < C) (hερ : ε < ρ) (hη : η < (ρ - ε) / 8)
    (hcrux : LinCrux F k C β ((s + 1) * hcTau m k C ε ρ * coldDepth k V β C ε) ρ)
    (M : TM) (hMk : M.k = k) (hβ : valueWidth M ≤ β) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ,
      ¬ (ObliviousLinTime M d (entryBits d) C T ∧
        MergeShallow F M (d * d * entryBits d) (traceAt M (d * d * entryBits d)) T m V β ε
          (coldDepth k V β C ε) s η) := by
  obtain ⟨d₀, hd₀⟩ := cor_HC_uniform F (V := V) (η := η) hk hm hC hερ (by linarith) hcrux
  exact ⟨d₀, fun d hd T => hd₀ d hd M hMk hβ T⟩

/-- **Corollary HC with formation depth, uniformly over machines**, with the paper's parameters and
`η < 7 (ρ - ε)/8`. -/
theorem cor_HC_formation_uniform (F : Type*) [Field F] {k m V β s : ℕ} {C ε ρ η : ℝ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hC : 0 < C) (hερ : ε < ρ) (hη : η < 7 * (ρ - ε) / 8)
    (hcrux : LinCrux F k C β ((s + 1) * hcTau m k C ε ρ * coldDepth k V β C ε) ρ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : TM, M.k = k → valueWidth M ≤ β → ∀ T : ℕ,
      ¬ (ObliviousLinTime M d (entryBits d) C T ∧
        FormationShallow F M (d * d * entryBits d) (traceAt M (d * d * entryBits d)) T m V β ε
          (coldDepth k V β C ε) s η) := by
  obtain ⟨d₀, hd₀⟩ := cor_HC_uniform F (V := V) hk hm hC hερ hη hcrux
  exact ⟨d₀, fun d hd M hk' hβ T h => hd₀ d hd M hk' hβ T ⟨h.1, h.2.mergeShallow⟩⟩

/-- **Corollary HC with formation depth, as stated** ("the same holds with merge depth replaced by
formation depth"). -/
theorem cor_HC_formation (F : Type*) [Field F] {k m V β s : ℕ} {C ε ρ η : ℝ} (hk : 1 ≤ k)
    (hm : 1 ≤ m) (hC : 0 < C) (hερ : ε < ρ) (hη : η < (ρ - ε) / 8)
    (hcrux : LinCrux F k C β ((s + 1) * hcTau m k C ε ρ * coldDepth k V β C ε) ρ)
    (M : TM) (hMk : M.k = k) (hβ : valueWidth M ≤ β) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ T : ℕ,
      ¬ (ObliviousLinTime M d (entryBits d) C T ∧
        FormationShallow F M (d * d * entryBits d) (traceAt M (d * d * entryBits d)) T m V β ε
          (coldDepth k V β C ε) s η) := by
  obtain ⟨d₀, hd₀⟩ := cor_HC_formation_uniform F (V := V) (η := η) hk hm hC hερ (by linarith) hcrux
  exact ⟨d₀, fun d hd T => hd₀ d hd M hMk hβ T⟩

end Corollary

/-! ### The eighth paper's Lemma 7.3 for machines -/

section Rigidity

variable {F : Type*} [Field F] {M : TM} {d b : ℕ} {τ₀ : Trace M.k} {T m : ℕ}

open Classical in
/-- **Per-machine rigidity for machines** (Lemma 7.3 of the eighth paper, with the translation from
the machine to its network). Let `M` be an oblivious transposer along `τ₀` before `T` with an
`F`-linear data path `P`, `β ≥ β(M)`, and `Γ` a genie under which every output has linear depth at
most `D` (the path sums of the representation from the append step of `ℓ` vanish under `φ_ℓ`
outside `I^D_Γ(ℓ)`). Then the system `I^D_Γ` and the ball system `B^D` of the machine have minrank
at most `β |Γ|` over `F`. -/
theorem LinDataPath.rigidity_machine (P : LinDataPath F M (d * d * b) τ₀ T m)
    (hM : ObliviousTransposer M d b τ₀ T) {β : ℕ} (hβ : valueWidth M ≤ β) (Γ : Finset ℕ) (D : ℕ)
    (hdepth : ∀ ℓ : Fin (d * d * b), ∀ j ∉ P.net.reach Γ D (appendTime τ₀ T ℓ),
      P.φ ℓ ⬝ᵥ P.net.C Γ (appendTime τ₀ T ℓ) j = 0) :
    minrank F (tposOf d b) (fun ℓ => P.net.reach Γ D (appendTime τ₀ T ℓ)) ≤ β * Γ.card ∧
      minrank F (tposOf d b) (ballSystem τ₀ T D d b) ≤ β * Γ.card := by
  obtain ⟨h1, h2⟩ := P.net.minrank_le (fun ℓ => appendTime τ₀ T ℓ) P.φ P.φc (tposOf d b) β Γ D
    (P.trans_of_transposer hM) (fun s _ => P.val_card_le hβ s) hdepth
  exact ⟨h1, (minrank_mono _ fun ℓ => P.reach_subset_stepBall D (appendTime τ₀ T ℓ)).trans h2⟩

end Rigidity

end MergeDepth
