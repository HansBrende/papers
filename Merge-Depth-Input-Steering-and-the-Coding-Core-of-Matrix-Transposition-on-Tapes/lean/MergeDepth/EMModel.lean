import Mathlib
import Transpose.Statement

/-!
# The external-memory model (Definition 6.3)

The external-memory model of Aggarwal and Vitter in the form of Definition 6.3. An alphabet `Λ`
contains three distinct letters `0`, `1` and the blank (`Alphabet`). A *block* is a word in `Λ^B`,
a *disk* assigns a block to every address `a ∈ ℤ`, and the *internal memory* consists of `m` slots
holding one block each and a register of `r` bits (`Mem`). An *I/O* is a triple `(σ, i, a)` of a
direction, a slot and an address (`IO`). An *external-memory algorithm* (`Alg`) maps the memory
contents `μ` to `halt` (`none`) or to `(σ, i, a, μ')`: the memory is replaced by `μ'` (free internal
computation) and the I/O is performed. `Runs A μ D ios D'` says that the run from memory `μ` and
disk `D` halts after the I/O sequence `ios` with final disk `D'`; runs are deterministic
(`Runs.det`).

The paper's disks are blank at all but finitely many addresses. Here a disk is any map `ℤ → Λ^B`;
the runs considered start from the finitely supported input disks, and runs preserve finite
support (`Runs.finite_nonblank`), so nothing changes.

For transposition at dimension `d` (block size `B = d b(d)`, one matrix row) the initial disk holds
row `i` of the input word at address `i` (`inputDisk`); the algorithm is correct on `w` if, whenever
`w = encode d b(d) X`, its run halts with row `j` of `encode d b(d) Xᵀ` at address `d + j`
(`CorrectAt`), and oblivious on a set `C` of input words if all runs on `C` halt with one I/O
sequence (`ObliviousOn`).

## Internal steps

`collapse inner enc dec` turns an abstract step function `inner` on (slots, abstract register),
whose results are `halt`, an internal step `tau`, or an I/O, into an external-memory algorithm: one
application follows internal steps until the first halt or I/O (`settle`), and the abstract
register is stored through `enc` and read back through `dec`. `MRuns.runs`: a halting run of
`inner` in which every visited register is `good`, with `dec ∘ enc = id` on good registers, is a
run of `collapse inner enc dec` with the same I/O sequence and final disk. `exists_enc` provides an
injective encoding of a finite type into `r` bits, with a chosen element sent to the zero register,
once `2^r` is at least its cardinality.
-/

namespace MergeDepth.EM

/-- The direction of an I/O. -/
inductive IODir
  | read
  | write
  deriving DecidableEq, Repr

/-- An alphabet with three distinct letters `0`, `1` and the blank. Finiteness is required where
it is used (`[Fintype Λ]`). -/
structure Alphabet (Λ : Type*) where
  /-- the letter `0` -/
  zero : Λ
  /-- the letter `1` -/
  one : Λ
  /-- the blank -/
  blank : Λ
  zero_ne_one : zero ≠ one
  zero_ne_blank : zero ≠ blank
  one_ne_blank : one ≠ blank

/-- The letter of a bit. -/
def Alphabet.bit {Λ : Type*} (al : Alphabet Λ) : Bool → Λ
  | false => al.zero
  | true => al.one

variable {Λ : Type*} {B m r : ℕ}

/-- A block: a word of length `B`. -/
abbrev Block (Λ : Type*) (B : ℕ) := Fin B → Λ

/-- A disk: a block at every address. -/
abbrev Disk (Λ : Type*) (B : ℕ) := ℤ → Block Λ B

/-- The internal memory: `m` slots holding one block each, and an `r`-bit register. -/
abbrev Mem (Λ : Type*) (B m r : ℕ) := (Fin m → Block Λ B) × (Fin r → Bool)

/-- An I/O `(σ, i, a)`: a direction, a slot and an address. -/
abbrev IO (m : ℕ) := IODir × Fin m × ℤ

/-- An external-memory algorithm: on memory contents `μ` it halts (`none`) or replaces the memory
by `μ'` and performs the I/O `(σ, i, a)` (`some (σ, i, a, μ')`). -/
abbrev Alg (Λ : Type*) (B m r : ℕ) := Mem Λ B m r → Option (IODir × Fin m × ℤ × Mem Λ B m r)

/-- `Runs A μ D ios D'`: the run of `A` from memory `μ` and disk `D` halts after performing the
I/O sequence `ios`, with final disk `D'`. A read replaces the memory by `μ'` with slot `i` replaced
by `D a`; a write sets `D a` to slot `i` of `μ'` and replaces the memory by `μ'`. -/
inductive Runs (A : Alg Λ B m r) : Mem Λ B m r → Disk Λ B → List (IO m) → Disk Λ B → Prop
  | halt {μ D} : A μ = none → Runs A μ D [] D
  | read {μ D i a μ' ios D'} : A μ = some (.read, i, a, μ') →
      Runs A (Function.update μ'.1 i (D a), μ'.2) D ios D' → Runs A μ D ((.read, i, a) :: ios) D'
  | write {μ D i a μ' ios D'} : A μ = some (.write, i, a, μ') →
      Runs A μ' (Function.update D a (μ'.1 i)) ios D' → Runs A μ D ((.write, i, a) :: ios) D'

/-- Runs are deterministic. -/
theorem Runs.det {A : Alg Λ B m r} {μ : Mem Λ B m r} {D D' D'' : Disk Λ B}
    {ios ios' : List (IO m)} (h : Runs A μ D ios D') (h' : Runs A μ D ios' D'') :
    ios = ios' ∧ D' = D'' := by
  induction h generalizing ios' D'' with
  | halt hA =>
    cases h' with
    | halt _ => exact ⟨rfl, rfl⟩
    | read hA' _ => rw [hA] at hA'; cases hA'
    | write hA' _ => rw [hA] at hA'; cases hA'
  | read hA _ ih =>
    cases h' with
    | halt hA' => rw [hA] at hA'; cases hA'
    | read hA' h2 =>
      rw [hA] at hA'
      simp only [Option.some.injEq, Prod.mk.injEq] at hA'
      obtain ⟨-, rfl, rfl, rfl⟩ := hA'
      obtain ⟨rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl⟩
    | write hA' _ =>
      rw [hA] at hA'
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at hA'
  | write hA _ ih =>
    cases h' with
    | halt hA' => rw [hA] at hA'; cases hA'
    | read hA' _ =>
      rw [hA] at hA'
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at hA'
    | write hA' h2 =>
      rw [hA] at hA'
      simp only [Option.some.injEq, Prod.mk.injEq] at hA'
      obtain ⟨-, rfl, rfl, rfl⟩ := hA'
      obtain ⟨rfl, rfl⟩ := ih h2
      exact ⟨rfl, rfl⟩

/-- A run depends on the memory only through the algorithm's answer to it. -/
theorem Runs.congr {A : Alg Λ B m r} {μ μ' : Mem Λ B m r} {D D' : Disk Λ B} {ios : List (IO m)}
    (hA : A μ = A μ') (h : Runs A μ D ios D') : Runs A μ' D ios D' := by
  cases h with
  | halt h0 => exact .halt (hA ▸ h0)
  | read h0 h1 => exact .read (hA ▸ h0) h1
  | write h0 h1 => exact .write (hA ▸ h0) h1

/-- Runs preserve the finiteness of the set of non-blank addresses. -/
theorem Runs.finite_nonblank {A : Alg Λ B m r} {μ : Mem Λ B m r} {D D' : Disk Λ B}
    {ios : List (IO m)} (bl : Λ) (h : Runs A μ D ios D')
    (hD : {a | D a ≠ fun _ => bl}.Finite) : {a | D' a ≠ fun _ => bl}.Finite := by
  induction h with
  | halt _ => exact hD
  | read _ _ ih => exact ih hD
  | @write μ D i a μ' ios D' _ _ ih =>
    refine ih ((hD.insert a).subset fun a' ha' => ?_)
    by_cases h : a' = a
    · exact Or.inl h
    · right
      simpa [Function.update_of_ne h] using ha'

/-- The initial memory: blank slots and a zero register. -/
def initMem (al : Alphabet Λ) : Mem Λ B m r := (fun _ _ => al.blank, fun _ => false)

/-- The initial disk on input `w` for dimension `d` and block size `B`: row `i` of `w` (its bits
at positions `iB, …, iB + B - 1`) at address `i` for `0 ≤ i < d`, blank elsewhere. -/
def inputDisk (al : Alphabet Λ) (d B : ℕ) (w : List Bool) : Disk Λ B := fun a =>
  if 0 ≤ a ∧ a < d then fun q => al.bit (w.getD (a.toNat * B + q) false) else fun _ => al.blank

/-- The input disk is blank outside the addresses `0, …, d - 1`. -/
theorem inputDisk_finite (al : Alphabet Λ) (d B : ℕ) (w : List Bool) :
    {a | inputDisk al d B w a ≠ fun _ => al.blank}.Finite := by
  refine (Set.finite_Ico (0 : ℤ) d).subset fun a ha => ?_
  by_contra h
  simp only [Set.mem_Ico] at h
  exact ha (by simp only [inputDisk]; rw [ite_eq_right h])

/-- Row `j` of a word `v` as a block: its bits at positions `jB, …, jB + B - 1`. -/
def rowBlock (al : Alphabet Λ) (B : ℕ) (v : List Bool) (j : ℕ) : Block Λ B :=
  fun q => al.bit (v.getD (j * B + q) false)

/-- On input `w` at dimension `d`, the run of `A` halts after the I/O sequence `ios` with row `j`
of the word `v` at address `d + j`, for every `j < d`. -/
def HaltsWith (A : Alg Λ B m r) (al : Alphabet Λ) (d : ℕ) (w : List Bool) (ios : List (IO m))
    (v : List Bool) : Prop :=
  ∃ D', Runs A (initMem al) (inputDisk al d B w) ios D' ∧
    ∀ j < d, D' ((d : ℤ) + j) = rowBlock al B v j

/-- Correctness on the input word `w` for transposition at dimension `d` (block size
`B = d b(d)`): whenever `w` encodes the matrix `X`, the run halts with row `j` of the encoding of
`Xᵀ` at address `d + j`, for every `j < d`. Every word of length `L = d² b(d)` encodes a matrix
(`Transpose.Tape.Impl.matrixInputs_eq`). -/
def CorrectAt {d : ℕ} (A : Alg Λ (d * Transpose.entryBits d) m r) (al : Alphabet Λ)
    (w : List Bool) : Prop :=
  ∀ X : Transpose.Matrix, Transpose.encode d (Transpose.entryBits d) X = w →
    ∃ ios, HaltsWith A al d w ios (Transpose.encode d (Transpose.entryBits d) (Transpose.transpose X))

/-- Obliviousness on a set `C` of input words: the runs on all words of `C` halt with one I/O
sequence. -/
def ObliviousOn (A : Alg Λ B m r) (al : Alphabet Λ) (d : ℕ) (C : Finset (List Bool)) : Prop :=
  ∃ ios, ∀ w ∈ C, ∃ D', Runs A (initMem al) (inputDisk al d B w) ios D'

/-! ## Collapsing internal steps -/

/-- The result of one step of an abstract algorithm: halt, an internal step to `s`, or the I/O
`(σ, i, a)` after replacing the abstract state by `s`. -/
inductive Micro (S : Type*) (m : ℕ)
  | halt
  | tau (s : S)
  | io (σ : IODir) (i : Fin m) (a : ℤ) (s : S)

/-- Whether a step result is an internal step. -/
def Micro.isTau {S : Type*} : Micro S m → Bool
  | .tau _ => true
  | _ => false

section Collapse

variable {R : Type*}
  (inner : (Fin m → Block Λ B) × R → Micro ((Fin m → Block Λ B) × R) m)

/-- Follow at most `n` internal steps after the first step. -/
def chase : ℕ → (Fin m → Block Λ B) × R → Micro ((Fin m → Block Λ B) × R) m
  | 0, s => inner s
  | n + 1, s => match inner s with
    | .tau s' => chase n s'
    | x => x

open Classical in
/-- The first result after the internal steps from `s`: a halt or an I/O (`halt` if internal
steps never end). -/
noncomputable def settle (s : (Fin m → Block Λ B) × R) : Micro ((Fin m → Block Λ B) × R) m :=
  if h : ∃ n, (chase inner n s).isTau = false then chase inner (Nat.find h) s else .halt

/-- The external-memory algorithm of `inner`: one application follows the internal steps to the
next halt or I/O; the abstract register is stored through `enc` and read through `dec`. -/
noncomputable def collapse (enc : R → Fin r → Bool) (dec : (Fin r → Bool) → R) : Alg Λ B m r :=
  fun μ => match settle inner (μ.1, dec μ.2) with
    | .io σ i a s' => some (σ, i, a, (s'.1, enc s'.2))
    | _ => none

/-- Halting runs of `inner` in which every visited register satisfies `good`. -/
inductive MRuns (good : R → Prop) :
    (Fin m → Block Λ B) × R → Disk Λ B → List (IO m) → Disk Λ B → Prop
  | halt {s D} : good s.2 → inner s = .halt → MRuns good s D [] D
  | tau {s s' D ios D'} : good s.2 → inner s = .tau s' → MRuns good s' D ios D' →
      MRuns good s D ios D'
  | read {s s' D i a ios D'} : good s.2 → inner s = .io .read i a s' →
      MRuns good (Function.update s'.1 i (D a), s'.2) D ios D' →
      MRuns good s D ((.read, i, a) :: ios) D'
  | write {s s' D i a ios D'} : good s.2 → inner s = .io .write i a s' →
      MRuns good s' (Function.update D a (s'.1 i)) ios D' →
      MRuns good s D ((.write, i, a) :: ios) D'

variable {inner}

theorem chase_succ_of_tau {s s' : (Fin m → Block Λ B) × R} (h : inner s = .tau s') (n : ℕ) :
    chase inner (n + 1) s = chase inner n s' := by
  simp only [chase, h]

theorem chase_succ_of_settled {s : (Fin m → Block Λ B) × R} {n : ℕ}
    (h : (chase inner n s).isTau = false) : chase inner (n + 1) s = chase inner n s := by
  induction n generalizing s with
  | zero =>
    simp only [chase] at h ⊢
    cases hs : inner s with
    | halt => rfl
    | tau s' => rw [hs] at h; simp [Micro.isTau] at h
    | io σ i a s' => rfl
  | succ n ih =>
    cases hs : inner s with
    | halt => simp only [chase, hs]
    | tau s' =>
      rw [chase_succ_of_tau hs] at h
      rw [chase_succ_of_tau hs, chase_succ_of_tau hs, ih h]
    | io σ i a s' => simp only [chase, hs]

theorem chase_eq_of_le {s : (Fin m → Block Λ B) × R} {n n' : ℕ}
    (h : (chase inner n s).isTau = false) (hle : n ≤ n') : chase inner n' s = chase inner n s := by
  induction n' with
  | zero => rw [Nat.le_zero.mp hle]
  | succ n' ih =>
    rcases Nat.lt_or_ge n (n' + 1) with hlt | hge
    · have e := ih (Nat.lt_succ_iff.mp hlt)
      rw [chase_succ_of_settled (e ▸ h), e]
    · rw [le_antisymm hle hge]

theorem settle_eq {s : (Fin m → Block Λ B) × R} {n : ℕ} (h : (chase inner n s).isTau = false) :
    settle inner s = chase inner n s := by
  classical
  have hex : ∃ n, (chase inner n s).isTau = false := ⟨n, h⟩
  rw [settle, dite_eq_left hex]
  have h1 := Nat.find_spec hex
  have h2 := Nat.find_min' hex h
  rw [chase_eq_of_le h1 h2]

theorem settle_of_tau {s s' : (Fin m → Block Λ B) × R} (h : inner s = .tau s') {n : ℕ}
    (hn : (chase inner n s').isTau = false) : settle inner s = settle inner s' := by
  rw [settle_eq hn, settle_eq (n := n + 1) (by rwa [chase_succ_of_tau h]),
    chase_succ_of_tau h]

theorem settle_of_halt {s : (Fin m → Block Λ B) × R} (h : inner s = .halt) :
    settle inner s = .halt := by
  rw [settle_eq (n := 0) (by simp [chase, h, Micro.isTau])]
  simp [chase, h]

theorem settle_of_io {s s' : (Fin m → Block Λ B) × R} {σ : IODir} {i : Fin m} {a : ℤ}
    (h : inner s = .io σ i a s') : settle inner s = .io σ i a s' := by
  rw [settle_eq (n := 0) (by simp [chase, h, Micro.isTau])]
  simp [chase, h]

variable {good : R → Prop}

/-- A micro-run reaches a halt or an I/O after finitely many internal steps. -/
theorem MRuns.settled {s : (Fin m → Block Λ B) × R} {D D' : Disk Λ B} {ios : List (IO m)}
    (h : MRuns inner good s D ios D') : ∃ n, (chase inner n s).isTau = false := by
  induction h with
  | halt _ h0 => exact ⟨0, by simp [chase, h0, Micro.isTau]⟩
  | tau _ h0 _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rwa [chase_succ_of_tau h0]⟩
  | read _ h0 _ => exact ⟨0, by simp [chase, h0, Micro.isTau]⟩
  | write _ h0 _ => exact ⟨0, by simp [chase, h0, Micro.isTau]⟩

/-- **Collapsing internal steps.** A halting micro-run through good registers is a run of the
collapsed algorithm with the same I/O sequence and final disk. -/
theorem MRuns.runs {enc : R → Fin r → Bool} {dec : (Fin r → Bool) → R}
    (henc : ∀ ρ, good ρ → dec (enc ρ) = ρ) {s : (Fin m → Block Λ B) × R} {D D' : Disk Λ B}
    {ios : List (IO m)} (h : MRuns inner good s D ios D') :
    Runs (collapse inner enc dec) (s.1, enc s.2) D ios D' := by
  induction h with
  | @halt s D hg h0 =>
    refine .halt ?_
    simp only [collapse, henc _ hg, settle_of_halt h0]
  | @tau s s' D ios D' hg h0 h1 ih =>
    obtain ⟨n, hn⟩ := MRuns.settled h1
    refine Runs.congr ?_ ih
    have hg' : good s'.2 := by cases h1 <;> assumption
    simp only [collapse, henc _ hg, henc _ hg', settle_of_tau h0 hn]
  | @read s s' D i a ios D' hg h0 _ ih =>
    refine .read (μ' := (s'.1, enc s'.2)) ?_ ih
    simp only [collapse, henc _ hg, settle_of_io h0]
  | @write s s' D i a ios D' hg h0 _ ih =>
    refine .write (μ' := (s'.1, enc s'.2)) ?_ ih
    simp only [collapse, henc _ hg, settle_of_io h0]

end Collapse

/-- An injective encoding of a finite type into `r` bits that sends `x₀` to the zero register,
when `2^r` is at least the cardinality of the type. -/
theorem exists_enc {F : Type*} [Fintype F] (x₀ : F) {r : ℕ}
    (hr : Fintype.card F ≤ 2 ^ r) :
    ∃ e : F → Fin r → Bool, Function.Injective e ∧ e x₀ = fun _ => false := by
  classical
  have hc : Fintype.card F ≤ Fintype.card (Fin r → Bool) := by simpa using hr
  obtain ⟨e₀⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun x => Equiv.swap (e₀ x₀) (fun _ => false) (e₀ x), ?_, ?_⟩
  · exact (Equiv.injective _).comp e₀.injective
  · simp

end MergeDepth.EM
