import DirectedRecovery.Hyperfinite

/-!
# [Q9.1]: an affirmative answer to Question 9.1 of the fifth paper

Question 9.1 of *Directed Recovery Structures in Tape Computations*: fix a degree bound `Δ`; let `N_j` be recovery relations on finite coordinate sets `V_j` with
`|V_j| → ∞`, whose paired incidence graphs have maximum degree at most `Δ` and satisfy the
paired-distance condition. Must every sequence of nonempty storage codes `𝒞_j ⊆ 𝒜_j^{V_j}`, over
finite alphabets with `|𝒜_j| ≥ 2` that may vary, satisfy
`limsup_j log_{|𝒜_j|} |𝒞_j| / |V_j| ≤ 1/2`?

The definitions use the fifth paper's library unchanged: the paired incidence graph
`pairedIncidenceGraph` (left port `inl p`, right port `inr q`, an edge exactly when `p ∈ N q`;
loops `p ∈ N p` are allowed), the paired-distance condition `HasPairedDistanceSeparation`
(`|{p : dist(inl p, inr p) ≤ K}| / |V_j| → 0` for every fixed `K > 0`, disconnected ports at
infinite distance), storage codes `MotionDepthCodes.IsStorageCode` (arbitrary, nonlinear) and the
rate `storageCodeRate C = log_{|𝒜|} |C| / |V|`.

* `Q91At Δ`: Question 9.1 at the degree bound `Δ`, all finite alphabets (the alphabets may vary
  with the index). `Q91 = ∀ Δ, Q91At Δ` is [Q9.1] as the paper uses it.
* `Q91BinaryAt Δ`, `Q91Binary`: the same for binary codes (alphabet `Bool`), the case the paper's
  applications need ("the binary alphabet suffices").
* `Q91At.binary`, `Q91.binary`: the all-alphabet form implies the binary one.
* `storageCodeRate_nonneg`, `storageCodeRate_le_one`: rates of nonempty codes lie in `[0, 1]`, so
  the `limsup` is that of a bounded sequence (no junk value of `limsup` is involved).
* `Q91At.eventually`, `Q91BinaryAt.eventually`: the equivalent eventual form,
  `∀ ε > 0, ∀ᶠ j, rate(𝒞_j) ≤ 1/2 + ε`, which is how [Q9.1] is applied.

Coordinate sets and alphabets are types in `Type`; every finite set is equivalent to one. The
indexing by `ℕ` is that of the fifth paper's `HasPairedDistanceSeparation`; a sequence along a
subsequence of sizes is such a sequence.
-/

namespace MergeDepth

open Filter DirectedRecovery MotionDepthCodes

set_option autoImplicit false

open Classical in
/-- **Question 9.1 of the fifth paper at the degree bound `Δ`, all finite alphabets.** For every
sequence of recovery relations `N n` on finite coordinate types `V n` with `|V n| → ∞`, whose
paired incidence graphs have maximum degree at most `Δ` and which satisfy the paired-distance
condition, and every sequence of nonempty storage codes `C n` for `N n` over finite alphabets
`A n` with `|A n| ≥ 2`, the rates satisfy `limsup rate(C n) ≤ 1/2`. -/
def Q91At (Δ : ℕ) : Prop :=
  ∀ (V : ℕ → Type) [∀ n, Fintype (V n)] (N : (n : ℕ) → V n → Finset (V n)),
    Tendsto (fun n => Fintype.card (V n)) atTop atTop →
    (∀ n v, (pairedIncidenceGraph (N n)).degree v ≤ Δ) →
    HasPairedDistanceSeparation N →
    ∀ (A : ℕ → Type) [∀ n, Fintype (A n)], (∀ n, 2 ≤ Fintype.card (A n)) →
    ∀ C : (n : ℕ) → Finset (V n → A n), (∀ n, IsStorageCode (N n) (C n)) →
      (∀ n, (C n).Nonempty) →
      limsup (fun n => storageCodeRate (C n)) atTop ≤ 1 / 2

/-- **[Q9.1]**: an affirmative answer to Question 9.1 for every degree bound, all alphabets. -/
def Q91 : Prop := ∀ Δ, Q91At Δ

open Classical in
/-- **Question 9.1 at the degree bound `Δ` for binary codes** (alphabet `Bool`). -/
def Q91BinaryAt (Δ : ℕ) : Prop :=
  ∀ (V : ℕ → Type) [∀ n, Fintype (V n)] (N : (n : ℕ) → V n → Finset (V n)),
    Tendsto (fun n => Fintype.card (V n)) atTop atTop →
    (∀ n v, (pairedIncidenceGraph (N n)).degree v ≤ Δ) →
    HasPairedDistanceSeparation N →
    ∀ C : (n : ℕ) → Finset (V n → Bool), (∀ n, IsStorageCode (N n) (C n)) →
      (∀ n, (C n).Nonempty) →
      limsup (fun n => storageCodeRate (C n)) atTop ≤ 1 / 2

/-- **Binary [Q9.1]**: an affirmative answer to Question 9.1 for every degree bound and binary
codes. This is the form the applications in the paper use. -/
def Q91Binary : Prop := ∀ Δ, Q91BinaryAt Δ

/-- The all-alphabet question at `Δ` contains the binary one (constant alphabet `Bool`). -/
theorem Q91At.binary {Δ : ℕ} (h : Q91At Δ) : Q91BinaryAt Δ := by
  intro V _ N hsize hdeg hsep C hC hne
  exact h V N hsize hdeg hsep (fun _ => Bool) (fun _ => by simp) C hC hne

/-- **[Q9.1] for all alphabets implies binary [Q9.1].** -/
theorem Q91.binary (h : Q91) : Q91Binary := fun Δ => (h Δ).binary

/-! ### Rates are bounded, and the eventual form -/

section Rates

variable {W A : Type*} [Fintype W] [Fintype A]

/-- The rate of a nonempty code over an alphabet of at least two letters is nonnegative. -/
theorem storageCodeRate_nonneg (hA : 2 ≤ Fintype.card A) {C : Finset (W → A)}
    (hC : C.Nonempty) : 0 ≤ storageCodeRate C := by
  unfold storageCodeRate
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Real.logb_nonneg (by exact_mod_cast hA) (by exact_mod_cast hC.card_pos)

/-- The rate of any code over an alphabet of at least two letters is at most one. -/
theorem storageCodeRate_le_one (hA : 2 ≤ Fintype.card A) (C : Finset (W → A)) :
    storageCodeRate C ≤ 1 := by
  classical
  unfold storageCodeRate
  have hA1 : (1 : ℝ) < Fintype.card A := by exact_mod_cast hA
  rcases Nat.eq_zero_or_pos (Fintype.card W) with hW | hW
  · simp [hW]
  have hWr : (0 : ℝ) < Fintype.card W := by exact_mod_cast hW
  rw [div_le_one hWr]
  rcases Nat.eq_zero_or_pos C.card with hC | hC
  · simp [hC]
  have hcard : (C.card : ℝ) ≤ (Fintype.card A : ℝ) ^ (Fintype.card W : ℝ) := by
    have h := Finset.card_le_univ C
    rw [Fintype.card_fun] at h
    rw [Real.rpow_natCast]
    exact_mod_cast h
  calc Real.logb (Fintype.card A) C.card
      ≤ Real.logb (Fintype.card A) ((Fintype.card A : ℝ) ^ (Fintype.card W : ℝ)) :=
        (Real.logb_le_logb hA1 (by exact_mod_cast hC) (by positivity)).mpr hcard
    _ = Fintype.card W := Real.logb_rpow (by linarith) hA1.ne'

end Rates

/-- From `limsup ≤ 1/2` for rates bounded by one: eventually `rate ≤ 1/2 + ε`. -/
theorem eventually_le_of_limsup_le {u : ℕ → ℝ} (hu : ∀ n, u n ≤ 1)
    (h : limsup u atTop ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, u n ≤ 1 / 2 + ε := by
  have hb : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of ⟨1, hu⟩
  have hlt : limsup u atTop < 1 / 2 + ε := by linarith
  exact (eventually_lt_of_limsup_lt hlt hb).mono fun n hn => hn.le

open Classical in
/-- **[Q9.1] at `Δ`, eventual form.** Under the hypotheses of Question 9.1, for every `ε > 0`
the rates are eventually at most `1/2 + ε`. -/
theorem Q91At.eventually {Δ : ℕ} (h : Q91At Δ) (V : ℕ → Type) [∀ n, Fintype (V n)]
    (N : (n : ℕ) → V n → Finset (V n)) (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hdeg : ∀ n v, (pairedIncidenceGraph (N n)).degree v ≤ Δ)
    (hsep : HasPairedDistanceSeparation N) (A : ℕ → Type) [∀ n, Fintype (A n)]
    (hA : ∀ n, 2 ≤ Fintype.card (A n)) (C : (n : ℕ) → Finset (V n → A n))
    (hC : ∀ n, IsStorageCode (N n) (C n)) (hne : ∀ n, (C n).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, storageCodeRate (C n) ≤ 1 / 2 + ε :=
  eventually_le_of_limsup_le (fun n => storageCodeRate_le_one (hA n) (C n))
    (h V N hsize hdeg hsep A hA C hC hne) hε

open Classical in
/-- **Binary [Q9.1] at `Δ`, eventual form.** -/
theorem Q91BinaryAt.eventually {Δ : ℕ} (h : Q91BinaryAt Δ) (V : ℕ → Type) [∀ n, Fintype (V n)]
    (N : (n : ℕ) → V n → Finset (V n)) (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hdeg : ∀ n v, (pairedIncidenceGraph (N n)).degree v ≤ Δ)
    (hsep : HasPairedDistanceSeparation N) (C : (n : ℕ) → Finset (V n → Bool))
    (hC : ∀ n, IsStorageCode (N n) (C n)) (hne : ∀ n, (C n).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, storageCodeRate (C n) ≤ 1 / 2 + ε :=
  eventually_le_of_limsup_le (fun n => storageCodeRate_le_one (by simp) (C n))
    (h V N hsize hdeg hsep C hC hne) hε

end MergeDepth
