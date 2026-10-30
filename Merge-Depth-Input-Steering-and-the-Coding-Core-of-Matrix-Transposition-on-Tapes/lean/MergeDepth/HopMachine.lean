import MergeDepth.Steps
import MergeDepth.ColdGenie

/-!
# Theorem HC′(a) for oblivious machines

A *cold genie at `(V, ε)` with depth `D`* (`IsColdGenie`) is a set `Γ` of steps of cost
`β |Γ| ≤ ε L` such that every `Γ`-free path of the dependency DAG of the work-head walks without deep
steps has at most `D` vertices. `cold_genie_exists` is Lemma 3.1: with `T ≤ C (L + 1)`, `C ≥ 1` and
`0 < ε`, a cold genie exists with depth `DF k (2V - 1) (ε / (4βC)) ⋅ ⌈4βC/ε⌉`.

`hop_charging_machine` is Theorem HC′(a): for a linear data path of width `m` on the dependency DAG
(its out-edges are dependency steps), whose steps take at most `2^β` values on binary inputs, a cold
genie, and a lineage assignment on the coordinate network whose other out-edges are dead, if the
`Γ`-free coordinate paths from the output coordinates of every position outside `X` have at most `s`
deep merges, then `P_tpos = R + S` with `rank R ≤ ε L + m k C (L + 1) / τ + |X|` and row `ℓ` of `S`
zero for `ℓ ∈ X` and supported in the ball of radius `(s + 1) τ D` around `tout ℓ` otherwise.
-/

namespace MergeDepth

open Finset Matrix Module BoundedNesting BoundedNesting.LinNet

variable {F : Type*} [Field F] {L m k : ℕ}

open Classical in
/-- A cold genie at `(V, ε)` with depth `D`, for value width `β`. -/
def IsColdGenie (xs : Fin k → ℕ → ℤ) (T V β : ℕ) (ε : ℝ) (D : ℕ) (Γ : Finset ℕ) : Prop :=
  (β * Γ.card : ℝ) ≤ ε * L ∧
    ∀ π, IsDepPath xs T π → LinNet.GFree Γ π → rCount (DeepStep xs T V) π = 0 → π.length ≤ D

/-- **Lemma 3.1.** Cold genies exist. -/
theorem cold_genie_exists (hk : 1 ≤ k) {V β C T : ℕ} (hV : 1 ≤ V) (hβ : 1 ≤ β) (hC : 1 ≤ C)
    (hL : 1 ≤ L) (hT : T ≤ C * (L + 1)) {ε : ℝ} (hε : 0 < ε) (xs : Fin k → ℕ → ℤ)
    (hx : ∀ h, IsWalk (xs h)) :
    ∃ Γ, IsColdGenie (L := L) xs T V β ε
      (DF k (2 * V - 1) (ε / (4 * β * C)) * ⌈4 * β * C / ε⌉₊) Γ := by
  have hβC : (0 : ℝ) < 4 * β * C := by positivity
  set P := ⌈4 * β * C / ε⌉₊
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  obtain ⟨Γ, hcard, hpath⟩ := cold_genie hk hV (div_pos hε hβC) hP xs hx T
  refine ⟨Γ, ?_, hpath⟩
  -- `β |Γ| ≤ β (ε/(4βC)) T + β T / P ≤ ε T / (2C) ≤ ε (L + 1)/2 ≤ ε L`
  have hPge : 4 * β * C / ε ≤ (P : ℝ) := Nat.le_ceil _
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hT' : (T : ℝ) ≤ C * (L + 1) := by exact_mod_cast hT
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hβ' : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have h1 : (Γ.card : ℝ) ≤ ε / (4 * β * C) * T + T / P := by
    have : (P : ℝ) * Γ.card ≤ P * (ε / (4 * β * C)) * T + T := hcard
    calc (Γ.card : ℝ) = (P * Γ.card) / P := by field_simp
      _ ≤ (P * (ε / (4 * β * C)) * T + T) / P := by gcongr
      _ = ε / (4 * β * C) * T + T / P := by field_simp
  have h2 : (T : ℝ) / P ≤ ε / (4 * β * C) * T := by
    rw [div_le_iff₀ hPpos]
    have : ε / (4 * β * C) * P ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (div_pos hε hβC), one_div_div]
      exact hPge
    have hT0 : (0 : ℝ) ≤ T := by positivity
    nlinarith
  have h3 : (β : ℝ) * Γ.card ≤ ε * T / (2 * C) := by
    have : (β : ℝ) * Γ.card ≤ β * (2 * (ε / (4 * β * C) * T)) := by
      gcongr
      linarith
    calc (β : ℝ) * Γ.card ≤ β * (2 * (ε / (4 * β * C) * T)) := this
      _ = ε * T / (2 * C) := by field_simp; ring
  calc (β : ℝ) * Γ.card ≤ ε * T / (2 * C) := h3
    _ ≤ ε * (C * (L + 1)) / (2 * C) := by gcongr
    _ = ε * (L + 1) / 2 := by field_simp
    _ ≤ ε * L := by nlinarith

/-- Paths of a network on the dependency DAG are dependency paths. -/
theorem isDepPath_of_paths {net : LinNet F L m} {xs : Fin k → ℕ → ℤ} {T : ℕ}
    (hout : ∀ t, ∀ s ∈ net.out t, DepStep xs T t s) :
    ∀ (π : List ℕ) (t : ℕ), π ∈ net.paths t → IsDepPath xs T π
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: π, t, h => by
    have := head_eq_of_mem_paths h
    subst this
    obtain ⟨hb, hπ⟩ := cons_cons_mem_paths.mp h
    exact ⟨hout a b hb, isDepPath_of_paths hout (b :: π) b hπ⟩

open Classical in
/-- **Theorem HC′(a)** for an oblivious machine with a linear data path. -/
theorem hop_charging_machine (net : LinNet F L m) (hm : 0 < m) (xs : Fin k → ℕ → ℤ) {T C V β : ℕ}
    (hT : T ≤ C * (L + 1)) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
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
  -- the deep pairs `(end, start)` of the deep hops
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
  have hq' : (τ * q : ℝ) ≤ m * k * C * (L + 1) := by
    have h1 : τ * q ≤ m * (k * T) := hq.trans (Nat.mul_le_mul_left _ hRcard)
    have h2 : m * (k * T) ≤ m * (k * (C * (L + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT)
    have := h1.trans h2
    have h3 : (τ * q : ℝ) ≤ m * (k * (C * (L + 1))) := by exact_mod_cast this
    linarith
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hqr : (q : ℝ) ≤ m * k * C * (L + 1) / τ := by
    rw [le_div_iff₀ hτ']; linarith
  have hr : (R.rank : ℝ) ≤ β * ΓF.card + q + X.card := by exact_mod_cast hrank
  linarith [hcold.1]

end MergeDepth
