import MergeDepth.HopFields
import MergeDepth.Capacity
import MotionDepthCodes.StorageCode

/-!
# Corollary HC* at one size

Theorem HC′(b) gives an index code for a ball system with few bits; a large fibre of it is a binary
storage code for a relation inside the balls (`isStorageCode_fibre_of_indexCode`). Lemma 3.14(b),
from an affirmative answer to Question 9.1, bounds such storage codes by `2^{(1/2 + δ) L}`. The
two are incompatible when the hop-charging rate is small (`cor_HCstar_step`): this is
Corollary HC* at one size, with the conclusion of Lemma 3.14(b) at that size as a hypothesis.
-/

namespace MergeDepth

open Finset BoundedNesting

/-- **A large fibre.** If a function of `L` input bits takes at most `M` values, one of its
fibres has at least `2^L / M` elements. -/
theorem exists_large_fibre_card {L : ℕ} {α : Type*} [DecidableEq α] (E : (Fin L → Bool) → α)
    {M : ℕ} (hM : (univ.image E).card ≤ M) :
    ∃ w₀, 2 ^ L ≤ M * (univ.filter fun w => E w = E w₀).card := by
  by_contra hno
  push Not at hno
  have hsum : (univ : Finset (Fin L → Bool)).card =
      ∑ a ∈ univ.image E, (univ.filter fun w => E w = a).card := card_eq_sum_card_image E univ
  have hcard : (univ : Finset (Fin L → Bool)).card = 2 ^ L := by simp
  have hne : (univ.image E).Nonempty := (univ_nonempty).image E
  have hlt : ∑ a ∈ univ.image E, M * (univ.filter fun w => E w = a).card <
      ∑ _a ∈ univ.image E, 2 ^ L := by
    refine sum_lt_sum_of_nonempty hne fun a ha => ?_
    obtain ⟨w₀, -, rfl⟩ := mem_image.mp ha
    exact hno w₀
  rw [← mul_sum, ← hsum, hcard, sum_const, smul_eq_mul] at hlt
  have : M * 2 ^ L < M * 2 ^ L :=
    hlt.trans_le (Nat.mul_le_mul_right _ hM)
  exact lt_irrefl _ this

/-- Every fibre of an index code for demands `tpos`, an involution, is a storage code for the
relation `q ↦ I (tpos q)`. -/
theorem isStorageCode_fibre_of_indexCode {L : ℕ} {α : Type*} [DecidableEq α]
    {E : (Fin L → Bool) → α} {I : Fin L → Finset (Fin L)} {tpos : Fin L → Fin L}
    (hcode : IsIndexCode E I tpos) (htpos : ∀ q, tpos (tpos q) = q) (a : α) :
    MotionDepthCodes.IsStorageCode (fun q => I (tpos q)) (univ.filter fun w => E w = a) := by
  intro x hx y hy q hq
  have hEx := (mem_filter.mp hx).2
  have hEy := (mem_filter.mp hy).2
  have := hcode (tpos q) x y (hEx.trans hEy.symm) hq
  rwa [htpos] at this

variable {L k : ℕ}

open Classical in
/-- **Corollary HC\* at one size.** Let `G` be a refinement of the dependency DAG of width `m`
satisfying the hypotheses of Theorem HC′(b) (`hop_charging_fields`), with merge depth at most `s`
outside a set `X` of at most `η L` output positions, `T ≤ C (L + 1)`, a cold genie at `(V, ε)`,
`γ = 1/2 - ε - η > 0` and `4 β m k C ≤ γ τ`. If every binary storage code for a relation inside the
balls of radius `(s + 1) τ D` has at most `2^{(1/2 + γ/4) L}` elements (Lemma 3.14(b) at this size),
the hypotheses are contradictory. -/
theorem cor_HCstar_step (G : FunDag L) (st : ℕ → ℕ) (nodesAt : ℕ → Finset ℕ) {m : ℕ}
    (hnodes : ∀ u t, u ∈ nodesAt t ↔ st u = t) (hwidth : ∀ t, (nodesAt t).card ≤ m)
    (xs : Fin k → ℕ → ℤ) {T V β C : ℕ} (hT : T ≤ C * (L + 1)) (hL : 1 ≤ L)
    (hedge : ∀ u, ∀ v ∈ G.out u, DepStep xs T (st u) (st v))
    (rdStep : ℕ → Option (Fin L)) (hrd : ∀ u j, G.rd u = some j → rdStep (st u) = some j)
    {ε η : ℝ} {D : ℕ} {ΓF : Finset ℕ} (hcold : IsColdGenie (L := L) xs T V β ε D ΓF)
    (hγ : 0 < 1 / 2 - ε - η)
    (hstep : ∀ t ∈ ΓF, (univ.image fun w => fun v : nodesAt t => G.val w v).card ≤ 2 ^ β)
    (hfield : ∀ u, (univ.image fun w => G.val w u).card ≤ 2 ^ β)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ G.net.paths u →
      LinNet.GFree (ΓF.biUnion nodesAt) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (st u) (st v)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (hτbig : 4 * β * m * k * C ≤ (1 / 2 - ε - η) * τ) (s : ℕ)
    (o : Fin L → ℕ) (tout : Fin L → ℕ) (hout : ∀ ℓ, st (o ℓ) = tout ℓ)
    (tpos : Fin L → Fin L) (htpos : ∀ q, tpos (tpos q) = q) (dec : Fin L → ℕ → Bool)
    (hdec : ∀ w ℓ, dec ℓ (G.val w (o ℓ)) = w (tpos ℓ))
    (X : Finset (Fin L)) (hX : (X.card : ℝ) ≤ η * L)
    (hround : ∀ ℓ ∉ X, ∀ π, π ∈ G.net.paths (o ℓ) → LinNet.GFree (ΓF.biUnion nodesAt) π →
      dm lin (fun u v => DeepStep xs T V (st u) (st v)) false π ≤ s)
    (hballs : ∀ N : Fin L → Finset (Fin L),
      (∀ q, N q ⊆ stepBall xs T rdStep ((s + 1) * τ * D) (tout (tpos q))) →
      ∀ Cd : Finset (Fin L → Bool), MotionDepthCodes.IsStorageCode N Cd →
        (Cd.card : ℝ) ≤ (2 : ℝ) ^ ((1 / 2 + (1 / 2 - ε - η) / 4) * L)) :
    False := by
  set γ := 1 / 2 - ε - η
  obtain ⟨Q, I, hQ, hcode, hball, himg⟩ := hop_charging_fields G st nodesAt hnodes hwidth xs hedge
    rdStep hrd hcold hstep hfield lin hside hτ s o tout hout tpos dec hdec X hround
  set E := fun w : Fin L → Bool => ((fun t : ΓF => fun v : nodesAt t.1 => G.val w v),
    (fun q : Q => G.val w q.1), (fun ℓ : X => w (tpos ℓ.1)))
  set bits := β * ΓF.card + β * Q.card + X.card
  -- a large fibre, which is a storage code for a relation inside the balls
  obtain ⟨w₀, hw₀⟩ := exists_large_fibre_card E himg
  have hsc := isStorageCode_fibre_of_indexCode hcode htpos (E w₀)
  have hsize := hballs (fun q => I (tpos q)) (fun q => hball (tpos q)) _ hsc
  set Fb := (univ.filter fun w => E w = E w₀).card
  -- `2^L ≤ 2^bits ⋅ |fibre| ≤ 2^{bits + (1/2 + γ/4) L}`
  have h1 : (2 : ℝ) ^ (L : ℝ) ≤ (2 : ℝ) ^ ((bits : ℝ) + (1 / 2 + γ / 4) * L) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    calc (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ bits * Fb : ℕ) : ℝ) := by exact_mod_cast hw₀
      _ = (2 : ℝ) ^ bits * Fb := by push_cast; ring
      _ ≤ (2 : ℝ) ^ bits * (2 : ℝ) ^ ((1 / 2 + γ / 4) * L) := by gcongr
  have h2 : (L : ℝ) ≤ bits + (1 / 2 + γ / 4) * L :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h1
  -- the bit count of Theorem HC′(b)
  have hRcard : (τ * Q.card : ℝ) ≤ m * k * C * (L + 1) := by
    have h3 : τ * Q.card ≤ m * (k * (C * (L + 1))) :=
      hQ.trans (Nat.mul_le_mul_left _ ((card_deepHops_le xs T V).trans
        (Nat.mul_le_mul_left _ hT)))
    have : (τ * Q.card : ℝ) ≤ m * (k * (C * (L + 1))) := by exact_mod_cast h3
    linarith
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hβQ : (β * Q.card : ℝ) ≤ γ * (L + 1) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hL0 : (0 : ℝ) ≤ L + 1 := by positivity
    have hβ0 : (0 : ℝ) ≤ β := by positivity
    have : (β : ℝ) * (τ * Q.card) ≤ β * (m * k * C * (L + 1)) :=
      mul_le_mul_of_nonneg_left hRcard hβ0
    have h4 : (4 * β * m * k * C : ℝ) * (L + 1) ≤ γ * τ * (L + 1) :=
      mul_le_mul_of_nonneg_right hτbig hL0
    nlinarith
  have hbits : (bits : ℝ) ≤ ε * L + γ * (L + 1) / 4 + η * L := by
    have : (bits : ℝ) = β * ΓF.card + β * Q.card + X.card := by push_cast [bits]; ring
    rw [this]
    linarith [hcold.1]
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have : γ * L / 2 ≤ γ / 4 := by
    simp only [γ] at h2 hbits ⊢
    nlinarith
  nlinarith

end MergeDepth
