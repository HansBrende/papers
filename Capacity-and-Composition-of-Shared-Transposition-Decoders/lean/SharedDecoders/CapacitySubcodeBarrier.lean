import SharedDecoders.CapacitySubcodeMixture

/-! # A fixed-excess seed gives a fixed-excess subcode barrier

The cyclic lift preserves the receiver partition and deterministic decoding.
All subsequent width changes repeat the actual binary code. No linear extension
of a nonlinear decoder, and no coordinatewise assumption on subcode decoders,
appears in the endpoint.
-/

namespace SharedDecoders.CapacitySubcode

open Module

variable {s b : ℕ} [NeZero s]

omit [NeZero s] in
theorem liftedPartition_triple_period (hc : Nat.Coprime 3 s) {κ : Type*} (p : ZMod s → κ) :
    ∀ c, liftedPartition hc p (c + (s : ZMod (3 * s))) = liftedPartition hc p c := by
  intro c
  simp only [liftedPartition, map_add, map_natCast, Prod.snd_add, Prod.snd_natCast,
    ZMod.natCast_self, add_zero]

/-- The stated conditional positive-rate barrier, at the unchanged two-class
partition lifted to dimension `3*s`. The width is existential and may be large. -/
theorem above_half_seed_barrier (hodd : Odd s) (hc : Nat.Coprime 3 s)
    (hb : 0 < b) (p : ZMod s → Bool) (hp : Function.Surjective p)
    (G : Submodule Bit (State s (Fin b → Bit))) (hG : IsSharedCode Bit p G)
    (eps : ℝ) (heps : 0 < eps)
    (hrate : (finrank Bit G : ℝ) = (1 / 2 + eps) * (b * s * s)) :
    Function.Surjective (liftedPartition hc p) ∧
      ∃ B : ℕ, 0 < B ∧
        ∃ C : Submodule Bit (State (3 * s) (Fin B → Bit)),
          IsSharedCode Bit (liftedPartition hc p) C ∧
          (finrank Bit C : ℝ) =
            (1 / 2 + eps / (18 * eps + 12)) * (B * (3 * s) * (3 * s)) ∧
          ∀ D ≤ C, IsLinearSharedCode (liftedPartition hc p) D →
            (finrank Bit D : ℝ) ≤
              (1 / 2 - eps / (18 * eps + 12)) * (B * (3 * s) * (3 * s)) := by
  have hspos := NeZero.pos s
  have hvol : (0 : ℝ) < (b : ℝ) * s * s := by positivity
  have hnat : b * s * s < 2 * finrank Bit G := by
    have hh : (b : ℝ) * s * s < 2 * (finrank Bit G : ℝ) := by nlinarith
    exact_mod_cast hh
  let k := 2 * finrank Bit G - b * s * s
  have hk : 0 < k := Nat.sub_pos_of_lt hnat
  have hdim : 2 * finrank Bit G = b * s * s + k := by dsimp [k]; omega
  have hkreal : (k : ℝ) = 2 * eps * ((b : ℝ) * s * s) := by
    have hh : (2 : ℝ) * finrank Bit G = (b : ℝ) * s * s + k := by exact_mod_cast hdim
    nlinarith
  have hthree : (3 : Bit) ≠ 0 := by decide
  let G' := cyclicLiftCode hc G
  have hG' : IsSharedCode Bit (liftedPartition hc p) G' := hG.cyclicLiftCode hc hthree
  have hG'dim : 2 * finrank Bit G' = b * (3 * s) * (3 * s) + 3 * k := by
    have hh := two_mul_finrank_cyclicLiftCode hc hthree G
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hh
    dsimp [G']
    nlinarith
  have hoddlift : Odd (3 * s) := (by decide : Odd 3).mul hodd
  obtain ⟨B, hB, C, hC, hdimC, hlin⟩ := good_hard_mixture hoddlift (liftedPartition hc p)
    (liftedPartition_triple_period hc p) hb (by omega : 0 < 3 * k) G' hG' hG'dim
  have hdelta : ((3 * k : ℕ) : ℝ) /
      (8 * ((b : ℝ) * (3 * s) * (3 * s)) + 18 * ((3 * k : ℕ) : ℝ)) = eps / (18 * eps + 12) := by
    push_cast
    rw [hkreal]
    have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne s)
    have hbne : (b : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  refine ⟨liftedPartition_surjective hc hp, B, hB, C, hC, ?_, ?_⟩
  · convert hdimC using 1
    rw [hdelta]
  · intro D hD hdlin
    have hh := hlin D hD hdlin
    convert hh using 1
    rw [hdelta]

end SharedDecoders.CapacitySubcode
