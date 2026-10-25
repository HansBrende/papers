import SubcubicMemo.HigherRankGeometry

/-! Exact six-coordinate support around three successive plane coordinates. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U}

structure TripleSupport (U : V → Submodule K W) (r : Recovery U)
    (p a b d z y : V) (S : Submodule K W) : Prop where
  dimension : finrank K S = 5
  tight : defect U S = 1
  left : U a ⊓ S = U a
  middle : U b ⊓ S = U b
  right : U d ⊓ S = U d
  back : U p ⊓ S = LinearMap.range (r.component a p)
  side_left : U z ⊓ S = LinearMap.range (r.component a z)
  side_right : U y ⊓ S = LinearMap.range (r.component b y)
  outside : ∀ w, w ≠ a → w ≠ b → w ≠ d → w ≠ p → w ≠ z → w ≠ y → U w ⊓ S = ⊥
  small : ∀ w, w ≠ a → w ≠ b → w ≠ d → finrank K (U w ⊓ S : Submodule K W) ≤ 1

theorem TripleSupport.full_plane_iff {p a b d z y : V} {S : Submodule K W}
    (h : TripleSupport U r p a b d z y S) {w : V} (hw : finrank K (U w) = 2) :
    U w ≤ S ↔ w = a ∨ w = b ∨ w = d := by
  constructor
  · intro hle
    by_contra hn
    have hwa : w ≠ a := fun he => hn (Or.inl he)
    have hwb : w ≠ b := fun he => hn (Or.inr (Or.inl he))
    have hwd : w ≠ d := fun he => hn (Or.inr (Or.inr he))
    have hd := h.small w hwa hwb hwd
    rw [inf_eq_left.mpr hle, hw] at hd
    omega
  · rintro (rfl | rfl | rfl)
    · exact inf_eq_left.mp h.left
    · exact inf_eq_left.mp h.middle
    · exact inf_eq_left.mp h.right

variable (c : HighCore G U r)
include c

theorem HighCore.triple_support {p a b d z y : V}
    (hpa : High r p a) (hab : High r a b) (hbd : High r b d)
    (hzp : z ≠ p) (hzb : z ≠ b) (hza : z ≠ a)
    (haN : G.neighborFinset a = {p, b, z})
    (hya : y ≠ a) (hyd : y ≠ d) (hyb : y ≠ b)
    (hbN : G.neighborFinset b = {a, d, y}) :
    TripleSupport U r p a b d z y
      ((U a ⊔ U b) ⊔ LinearMap.range (r.component b y)) := by
  have hpaA := c.high_adj hpa
  have habA := c.high_adj hab
  have hbdA := c.high_adj hbd
  have hazA : G.Adj a z := (G.mem_neighborFinset a z).mp (by rw [haN]; simp)
  have hbyA : G.Adj b y := (G.mem_neighborFinset b y).mp (by rw [hbN]; simp)
  have had := c.path_two_ne hab hbd
  have hpb := c.path_two_ne hpa hab
  have hpd := c.path_three_ne hpa hab hbd
  have hzd : z ≠ d := by
    intro he
    subst z
    exact c.triangle {a, b, d} (SimpleGraph.is3Clique_triple_iff.mpr ⟨habA, hazA, hbdA⟩)
  have hyp : y ≠ p := by
    intro he
    subst y
    exact c.triangle {p, a, b} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpaA, hbyA.symm, habA⟩)
  have hzy : z ≠ y := by
    rintro rfl
    exact c.triangle {a, b, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨habA, hazA, hbyA⟩)
  let S := (U a ⊔ U b) ⊔ LinearMap.range (r.component b y)
  have haS : U a ≤ S := le_sup_left.trans le_sup_left
  have hbS : U b ≤ S := le_sup_right.trans le_sup_left
  have hyS : LinearMap.range (r.component b y) ≤ S := le_sup_right
  have hdS : U d ≤ S := by
    apply c.high_target_le hbd S hbS
    intro w hwd
    by_cases hwA : G.Adj b w
    · have hwN := (G.mem_neighborFinset b w).mpr hwA
      rw [hbN] at hwN
      simp only [mem_insert, mem_singleton] at hwN
      rcases hwN with hw | hw | hw
      · subst w; exact (r.target b a).trans haS
      · exact False.elim (hwd hw)
      · subst w; exact hyS
    · rw [c.support b w hwA, LinearMap.range_zero]; exact bot_le
  have hpS : LinearMap.range (r.component a p) ≤ S :=
    (c.other_image_le_pair hab hpaA.symm hpb).trans le_sup_left
  have hzS : LinearMap.range (r.component a z) ≤ S :=
    (c.other_image_le_pair hab hazA hzb).trans le_sup_left
  have haD := (c.high_dimensions hab).1
  have hbD := (c.high_dimensions hab).2.1
  have hdD := (c.high_dimensions hbd).2.1
  have hlinesA := c.third_image_line hpa hab hzp hzb hza haN
  have hlinesB := c.third_image_line hab hbd hya hyd hyb hbN
  let f : Fin 6 → V := ![a, b, d, p, z, y]
  let L : Fin 6 → Submodule K W := ![U a, U b, U d,
    LinearMap.range (r.component a p), LinearMap.range (r.component a z),
    LinearMap.range (r.component b y)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, habA.ne, hbdA.ne, hpaA.ne, Ne.symm]
  have hL : ∀ i, L i ≤ U (f i) ⊓ S := by
    intro i
    fin_cases i
    · exact le_inf le_rfl haS
    · exact le_inf le_rfl hbS
    · exact le_inf le_rfl hdS
    · exact le_inf (r.target a p) hpS
    · exact le_inf (r.target a z) hzS
    · exact le_inf (r.target b y) hyS
  have hmass : ∑ i, finrank K (L i) = 9 := by
    calc
      _ = ∑ i, (![2, 2, 2, 1, 1, 1] : Fin 6 → ℕ) i := by
        apply sum_congr rfl
        intro i _
        fin_cases i
        · exact haD
        · exact hbD
        · exact hdD
        · exact hlinesA.1
        · exact hlinesA.2
        · exact hlinesB.2
      _ = 9 := by decide
  have hdim : finrank K S ≤ 5 := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (U a) (U b)
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (U a ⊔ U b)
      (LinearMap.range (r.component b y))
    rw [haD, hbD] at h1
    rw [hlinesB.2] at h2
    change finrank K ((U a ⊔ U b) ⊔ LinearMap.range (r.component b y) : Submodule K W) ≤ 5
    omega
  have hS0 : S ≠ ⊥ := by
    intro h
    have hz : U a = ⊥ := le_bot_iff.mp (haS.trans_eq h)
    rw [hz, finrank_bot] at haD
    omega
  have hlo := family_mass_le U S f hf L hL
  have hbudget := c.mass_bound hS0
  rw [hmass] at hlo
  have hSdim : finrank K S = 5 := by omega
  obtain ⟨ht, he, hout⟩ := exact_finite_family U S (c.positive S hS0) f hf L hL
    (by rw [hmass, hSdim])
  refine ⟨hSdim, ht, he 0, he 1, he 2, he 3, he 4, he 5, ?_, ?_⟩
  · intro w hwa hwb hwd hwp hwz hwy
    apply hout w
    intro i
    fin_cases i <;> assumption
  · intro w hwa hwb hwd
    by_cases hwp : w = p
    · subst w
      rw [show U p ⊓ S = LinearMap.range (r.component a p) from he 3, hlinesA.1]
    by_cases hwz : w = z
    · subst w
      rw [show U z ⊓ S = LinearMap.range (r.component a z) from he 4, hlinesA.2]
    by_cases hwy : w = y
    · subst w
      rw [show U y ⊓ S = LinearMap.range (r.component b y) from he 5, hlinesB.2]
    · have hz : U w ⊓ S = ⊥ := hout w (fun i => by fin_cases i <;> assumption)
      rw [hz, finrank_bot]
      omega

end SubcubicMemo.LowRank
