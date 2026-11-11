import AdaptiveTransfer.PersistenceSelection
import AdaptiveTransfer.PersistenceWholeWord

/-! A common retained law for all selected whole native tape words and all
times in the selected interval. This composes actual catalogue escape,
finite weighted selection and conditional top-set pruning. -/

namespace AdaptiveTransfer.PersistenceSelection

open Transpose Transpose.Tape LeanMachine Finset
open PersistenceGraph PersistenceCatalogues FiniteTimeGrid FiniteObservationTopSets
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

theorem exists_common_interval_atoms (M : TM) (input : Ω → List Bool)
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hprob : ∑ x, w x = 1)
    (T K R m : ℕ) (hK : 1 ≤ K) (hR : 2 ≤ R)
    (limit : Ω → ℕ) (B : Finset Ω) (hp : 0 < ContextPruning.mass w B)
    (hlimit : ∀ x ∈ B, limit x ≤ T)
    (hescape : ∀ x ∈ B, ∃ t ≤ limit x, ∃ H : Finset (Fin M.k), H.card = m ∧
      ∀ h ∈ H, vertex M (input x) T t h ∉
        catalogue (nativeTop M input w T K h) t R
          (PrefixOutput.word (outBit M (input x)) t)) :
    ∃ H : Finset (Fin M.k), H.card = m ∧ ∃ j < T / (R / 2) + 1,
      ∃ D ⊆ B,
        ContextPruning.mass w B /
          (2 * (M.k.choose m * (T / (R / 2) + 1) : ℕ)) ≤ ContextPruning.mass w D ∧
        (∀ x ∈ D, ∀ h ∈ H, ∀ u ∈ interval (R / 2) j,
          u < limit x ∧ vertex M (input x) T u h ∉ nativeTop M input w T K h u
            (PrefixOutput.word (outBit M (input x)) u)) ∧
        ∀ h ∈ H, ∀ u ∈ interval (R / 2) j, ∀ z v,
          0 < ContextPruning.mass w (D ∩ ContextPruning.fibre
            (fun x => PrefixOutput.word (outBit M (input x)) u) z) →
          atom (fun x => if x ∈ D then w x else 0)
              (fun x => PrefixOutput.word (outBit M (input x)) u)
              (fun x => (run M (input x) u).work h) z v /
            ContextPruning.mass w (D ∩ ContextPruning.fibre
              (fun x => PrefixOutput.word (outBit M (input x)) u) z) ≤
            2 * (2 * T + 1 : ℕ) * (R / 2 : ℕ) *
              (M.k.choose m * (T / (R / 2) + 1) : ℕ) /
              ((K + 1) * ContextPruning.mass w B) := by
  classical
  obtain ⟨H, hH, j, hj, E, hEB, hmass, havoid⟩ :=
    exists_fixed_escape_interval M input w hw hprob T K R m hK hR limit B hp hlimit hescape
  let L := M.k.choose m * (T / (R / 2) + 1)
  have hmk : m ≤ M.k := by
    simpa only [hH, Fintype.card_fin] using card_le_univ H
  have hL : (0 : ℝ) < L := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hmk) (Nat.succ_pos _)
  have hEp : 0 < ContextPruning.mass w E := (div_pos hp hL).trans_le hmass
  let I := ↑(interval (R / 2) j)
  have hI : Nonempty I := by
    have hh : 0 < (interval (R / 2) j).card := by rw [card_interval]; omega
    obtain ⟨u, hu⟩ := card_pos.mp hh
    exact ⟨⟨u, hu⟩⟩
  let : Nonempty I := hI
  let z (i : I) (x : Ω) := PrefixOutput.word (outBit M (input x)) i.val
  let f (h : H) (i : I) (x : Ω) := vertex M (input x) T i.val h.val
  let g (_h : H) (_i : I) (v : FiniteTapeGraph.Vertex (Fin (M.g + 1)) (2 * T + 1)) :=
    extendWord (0 : Fin (M.g + 1)) T v.1
  obtain ⟨D, hDE, hDmass, hbound⟩ := exists_half_mass_avoid_top w hw
    (show ContextPruning.mass w univ = 1 from hprob) z f g E hEp K (2 * T + 1)
    (fun _h _i v => whole_word_fibre 0 T v)
    (fun h i x hx => (havoid x hx h.val h.property i.val i.property).2)
  have hDB := hDE.trans hEB
  refine ⟨H, hH, j, hj, D, hDB, ?_, ?_, ?_⟩
  · change ContextPruning.mass w B / (2 * (L : ℝ)) ≤ _
    calc
      _ = (ContextPruning.mass w B / L) / 2 := by ring
      _ ≤ ContextPruning.mass w E / 2 := div_le_div_of_nonneg_right hmass (by norm_num)
      _ ≤ _ := hDmass
  · exact fun x hx h hh u hu => havoid x (hDE hx) h hh u hu
  · intro h hh u hu a v hden
    have hb := hbound ⟨h, hh⟩ ⟨u, hu⟩ a v hden
    have heq : atom (fun x => if x ∈ D then w x else 0) (z ⟨u, hu⟩)
        (fun x => (run M (input x) u).work h) a v =
        atom (fun x => if x ∈ D then w x else 0) (z ⟨u, hu⟩)
          (g ⟨h, hh⟩ ⟨u, hu⟩ ∘ f ⟨h, hh⟩ ⟨u, hu⟩) a v := by
      unfold atom
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ D
      · have htime := (havoid x (hDE hx) h hh u hu).1.le.trans (hlimit x (hDB hx))
        have hwhole := extendWord_vertex M (input x) h htime
        dsimp only [Function.comp_apply, g, f]
        simp only [hwhole]
        split_ifs <;> rfl
      · simp only [hx, ite_false, ite_self]
    rw [← heq] at hb
    have hcardI : Fintype.card I = R / 2 := by
      change Fintype.card ↑(interval (R / 2) j) = _
      rw [Fintype.card_coe, card_interval]
    rw [hcardI] at hb
    apply hb.trans
    have hKE : 0 < (K + 1 : ℝ) * ContextPruning.mass w E := by positivity
    have hKB : 0 < (K + 1 : ℝ) * ContextPruning.mass w B := by positivity
    apply (div_le_div_iff₀ hKE hKB).mpr
    have hpE : ContextPruning.mass w B ≤ (L : ℝ) * ContextPruning.mass w E := by
      have he := (div_le_iff₀ hL).mp hmass
      simpa only [mul_comm] using he
    have hn : 0 ≤ 2 * (2 * T + 1 : ℕ) * (R / 2 : ℕ) * (K + 1 : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hpE hn
    convert hmul using 1 <;> ring

end AdaptiveTransfer.PersistenceSelection
