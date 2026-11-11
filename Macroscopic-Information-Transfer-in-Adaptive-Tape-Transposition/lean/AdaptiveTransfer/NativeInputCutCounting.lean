import AdaptiveTransfer.NativeInputCut
import AdaptiveTransfer.FragmentMenuCount

/-! Exact finite counting for original adaptive input cuts. The complete
record and exterior are extracted from each actual successful run; the
pairwise replay injection is proved before the finite fibre sum. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset BoundedNesting NativeRelations
open scoped BigOperators

namespace FragmentObservation

theorem omitted_eq_of_record_heq {M : TM} {P T : ℕ} {X Y : Fin P → Bool}
    {B B' : Finset ℕ} (g : FragmentObservation M P T X B) (h : FragmentObservation M P T Y B')
    (hB : B = B') (he : HEq g.encode h.encode) (π : Fin P → Fin P) :
    g.omitted π = h.omitted π := by
  subst B'
  exact encode_omitted (eq_of_heq he) π

theorem input_eq_of_record_heq {M : TM} {P T : ℕ} {X Y : Fin P → Bool}
    {B B' : Finset ℕ} (g : FragmentObservation M P T X B) (h : FragmentObservation M P T Y B')
    (hB : B = B') (he : HEq g.encode h.encode) (π : Fin P → Fin P)
    (hpg : g.Parents) (hph : h.Parents)
    (hgout : (run M (List.ofFn X) g.finish).outRev.reverse = List.ofFn (fun j => X (π j)))
    (hhout : (run M (List.ofFn Y) h.finish).outRev.reverse = List.ofFn (fun j => Y (π j)))
    (hext : ∀ p ∉ g.omitted π, X p = Y p) : X = Y := by
  subst B'
  exact record_recovers_input g h π hpg hph hgout hhout (eq_of_heq he) hext

end FragmentObservation

namespace NativeInputCutWitness
variable {M : TM} {P T r : ℕ} {π : Equiv.Perm (Fin P)} {X Y : Fin P → Bool}

noncomputable def encode (g : NativeInputCutWitness M P T π X) (hr : g.cut.card ≤ r) :
    TotalFragmentRecord M P T r :=
  ⟨⟨g.cut, mem_filter.mpr ⟨mem_powerset.mpr (fun t ht =>
    mem_range.mpr ((g.cut_lt t ht).trans_le g.finish_le)), hr⟩⟩, g.fragment.encode⟩

theorem encode_fields {g : NativeInputCutWitness M P T π X} {h : NativeInputCutWitness M P T π Y}
    {hg : g.cut.card ≤ r} {hh : h.cut.card ≤ r} (he : g.encode hg = h.encode hh) :
    g.cut = h.cut ∧ HEq g.fragment.encode h.fragment.encode := by
  have hx := Sigma.mk.inj_iff.mp he
  exact ⟨congrArg Subtype.val hx.1, hx.2⟩

theorem encode_omitted {g : NativeInputCutWitness M P T π X} {h : NativeInputCutWitness M P T π Y}
    {hg : g.cut.card ≤ r} {hh : h.cut.card ≤ r} (he : g.encode hg = h.encode hh) :
    g.fragment.omitted π = h.fragment.omitted π :=
  FragmentObservation.omitted_eq_of_record_heq g.fragment h.fragment (encode_fields he).1
    (encode_fields he).2 π

theorem encode_input_eq {g : NativeInputCutWitness M P T π X} {h : NativeInputCutWitness M P T π Y}
    {hg : g.cut.card ≤ r} {hh : h.cut.card ≤ r} (he : g.encode hg = h.encode hh)
    (hext : ∀ p ∉ g.fragment.omitted π, X p = Y p) : X = Y :=
  FragmentObservation.input_eq_of_record_heq g.fragment h.fragment (encode_fields he).1
    (encode_fields he).2 π g.fragment_parents h.fragment_parents g.output h.output hext

end NativeInputCutWitness

/-- The exact finite adaptive input-cut bound for arbitrary actual bounded
successful executions of a fixed output permutation. Desired/read sets and
separators vary freely with the input and are never included in the message. -/
theorem native_input_cut_bound {M : TM} {P T r q a : ℕ} (π : Equiv.Perm (Fin P)) (D : ℝ)
    (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a)
    (C : Finset (Fin P → Bool)) (witness : ∀ X : C, NativeInputCutWitness M P T π X.val)
    (hdesired : ∀ X : C, D ≤ ((witness X).desired.card : ℝ))
    (hcut : ∀ X : C, (witness X).cut.card ≤ r) :
    (C.card : ℝ) ≤ (2 : ℝ) ^ ((P : ℝ) - D) *
      (∑ s ∈ range (min r T + 1), globalGeometryMenuSize M.k P T s * 2 ^ ((q + M.k * a + 2) * s) : ℕ) := by
  classical
  let R := TotalFragmentRecord M P T r
  let code (X : C) : R := (witness X).encode (hcut X)
  let cost : ℝ := (2 : ℝ) ^ ((P : ℝ) - D)
  have hfibre (σ : R) : (((univ : Finset C).filter fun X => code X = σ).card : ℝ) ≤ cost := by
    let F : Finset C := univ.filter fun X => code X = σ
    rcases F.eq_empty_or_nonempty with hemp | hne
    · change (F.card : ℝ) ≤ cost
      rw [hemp, card_empty, Nat.cast_zero]
      positivity
    let X₀ : F := ⟨hne.choose, hne.choose_spec⟩
    let W := (witness X₀.val).fragment.omitted π
    let exterior (X : F) : ↑Wᶜ → Bool := fun p => X.val.val p.val
    have hagree (X Y : F) : code X.val = code Y.val :=
      (mem_filter.mp X.property).2.trans (mem_filter.mp Y.property).2.symm
    have hW (X : F) : (witness X.val).fragment.omitted π = W :=
      NativeInputCutWitness.encode_omitted (hagree X X₀)
    have hinj : Function.Injective exterior := by
      intro X Y he
      apply Subtype.ext
      apply Subtype.ext
      apply NativeInputCutWitness.encode_input_eq (hagree X Y)
      intro p hp
      have hpW : p ∈ Wᶜ := mem_compl.mpr (by simpa only [hW X] using hp)
      exact congrFun he ⟨p, hpW⟩
    have hcard : F.card ≤ 2 ^ (P - W.card) := by
      have hh := Fintype.card_le_of_injective exterior hinj
      simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, card_compl,
        Fintype.card_fin] using hh
    have hWP : W.card ≤ P := by simpa only [Fintype.card_fin] using card_le_univ W
    have hDW : D ≤ (W.card : ℝ) :=
      (hdesired X₀.val).trans (by exact_mod_cast card_le_card (witness X₀.val).desired_subset_omitted)
    have hh : (F.card : ℝ) ≤ (2 : ℝ) ^ (P - W.card) := by exact_mod_cast hcard
    rw [← Real.rpow_natCast, Nat.cast_sub hWP] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have htotal : C.card = ∑ σ : R, ((univ : Finset C).filter fun X => code X = σ).card := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset C))
      (f := code) (t := (univ : Finset R)) (fun _ _ => mem_univ _)
    simpa only [card_univ, Fintype.card_coe] using hh
  have hbound : (C.card : ℝ) ≤ (Fintype.card R : ℝ) * cost := by
    rw [htotal, Nat.cast_sum]
    calc
      _ ≤ ∑ _σ : R, cost := sum_le_sum (fun σ _ => hfibre σ)
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]
  have hmenu : (Fintype.card R : ℝ) ≤
      (∑ s ∈ range (min r T + 1), globalGeometryMenuSize M.k P T s * 2 ^ ((q + M.k * a + 2) * s) : ℕ) := by
    exact_mod_cast totalFragmentRecord_card_le M P T r q a hq ha
  exact hbound.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmenu (by positivity : 0 ≤ cost))

end AdaptiveTransfer
