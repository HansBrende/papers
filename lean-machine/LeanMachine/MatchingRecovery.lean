import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import LeanMachine.InvolutionCompletion
import LeanMachine.MatchingSeed

/-!
# Nonlinear recovery from a matching and one extra helper

A transversal meeting every extra-helper trap determines the whole word.
This argument compares two words directly; it needs no iteration or
chosen order of recovery, and allows arbitrary fixed boundary records.
-/

namespace LeanMachine.MatchingRecovery

open Finset

variable {V Ω A H : Type*} [Fintype V] [DecidableEq V]

/-- Agreement on a seed set meeting all extra-helper traps implies agreement
everywhere when the matching partner of every unseeded coordinate is known.
The matching map need not be an involution for this implication. -/
theorem eq_of_seed (m : V → V) (f : V → Finset V) (S : Finset V)
    (hmate : ∀ v, v ∉ S → m v ≠ v → m v ∈ S)
    (htrap : ∀ D : Finset V, D.Nonempty →
      (∀ v ∈ D, (f v ∩ D).Nonempty) → (S ∩ D).Nonempty)
    (X : Ω → V → A) (Z : Ω → H)
    (hlocal : ∀ v x y, Z x = Z y →
      (m v ≠ v → X x (m v) = X y (m v)) →
      (∀ u ∈ f v, X x u = X y u) → X x v = X y v)
    {x y : Ω} (hZ : Z x = Z y)
    (hS : ∀ v ∈ S, X x v = X y v) : X x = X y := by
  classical
  let D : Finset V := univ.filter (fun v => X x v ≠ X y v)
  have hD (v : V) : v ∈ D ↔ X x v ≠ X y v := by simp [D]
  have hout : ∀ v ∈ D, v ∉ S := by
    intro v hv hs
    exact (hD v).mp hv (hS v hs)
  have hclosed : ∀ v ∈ D, (f v ∩ D).Nonempty := by
    intro v hv
    by_contra hn
    apply (hD v).mp hv
    apply hlocal v x y hZ
    · intro hm
      exact hS (m v) (hmate v (hout v hv) hm)
    · intro u hu
      by_contra hne
      exact hn ⟨u, mem_inter.mpr ⟨hu, (hD u).mpr hne⟩⟩
  have hempty : D = ∅ := by
    by_contra hn
    obtain ⟨v, hv⟩ := htrap D (nonempty_iff_ne_empty.mpr hn) hclosed
    exact hout v (mem_inter.mp hv).2 (mem_inter.mp hv).1
  funext v
  by_contra hne
  have hv := (hD v).mpr hne
  simp [hempty] at hv

/-- A partial matching and a loopless extra helper admit a half-size seed
set chosen from the support alone. Fixed points of `m` are unmatched, not
self-helpers. Every nonempty extra-helper trap meets it: a trap requires
each of its vertices to have an extra helper inside the set. -/
theorem exists_seed (m : V → V) (hm : Function.Involutive m)
    (f : V → Finset V) (hf : ∀ v, (f v).card ≤ 1) (hself : ∀ v, v ∉ f v) :
    ∃ S : Finset V, S.card = Fintype.card V / 2 ∧
      (∀ v, v ∉ S → m v ≠ v → m v ∈ S) ∧
      ∀ D : Finset V, D.Nonempty → (∀ v ∈ D, (f v ∩ D).Nonempty) →
        (S ∩ D).Nonempty := by
  classical
  by_cases heven : Even (Fintype.card V)
  · obtain ⟨p, hp, hpf, hpm⟩ :=
      InvolutionCompletion.exists_fixedPointFree_extension m hm heven
    cases isEmpty_or_nonempty V with
    | inl h =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · intro v; exact isEmptyElim v
      · intro D hD
        obtain ⟨v, _⟩ := hD
        exact isEmptyElim v
    | inr h =>
      obtain ⟨S, hcard, -, hpair, htrap⟩ :=
        MatchingSeed.exists_seed p hp hpf f hf hself (Classical.choice h)
      refine ⟨S, by omega, ?_, ?_⟩
      · intro v hv hmv
        have hpv : p v ∈ S := by
          by_contra hn
          exact hv ((hpair v).mpr hn)
        rwa [hpm v hmv] at hpv
      · intro D hD hc
        exact htrap D ⟨hD, hc⟩
  · let m' : Option V → Option V := Option.map m
    have hm' : Function.Involutive m' := by
      intro v
      cases v with
      | none => rfl
      | some v => simpa only [m', Option.map_some] using congrArg some (hm v)
    have heven' : Even (Fintype.card (Option V)) := by
      rw [Fintype.card_option, Nat.even_add_one]
      exact heven
    obtain ⟨p, hp, hpf, hpm⟩ :=
      InvolutionCompletion.exists_fixedPointFree_extension m' hm' heven'
    let f' : Option V → Finset (Option V) := fun v =>
      match v with
      | none => ∅
      | some v => (f v).map Function.Embedding.some
    have hf' : ∀ v, (f' v).card ≤ 1 := by
      intro v
      cases v with
      | none => simp [f']
      | some v => simpa [f'] using hf v
    have hself' : ∀ v, v ∉ f' v := by
      intro v
      cases v with
      | none => simp [f']
      | some v => simpa [f'] using hself v
    obtain ⟨S, hcard, hnone, hpair, htrap⟩ :=
      MatchingSeed.exists_seed p hp hpf f' hf' hself' none
    refine ⟨S.eraseNone, ?_, ?_, ?_⟩
    · rw [card_eraseNone_of_mem hnone]
      rw [Fintype.card_option] at hcard
      omega
    · intro v hv hmv
      have hpv : p (some v) ∈ S := by
        by_contra hn
        exact hv (mem_eraseNone.mpr ((hpair (some v)).mpr hn))
      have hneq : m' (some v) ≠ some v := by simpa [m'] using hmv
      rw [hpm (some v) hneq] at hpv
      exact mem_eraseNone.mpr hpv
    · intro D hD hc
      let D' := D.map Function.Embedding.some
      have hD' : MatchingSeed.IsTrap f' D' := by
        refine ⟨?_, ?_⟩
        · obtain ⟨v, hv⟩ := hD
          exact ⟨some v, by simpa [D'] using hv⟩
        · intro v hv
          obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
          obtain ⟨z, hz⟩ := hc u hu
          refine ⟨some z, mem_inter.mpr ⟨?_, ?_⟩⟩
          · simpa [f'] using (mem_inter.mp hz).1
          · simpa [D'] using (mem_inter.mp hz).2
      obtain ⟨v, hv⟩ := htrap D' hD'
      obtain ⟨u, hu, rfl⟩ := mem_map.mp (mem_inter.mp hv).2
      exact ⟨u, mem_inter.mpr ⟨mem_eraseNone.mpr (mem_inter.mp hv).1, hu⟩⟩

/-- The same half-size coordinate set determines every word together with
its boundary record. Recovery may be nonlinear and the record correlated. -/
theorem exists_determining_seed (m : V → V) (hm : Function.Involutive m)
    (f : V → Finset V) (hf : ∀ v, (f v).card ≤ 1) (hself : ∀ v, v ∉ f v)
    (X : Ω → V → A) (Z : Ω → H)
    (hlocal : ∀ v x y, Z x = Z y →
      (m v ≠ v → X x (m v) = X y (m v)) →
      (∀ u ∈ f v, X x u = X y u) → X x v = X y v) :
    ∃ S : Finset V, S.card = Fintype.card V / 2 ∧
      ∀ x y, Z x = Z y → (∀ v ∈ S, X x v = X y v) → X x = X y := by
  obtain ⟨S, hsize, hmate, htrap⟩ := exists_seed m hm f hf hself
  exact ⟨S, hsize, fun _ _ hZ hS => eq_of_seed m f S hmate htrap X Z hlocal hZ hS⟩

/-- A varying boundary record is charged by its attained range, not by an
ambient record alphabet. No nonempty-alphabet hypothesis is needed. -/
theorem card_code_le_record [Fintype A] (C : Set (V → A))
    (m : V → V) (hm : Function.Involutive m)
    (f : V → Finset V) (hf : ∀ v, (f v).card ≤ 1) (hself : ∀ v, v ∉ f v)
    (Z : C → H)
    (hlocal : ∀ v (x y : C), Z x = Z y →
      (m v ≠ v → x.val (m v) = y.val (m v)) →
      (∀ u ∈ f v, x.val u = y.val u) → x.val v = y.val v) :
    Nat.card C ≤ Nat.card (Set.range Z) * Fintype.card A ^ (Fintype.card V / 2) := by
  classical
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (Set.range Z) := Fintype.ofFinite (Set.range Z)
  obtain ⟨S, hsize, hgen⟩ := exists_determining_seed m hm f hf hself
    (fun x : C => x.val) Z hlocal
  let obs : C → Set.range Z × (S → A) :=
    fun x => (⟨Z x, ⟨x, rfl⟩⟩, fun v => x.val v)
  have hinj : Function.Injective obs := by
    intro x y hxy
    apply Subtype.ext
    apply hgen x y
    · exact congrArg (fun r : Set.range Z × (S → A) => r.1.val) hxy
    · intro v hv
      exact congrFun (congrArg Prod.snd hxy) ⟨v, hv⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe, hsize] using Fintype.card_le_of_injective obs hinj

/-- A matching plus one loopless extra helper gives at most `q^floor(N/2)`
codewords over every finite alphabet, with arbitrary nonlinear recovery. -/
theorem card_code_le [Fintype A] (C : Set (V → A))
    (m : V → V) (hm : Function.Involutive m)
    (f : V → Finset V) (hf : ∀ v, (f v).card ≤ 1) (hself : ∀ v, v ∉ f v)
    (hlocal : ∀ v (x y : C),
      (m v ≠ v → x.val (m v) = y.val (m v)) →
      (∀ u ∈ f v, x.val u = y.val u) → x.val v = y.val v) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card V / 2) := by
  classical
  let Z : C → Unit := fun _ => ()
  have hc := card_code_le_record C m hm f hf hself Z (fun v x y _ => hlocal v x y)
  let : Fintype (Set.range Z) := Fintype.ofFinite (Set.range Z)
  have hr : Nat.card (Set.range Z) ≤ 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_punit] using
      Fintype.card_le_of_injective (Subtype.val : Set.range Z → Unit) Subtype.val_injective
  exact hc.trans (by simpa only [one_mul] using
    (Nat.mul_le_mul_right (Fintype.card A ^ (Fintype.card V / 2)) hr))

end LeanMachine.MatchingRecovery

#print axioms LeanMachine.MatchingRecovery.eq_of_seed
#print axioms LeanMachine.MatchingRecovery.exists_seed
#print axioms LeanMachine.MatchingRecovery.exists_determining_seed
#print axioms LeanMachine.MatchingRecovery.card_code_le_record
#print axioms LeanMachine.MatchingRecovery.card_code_le
