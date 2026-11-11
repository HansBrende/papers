import SharedDecoders.CapacityIntervalsSource

/-!
# Arbitrary-partition construction and exact interval capacity

Surjectivity means that all declared receiver classes are nonempty. Pairing the
complement of a representative transversal is an actual finite equivalence,
not an extra construction hypothesis. The interval upper bound uses the literal
condition that every class boundary is in that transversal.
-/

namespace SharedDecoders.CapacityIntervals

open Module

variable {d b : ℕ} [NeZero d] {κ : Type*} [Fintype κ]

theorem exists_paired_layout (p : ZMod d → κ) (hp : Function.Surjective p)
    (heven : Even (d - Fintype.card κ)) :
    ∃ k : ℕ, ∃ layout : κ ⊕ (Fin k × Bool) ≃ ZMod d,
      (∀ a, p (layout (Sum.inl a)) = a) ∧ d = Fintype.card κ + 2 * k := by
  classical
  let r : κ → ZMod d := fun a => (hp a).choose
  have hr : ∀ a, p (r a) = a := fun a => (hp a).choose_spec
  have hinj : Function.Injective r := by
    intro a a' h
    simpa only [hr] using congrArg p h
  have hle : Fintype.card κ ≤ d := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective r hinj
  obtain ⟨k, hk⟩ := heven
  have hsize : d = Fintype.card κ + 2 * k := by omega
  let U : Set (ZMod d) := Set.range r
  let e₀ : κ ≃ U := Equiv.ofInjective r hinj
  have hU : Fintype.card U = Fintype.card κ := (Fintype.card_congr e₀).symm
  have hcompl : Fintype.card (↑(Uᶜ)) = 2 * k := by
    change Fintype.card {x : ZMod d // ¬x ∈ U} = _
    rw [Fintype.card_subtype_compl, ZMod.card, hU]
    omega
  let e₁ : (Fin k × Bool) ≃ ↑(Uᶜ) := Fintype.equivOfCardEq (by simp [hcompl, mul_comm])
  let layout : κ ⊕ (Fin k × Bool) ≃ ZMod d :=
    (Equiv.sumCongr e₀ e₁).trans (Equiv.Set.sumCompl U)
  refine ⟨k, layout, ?_, hsize⟩
  intro a
  simp only [layout, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl, e₀]
  exact (congrArg (fun z : Set.range r => p z) (Equiv.ofInjective_apply r hinj a)).trans (hr a)

/-- The actual all-width binary construction for every partition of the admitted
parity. Only the decoder functions, not the source subspace, need be nonlinear. -/
theorem exists_binary_code (p : ZMod d → κ) (hp : Function.Surjective p)
    (heven : Even (d - Fintype.card κ)) :
    ∃ C : Submodule Bit (State d (Fin b → Bit)), IsSharedCode Bit p C ∧
      2 * finrank Bit C = b * (d * d + Fintype.card κ * d) := by
  obtain ⟨k, layout, hr, hd⟩ := exists_paired_layout p hp heven
  obtain ⟨C, hC, hdim⟩ := paired_completion (b := b) p layout hr
  refine ⟨C, hC, ?_⟩
  simp only [Fintype.card_fin] at hdim
  rw [hdim, hd]
  ring

theorem exists_binary_code_dimension (p : ZMod d → κ) (hp : Function.Surjective p)
    (heven : Even (d - Fintype.card κ)) :
    ∃ C : Submodule Bit (State d (Fin b → Bit)), IsSharedCode Bit p C ∧
      finrank Bit C = b * (d * d + Fintype.card κ * d) / 2 := by
  obtain ⟨C, hC, hdim⟩ := exists_binary_code (b := b) p hp heven
  exact ⟨C, hC, by omega⟩

end SharedDecoders.CapacityIntervals

namespace SharedDecoders

open Module Finset

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A] {d : ℕ} [NeZero d]

/-- Every literal cyclic class boundary is selected. This condition is satisfied
by choosing one start per nonempty cyclic interval (one arbitrary row if constant). -/
theorem IsSharedCode.two_mul_finrank_le_boundaries {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    {S : Finset (ZMod d)} (hS : S.Nonempty)
    (hboundary : ∀ c ∉ S, p (c - 1) = p c) :
    2 * finrank F C ≤ d * d * finrank F A + d * S.card * finrank F A := by
  classical
  have hlink : ∀ c ∉ S, Link p {0, 1} (c - 1) c :=
    fun c hc => ⟨hboundary c hc, 1, by simp, 0, by simp, by simp⟩
  have hwalk : ∀ k : ℕ, ∀ c : ZMod d, c - (k : ZMod d) ∈ S →
      ∃ e ∈ S, Relation.EqvGen (Link p {0, 1}) c e := by
    intro k
    induction k with
    | zero =>
      intro c hc
      exact ⟨c, by simpa using hc, Relation.EqvGen.refl _⟩
    | succ k ih =>
      intro c hc
      by_cases hcS : c ∈ S
      · exact ⟨c, hcS, Relation.EqvGen.refl _⟩
      · have hc' : c - 1 - (k : ZMod d) ∈ S := by
          convert hc using 1
          push_cast
          ring
        obtain ⟨e, he, hrel⟩ := ih (c - 1) hc'
        exact ⟨e, he, Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hlink c hcS))) hrel⟩
  have hconn : ∀ c, ∃ e ∈ S, Relation.EqvGen (Link p {0, 1}) c e := by
    intro c
    obtain ⟨e, he⟩ := hS
    apply hwalk (c - e).val c
    simpa only [ZMod.natCast_zmod_val, sub_sub_cancel] using he
  have hh := h.finrank_le (Δ := {0, 1}) (Finset.insert_nonempty _ _) hconn
  by_cases h01 : (0 : ZMod d) = 1
  · have hdim : finrank F C ≤ d * d * finrank F A := by
      simpa only [finrank_state] using C.finrank_le
    rw [← h01, Finset.pair_eq_singleton, Finset.card_singleton] at hh
    simp only [one_mul, Nat.sub_self, zero_mul, zero_add] at hh
    omega
  · rw [Finset.card_pair h01] at hh
    simp only [Nat.reduceSub, one_mul] at hh
    exact hh

variable [Fintype κ]

theorem IsSharedCode.two_mul_finrank_le_interval {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C)
    (r : κ → ZMod d) (hr : ∀ a, p (r a) = a)
    (hinterval : ∀ c, p (c - 1) ≠ p c → c ∈ Set.range r) :
    2 * finrank F C ≤ d * d * finrank F A + Fintype.card κ * d * finrank F A := by
  classical
  let S := univ.image r
  have hS : S.Nonempty := ⟨r (p 0), mem_image_of_mem r (mem_univ _)⟩
  have hinj : Function.Injective r := by
    intro a b he
    simpa only [hr] using congrArg p he
  have hcard : S.card = Fintype.card κ := by simp [S, card_image_of_injective _ hinj]
  have hh := h.two_mul_finrank_le_boundaries hS (fun c hc => by
    by_contra hn
    obtain ⟨a, ha⟩ := hinterval c hn
    exact hc (mem_image.mpr ⟨a, mem_univ _, ha⟩))
  simpa only [hcard, mul_comm, mul_left_comm, mul_assoc] using hh

end SharedDecoders

namespace SharedDecoders.CapacityIntervals

open Module

variable {d b : ℕ} [NeZero d] {κ : Type*} [Fintype κ]

/-- Exact deterministic capacity for interval classes, with every lane included. -/
theorem exists_optimal_interval_code (p : ZMod d → κ) (r : κ → ZMod d)
    (hr : ∀ a, p (r a) = a)
    (hinterval : ∀ c, p (c - 1) ≠ p c → c ∈ Set.range r)
    (heven : Even (d - Fintype.card κ)) :
    ∃ C : Submodule Bit (State d (Fin b → Bit)), IsSharedCode Bit p C ∧
      finrank Bit C = b * (d * d + Fintype.card κ * d) / 2 ∧
      ∀ C' : Submodule Bit (State d (Fin b → Bit)), IsSharedCode Bit p C' →
        finrank Bit C' ≤ finrank Bit C := by
  have hp : Function.Surjective p := fun a => ⟨r a, hr a⟩
  obtain ⟨C, hC, hdim⟩ := exists_binary_code (b := b) p hp heven
  refine ⟨C, hC, by omega, ?_⟩
  intro C' hC'
  have hh := hC'.two_mul_finrank_le_interval r hr hinterval
  have hlanes : finrank Bit (Fin b → Bit) = b := by simp
  rw [hlanes] at hh
  nlinarith

end SharedDecoders.CapacityIntervals
