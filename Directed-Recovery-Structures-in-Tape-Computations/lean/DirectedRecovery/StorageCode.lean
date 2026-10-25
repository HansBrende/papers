import MotionDepthCodes.StorageCode

/-!
# Directed storage codes and index-code fibres

The storage-code predicate is imported unchanged from the fourth paper.
An index code sends one common message; equality of that message and of the
side-information symbols must determine each requested symbol. Its fibres
are therefore storage codes. Finite counting transfers any real exponential
bound on binary storage-code size to the same lower bound on broadcast length.
-/

namespace DirectedRecovery

open Finset MotionDepthCodes
open scoped BigOperators
set_option autoImplicit false

variable {V α β : Type*} [DecidableEq V]

/-- A common-message index code for the directed side-information relation `N`.
The alphabet of messages need not be binary. -/
def IsIndexCode (N : V → Finset V) (G : (V → α) → β) : Prop :=
  ∀ x y, G x = G y → ∀ v, (∀ u ∈ N v, x u = y u) → x v = y v

variable [Fintype V] [Fintype α]

/-- The fibre of a common-message encoder, as a finite set of source words. -/
noncomputable def indexFiber (G : (V → α) → β) (z : β) : Finset (V → α) :=
  by classical exact Finset.univ.filter (fun x => G x = z)

@[simp] theorem mem_indexFiber (G : (V → α) → β) (z : β) (x : V → α) :
    x ∈ indexFiber G z ↔ G x = z := by
  classical
  simp [indexFiber]

/-- Every fibre of an index code is a storage code for the same relation. -/
theorem isStorageCode_indexFiber {N : V → Finset V} {G : (V → α) → β}
    (hG : IsIndexCode N G) (z : β) : IsStorageCode N (indexFiber G z) := by
  intro x hx y hy v hxy
  exact hG x y ((mem_indexFiber G z x).mp hx |>.trans
    ((mem_indexFiber G z y).mp hy).symm) v hxy

/-- Fibre counting with an arbitrary real upper bound on storage-code size.
No positivity hypothesis on the bound is needed. -/
theorem indexCode_card_le [Fintype β] {N : V → Finset V} {G : (V → α) → β}
    (hG : IsIndexCode N G) {R : ℝ}
    (hR : ∀ C : Finset (V → α), IsStorageCode N C → (C.card : ℝ) ≤ R) :
    (Fintype.card α : ℝ) ^ Fintype.card V ≤ (Fintype.card β : ℝ) * R := by
  classical
  have hcount : Fintype.card (V → α) = ∑ z : β, (indexFiber G z).card := by
    simpa [indexFiber] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (V → α))) (t := (Finset.univ : Finset β))
        (f := G) (fun _ _ => Finset.mem_univ _))
  have hcountR : (Fintype.card (V → α) : ℝ) =
      ∑ z : β, ((indexFiber G z).card : ℝ) := by
    exact_mod_cast hcount
  calc
    (Fintype.card α : ℝ) ^ Fintype.card V =
        (Fintype.card (V → α) : ℝ) := by simp
    _ = ∑ z : β, ((indexFiber G z).card : ℝ) := hcountR
    _ ≤ ∑ _z : β, R := Finset.sum_le_sum fun z _ =>
      hR (indexFiber G z) (isStorageCode_indexFiber hG z)
    _ = (Fintype.card β : ℝ) * R := by simp

/-- The exact real-exponent fibre bound: if every binary storage code has
at most `2 ^ (|V| - s)` words, every binary index code has length at least `s`.
The subtraction is in the reals, so no integrality or `s ≤ |V|` hypothesis
is imposed. -/
theorem indexCode_length_ge {N : V → Finset V} {m : ℕ}
    {G : (V → Bool) → (Fin m → Bool)} (hG : IsIndexCode N G) {s : ℝ}
    (hC : ∀ C : Finset (V → Bool), IsStorageCode N C →
      (C.card : ℝ) ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) - s)) :
    s ≤ (m : ℝ) := by
  have h := indexCode_card_le hG hC
  have hpow : (2 : ℝ) ^ (Fintype.card V : ℝ) ≤
      (2 : ℝ) ^ ((m : ℝ) + ((Fintype.card V : ℝ) - s)) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simpa only [Fintype.card_bool, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using h
  have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
  linarith

/-- The induced recovery relation on the retained coordinates `Q`. -/
def inducedNeighborhood (N : V → Finset V) (Q : Finset V) (q : Q) : Finset Q :=
  (N q).subtype (fun v => v ∈ Q)

/-- Restriction to the retained coordinates. -/
def restrictWord (Q : Finset V) (x : V → α) : Q → α := fun q => x q

/-- The coordinates that must be fixed before restricting to `Q`. -/
def outsideWord (Q : Finset V) (x : V → α) : {v // v ∉ Q} → α := fun v => x v

/-- A fibre of a storage code obtained by fixing all omitted coordinates,
then restricting to the retained coordinates. -/
noncomputable def conditionedCode (C : Finset (V → α)) (Q : Finset V)
    (z : {v // v ∉ Q} → α) : Finset (Q → α) := by
  classical
  exact (C.filter (fun x => outsideWord Q x = z)).image (restrictWord Q)

omit [Fintype α] in
/-- Conditioning, unlike unrestricted projection, preserves the storage
property for the induced recovery relation. This includes the empty fibre. -/
theorem isStorageCode_conditionedCode {N : V → Finset V} {C : Finset (V → α)}
    (hC : IsStorageCode N C) (Q : Finset V) (z : {v // v ∉ Q} → α) :
    IsStorageCode (inducedNeighborhood N Q) (conditionedCode C Q z) := by
  classical
  intro x hx y hy q hxy
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxC, hxz⟩ := Finset.mem_filter.mp hx₀
  obtain ⟨hyC, hyz⟩ := Finset.mem_filter.mp hy₀
  apply hC x₀ hxC y₀ hyC q
  intro v hv
  by_cases hvQ : v ∈ Q
  · exact hxy ⟨v, hvQ⟩ (by simpa [inducedNeighborhood] using hv)
  · exact congrFun (hxz.trans hyz.symm) ⟨v, hvQ⟩

omit [Fintype α] in
open Classical in
/-- Restriction is injective within a fibre with fixed omitted coordinates. -/
theorem conditionedCode_card (C : Finset (V → α)) (Q : Finset V)
    (z : {v // v ∉ Q} → α) :
    (conditionedCode C Q z).card = (C.filter (fun x => outsideWord Q x = z)).card := by
  classical
  unfold conditionedCode
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxz := (Finset.mem_filter.mp hx).2
  have hyz := (Finset.mem_filter.mp hy).2
  funext v
  by_cases hv : v ∈ Q
  · exact congrFun hxy ⟨v, hv⟩
  · exact congrFun (hxz.trans hyz.symm) ⟨v, hv⟩

/-- The cardinality cost of conditioning: one factor of the alphabet size
for each omitted coordinate, with an arbitrary real bound on each code
for the induced recovery relation. -/
theorem storageCode_conditioning_card_le {N : V → Finset V} {C : Finset (V → α)}
    (hC : IsStorageCode N C) (Q : Finset V) {R : ℝ}
    (hR : ∀ D : Finset (Q → α), IsStorageCode (inducedNeighborhood N Q) D →
      (D.card : ℝ) ≤ R) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ Fintype.card {v // v ∉ Q} * R := by
  classical
  have hcount : C.card = ∑ z : ({v // v ∉ Q} → α),
      (C.filter (fun x => outsideWord Q x = z)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := C) (t := (Finset.univ : Finset ({v // v ∉ Q} → α)))
      (f := outsideWord Q) (fun _ _ => Finset.mem_univ _))
  have hcountR : (C.card : ℝ) = ∑ z : ({v // v ∉ Q} → α),
      ((C.filter (fun x => outsideWord Q x = z)).card : ℝ) := by
    exact_mod_cast hcount
  calc
    (C.card : ℝ) = ∑ z : ({v // v ∉ Q} → α),
        ((C.filter (fun x => outsideWord Q x = z)).card : ℝ) := hcountR
    _ ≤ ∑ _z : ({v // v ∉ Q} → α), R := by
      apply Finset.sum_le_sum
      intro z _
      rw [← conditionedCode_card C Q z]
      exact hR (conditionedCode C Q z) (isStorageCode_conditionedCode hC Q z)
    _ = (Fintype.card α : ℝ) ^ Fintype.card {v // v ∉ Q} * R := by simp

/-- Paid conditioning in the exact exponential form used in the paper.
The alphabet is nonempty and the exponent `u` may be any real number. -/
theorem storageCode_conditioning_bound {N : V → Finset V} {C : Finset (V → α)}
    (hC : IsStorageCode N C) (Q : Finset V) (ha : 0 < (Fintype.card α : ℝ)) {u : ℝ}
    (hu : ∀ D : Finset (Q → α), IsStorageCode (inducedNeighborhood N Q) D →
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ u) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^ ((Fintype.card {v // v ∉ Q} : ℝ) + u) := by
  rw [Real.rpow_add ha, Real.rpow_natCast]
  exact storageCode_conditioning_card_le hC Q hu

/-- An independent coordinate set has no recovery incidence between its
members, including a self-incidence. -/
def IsIndependent (N : V → Finset V) (I : Finset V) : Prop :=
  ∀ q ∈ I, ∀ p ∈ N q, p ∉ I

omit [Fintype V] [Fintype α] in
/-- On a storage code, the coordinates outside an independent set determine
the entire word. -/
theorem independent_outside_injOn {N : V → Finset V} {I : Finset V}
    (hI : IsIndependent N I) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    Set.InjOn (outsideWord I) (C : Set (V → α)) := by
  intro x hx y hy hxy
  funext q
  by_cases hq : q ∈ I
  · apply hC x hx y hy q
    intro p hp
    exact congrFun hxy ⟨p, hI q hq p hp⟩
  · exact congrFun hxy ⟨q, hq⟩

/-- Independent coordinates bound every storage code, without linearity
or an extension assumption. -/
theorem storageCode_card_le_of_independent {N : V → Finset V} {I : Finset V}
    (hI : IsIndependent N I) {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ≤ Fintype.card α ^ (Fintype.card V - I.card) := by
  classical
  have h : C.card ≤ Fintype.card ({v // v ∉ I} → α) := by
    rw [← Finset.card_image_of_injOn (independent_outside_injOn hI hC)]
    exact Finset.card_le_univ _
  simpa using h

omit [Fintype V] in
/-- Independence passes to the induced relation on any retained set. -/
theorem isIndependent_induced {N : V → Finset V} {I : Finset V}
    (hI : IsIndependent N I) (Q : Finset V) :
    IsIndependent (inducedNeighborhood N Q) (I.subtype (fun v => v ∈ Q)) := by
  intro q hq p hp hpI
  exact hI q (Finset.mem_subtype.mp hq) p
    (Finset.mem_subtype.mp hp) (Finset.mem_subtype.mp hpI)

omit [Fintype V] in
/-- The exact induced-code bound: only independent coordinates retained
in `Q` are subtracted from the exponent. -/
theorem induced_storageCode_card_le_of_independent {N : V → Finset V} {I : Finset V}
    (hI : IsIndependent N I) (Q : Finset V) {C : Finset (Q → α)}
    (hC : IsStorageCode (inducedNeighborhood N Q) C) :
    C.card ≤ Fintype.card α ^ (Q.card - (I ∩ Q).card) := by
  have h := storageCode_card_le_of_independent (isIndependent_induced hI Q) hC
  simpa [Finset.card_subtype, Finset.filter_mem_eq_inter] using h

/-- The independent-set projection also preserves entropy for every law
supported on the code. Entropies are expressed in bits by dividing the
imported natural-log entropy by `log 2`. -/
theorem storageCode_entropy_of_independent [Nonempty α]
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) {N : V → Finset V} {I : Finset V}
    (hI : IsIndependent N I) {C : Finset (V → α)} (hC : IsStorageCode N C)
    (X : Ω → V → α) (hX : ∀ ω, X ω ∈ C) :
    TransposeFollowup.observationEntropy p X / Real.log 2 =
      TransposeFollowup.observationEntropy p (fun ω => outsideWord I (X ω)) / Real.log 2 ∧
    TransposeFollowup.observationEntropy p X / Real.log 2 ≤
      ((Fintype.card V - I.card : ℕ) : ℝ) * (Real.log (Fintype.card α) / Real.log 2) := by
  classical
  let F := fun ω => outsideWord I (X ω)
  have heq : TransposeFollowup.observationEntropy p X =
      TransposeFollowup.observationEntropy p F := by
    apply TransposeFollowup.observationEntropy_eq_of_same_fibers p hp
    intro ω ω'
    constructor
    · intro h
      exact congrArg (outsideWord I) h
    · exact independent_outside_injOn hI hC (hX ω) (hX ω')
  have hbound : TransposeFollowup.observationEntropy p F ≤
      Real.log (Fintype.card ({v // v ∉ I} → α)) := by
    exact TransposeFollowup.entropy_le_log_card (TransposeFollowup.pushforward p F)
      (TransposeFollowup.pushforward_nonneg p hp F)
      (by rw [TransposeFollowup.sum_pushforward, hp1])
  have hbound' : TransposeFollowup.observationEntropy p F ≤
      ((Fintype.card V - I.card : ℕ) : ℝ) * Real.log (Fintype.card α) := by
    simpa [Nat.cast_pow, Real.log_pow] using hbound
  constructor
  · exact congrArg (fun r : ℝ => r / Real.log 2) heq
  · rw [heq, ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hbound'

omit [Fintype V] in
/-- The entropy form of the independent-coordinate bound on every induced
relation, for every probability law supported on its storage code. -/
theorem induced_storageCode_entropy_of_independent [Nonempty α]
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) {N : V → Finset V} {I : Finset V}
    (hI : IsIndependent N I) (Q : Finset V) {C : Finset (Q → α)}
    (hC : IsStorageCode (inducedNeighborhood N Q) C)
    (X : Ω → Q → α) (hX : ∀ ω, X ω ∈ C) :
    TransposeFollowup.observationEntropy p X / Real.log 2 =
      TransposeFollowup.observationEntropy p
        (fun ω => outsideWord (I.subtype (fun v => v ∈ Q)) (X ω)) / Real.log 2 ∧
    TransposeFollowup.observationEntropy p X / Real.log 2 ≤
      ((Q.card - (I ∩ Q).card : ℕ) : ℝ) * (Real.log (Fintype.card α) / Real.log 2) := by
  have h := storageCode_entropy_of_independent p hp hp1 (isIndependent_induced hI Q) hC X hX
  simpa [Finset.card_subtype, Finset.filter_mem_eq_inter] using h

end DirectedRecovery
