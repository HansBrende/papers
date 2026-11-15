import DirectedRecovery.StorageCode

/-!
# Local record views and finite covering invoices

On the full source cube, each coordinate is determined by fixed raw helpers
and a fixed view of a common record tuple. Fixing the exterior of a patch
turns the selected records into an index code for the induced relation.
Paper 5's fibre bound then pays each patch's storage-code deficit.

The counting adapter allows arbitrary finite source and record alphabets.
Its binary consequences allow unequal record widths and fractional covers.
No causal origin, native cut, or local capacity theorem is supplied here.
-/

namespace LeanBacklog.LocalRecordViews

open Finset DirectedRecovery MotionDepthCodes
open scoped BigOperators
set_option autoImplicit false

variable {V R α : Type*} {β : R → Type*}

/-- Fixed raw-helper and record views recover every coordinate on the full
source cube. The record tuple may be any function of the entire input. -/
def Recovers (N : V → Finset V) (view : V → Finset R)
    (a : (V → α) → (r : R) → β r) : Prop :=
  ∀ x y v, (∀ u ∈ N v, x u = y u) →
    (∀ r ∈ view v, a x r = a y r) → x v = y v

variable [DecidableEq V]

/-- Fill a patch freely and keep every exterior coordinate fixed. -/
def fill (S : Finset V) (z : V → α) (x : S → α) : V → α :=
  fun v => if hv : v ∈ S then x ⟨v, hv⟩ else z v

/-- The records selected for a patch, after fixing its exterior input. -/
def patchEncoder (a : (V → α) → (r : R) → β r)
    (S : Finset V) (T : Finset R) (z : V → α) (x : S → α) :
    (r : T) → β r := fun r => a (fill S z x) r

/-- Exterior conditioning makes the selected records an index code for
the induced relation. Every selected target's complete record view must
lie in `T`; raw helpers outside `S` are held fixed, not discarded. -/
theorem isIndexCode_patchEncoder {N : V → Finset V} {view : V → Finset R}
    {a : (V → α) → (r : R) → β r} (ha : Recovers N view a)
    (S : Finset V) (T : Finset R) (z : V → α)
    (hview : ∀ v ∈ S, view v ⊆ T) :
    IsIndexCode (inducedNeighborhood N S) (patchEncoder a S T z) := by
  intro x y hxy v hraw
  have hv := ha (fill S z x) (fill S z y) v (by
    intro u hu
    by_cases huS : u ∈ S
    · simpa [fill, huS] using hraw ⟨u, huS⟩ (by
        simpa [inducedNeighborhood] using hu)
    · simp [fill, huS]) (by
    intro r hr
    exact congrFun hxy ⟨r, hview v v.property hr⟩)
  simpa [fill, v.property] using hv

open Classical in
/-- The alphabet-independent local invoice. No independence of records or
uniform distribution on their values is assumed. -/
theorem patch_card_le [Fintype V] [Fintype α] [∀ r, Fintype (β r)]
    {N : V → Finset V} {view : V → Finset R}
    {a : (V → α) → (r : R) → β r} (ha : Recovers N view a)
    (S : Finset V) (T : Finset R) (z : V → α)
    (hview : ∀ v ∈ S, view v ⊆ T) {cap : ℝ}
    (hcap : ∀ C : Finset (S → α), IsStorageCode (inducedNeighborhood N S) C →
      (C.card : ℝ) ≤ cap) :
    (Fintype.card α : ℝ) ^ S.card ≤
      (Fintype.card ((r : T) → β r) : ℝ) * cap := by
  simpa using indexCode_card_le (isIndexCode_patchEncoder ha S T z hview) hcap

open Classical in
/-- Actual bit lengths add, including for unequal record widths. -/
theorem card_recordWords (width : R → ℕ) (T : Finset R) :
    Fintype.card ((r : T) → Fin (width r) → Bool) =
      2 ^ (∑ r ∈ T, width r) := by
  classical
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_coe_sort T width

/-- A binary patch's deficit is at most the total width of its selected
records. Capacities and deficits are real-valued; subtraction is not truncated. -/
theorem patch_deficit_le [Fintype V] {N : V → Finset V} {view : V → Finset R}
    {width : R → ℕ} {a : (V → Bool) → (r : R) → Fin (width r) → Bool}
    (ha : Recovers N view a) (S : Finset V) (T : Finset R)
    (hview : ∀ v ∈ S, view v ⊆ T) {cap : ℝ}
    (hcap : ∀ C : Finset (S → Bool), IsStorageCode (inducedNeighborhood N S) C →
      (C.card : ℝ) ≤ (2 : ℝ) ^ cap) :
    (S.card : ℝ) - cap ≤ (∑ r ∈ T, width r : ℕ) := by
  have h := patch_card_le ha S T (fun _ => false) hview hcap
  rw [Fintype.card_bool, card_recordWords] at h
  have hpow : (2 : ℝ) ^ (S.card : ℝ) ≤
      (2 : ℝ) ^ ((∑ r ∈ T, width r : ℕ) + cap) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using h
  have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
  linarith

variable {I : Type*} [Fintype I] [Fintype V]

/-- Sum any nonnegative weighted collection of local invoices. Patch and
record overlaps are both allowed; only the latter are charged on the right. -/
theorem weighted_deficit_le {N : V → Finset V} {view : V → Finset R}
    {width : R → ℕ} {a : (V → Bool) → (r : R) → Fin (width r) → Bool}
    (ha : Recovers N view a) (S : I → Finset V) (T : I → Finset R)
    (weight cap : I → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hview : ∀ i v, v ∈ S i → view v ⊆ T i)
    (hcap : ∀ i (C : Finset (S i → Bool)),
      IsStorageCode (inducedNeighborhood N (S i)) C → (C.card : ℝ) ≤ (2 : ℝ) ^ cap i) :
    ∑ i, weight i * ((S i).card - cap i) ≤
      ∑ i, weight i * (∑ r ∈ T i, width r : ℕ) := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (patch_deficit_le ha (S i) (T i) (hview i) (hcap i)) (hweight i)

/-- A fractional cover counts every source coordinate at least once. -/
theorem card_le_weighted_cover (S : I → Finset V) (weight : I → ℝ)
    (hcover : ∀ v, 1 ≤ ∑ i, if v ∈ S i then weight i else 0) :
    (Fintype.card V : ℝ) ≤ ∑ i, weight i * (S i).card := by
  classical
  calc
    (Fintype.card V : ℝ) = ∑ v : V, (1 : ℝ) := by simp
    _ ≤ ∑ v : V, ∑ i, if v ∈ S i then weight i else 0 :=
      Finset.sum_le_sum fun v _ => hcover v
    _ = ∑ i, weight i * (S i).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm]

/-- The cover consumer: local half bounds with summable errors pay half
the full source cube. Unequal record widths and fractional covers are allowed.
This is an abstract invoice, not a native cut or separation theorem. -/
theorem weighted_half_invoice {N : V → Finset V} {view : V → Finset R}
    {width : R → ℕ} {a : (V → Bool) → (r : R) → Fin (width r) → Bool}
    (ha : Recovers N view a) (S : I → Finset V) (T : I → Finset R)
    (weight error : I → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hview : ∀ i v, v ∈ S i → view v ⊆ T i)
    (hcap : ∀ i (C : Finset (S i → Bool)),
      IsStorageCode (inducedNeighborhood N (S i)) C →
      (C.card : ℝ) ≤ (2 : ℝ) ^ ((S i).card / 2 + error i))
    (hcover : ∀ v, 1 ≤ ∑ i, if v ∈ S i then weight i else 0) :
    (Fintype.card V : ℝ) / 2 - ∑ i, weight i * error i ≤
      ∑ i, weight i * (∑ r ∈ T i, width r : ℕ) := by
  have hd := weighted_deficit_le ha S T weight
    (fun i => (S i).card / 2 + error i) hweight hview hcap
  have hc := card_le_weighted_cover S weight hcover
  have heq : (∑ i, weight i * ((S i).card - ((S i).card / 2 + error i))) =
      (∑ i, weight i * (S i).card) / 2 - ∑ i, weight i * error i := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq] at hd
  linarith

/-- Equal-width, unweighted form: if the selected patches cover the source
coordinates and the total number of record uses is at most `overlap * m`,
then `s * overlap * m` pays the local half deficit. -/
theorem half_invoice [Fintype R] {N : V → Finset V} {view : V → Finset R}
    {s : ℕ} {a : (V → Bool) → R → Fin s → Bool}
    (ha : Recovers N view a) (S : I → Finset V) (T : I → Finset R)
    (error : I → ℝ) (hview : ∀ i v, v ∈ S i → view v ⊆ T i)
    (hcap : ∀ i (C : Finset (S i → Bool)),
      IsStorageCode (inducedNeighborhood N (S i)) C →
      (C.card : ℝ) ≤ (2 : ℝ) ^ ((S i).card / 2 + error i))
    (hcover : ∀ v, ∃ i, v ∈ S i) {overlap : ℝ}
    (huses : (∑ i, (T i).card : ℕ) ≤ overlap * Fintype.card R) :
    (Fintype.card V : ℝ) / 2 - ∑ i, error i ≤ s * overlap * Fintype.card R := by
  classical
  have hcover' : ∀ v, (1 : ℝ) ≤ ∑ i, if v ∈ S i then 1 else 0 := by
    intro v
    obtain ⟨i, hi⟩ := hcover v
    have hi' := Finset.single_le_sum
      (s := (Finset.univ : Finset I))
      (f := fun j => if v ∈ S j then (1 : ℝ) else 0)
      (fun j _ => by split <;> norm_num) (Finset.mem_univ i)
    simpa only [hi, ite_true] using hi'
  have h := weighted_half_invoice ha S T (fun _ => 1) error
    (fun _ => by norm_num) hview hcap hcover'
  have heq : (∑ i, (1 : ℝ) * (∑ _r ∈ T i, s : ℕ)) =
      s * (∑ i, (T i).card : ℕ) := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum, mul_comm]
  simp only [one_mul] at h
  have hbill : (∑ i, ((∑ _r ∈ T i, s : ℕ) : ℝ)) ≤
      s * overlap * Fintype.card R := by
    simpa only [one_mul, mul_assoc] using
      heq.le.trans (mul_le_mul_of_nonneg_left huses (Nat.cast_nonneg s))
  simpa only [one_mul] using h.trans hbill

#print axioms Recovers
#print axioms fill
#print axioms patchEncoder
#print axioms isIndexCode_patchEncoder
#print axioms patch_card_le
#print axioms card_recordWords
#print axioms patch_deficit_le
#print axioms weighted_deficit_le
#print axioms card_le_weighted_cover
#print axioms weighted_half_invoice
#print axioms half_invoice

end LeanBacklog.LocalRecordViews
