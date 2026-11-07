import TapeStorageRates.Conditioning
import BoundedStackDepth.Machines
import MergeDepth.SkelUniformQ91

/-!
# Frozen packet computations

A local record may have any finite alphabet. On one schedule class, its value is determined by
the packet at the physical input address and the records at the state and last-write predecessors.
Revealing a set of records turns the largest common fibre into a storage code for Paper 11's
actual cone relation. Only values attained on the chosen class are charged.
-/

namespace TapeStorageRates

open Finset MergeDepth BoundedNesting DirectedRecovery MotionDepthCodes

set_option autoImplicit false

section Frozen

variable {k n T : ℕ} {A B : Type*}

/-- One local transition on a fixed packet schedule. All input-dependent data read at a tick
occur in the scanned packet or in predecessor records. The input set can be any finite fibre. -/
def PacketLocal (z : Tp k → ℕ → ℤ) (T : ℕ) (S : Finset (Fin n → A))
    (val : (Fin n → A) → ℕ → B) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ t < T,
    (∀ u, DepStep (fun j => z (some (some j))) T t u → val x u = val y u) →
    (∀ i : Fin n, (i : ℤ) = z none t → x i = y i) → val x t = val y t

/-- Agreement on revealed records and the input packets reached by unrevealed paths
determines the root record. This permits arbitrary alphabets, nonlinear updates and initial
tape symbols fixed by the public layout. -/
theorem PacketLocal.record_eq {z : Tp k → ℕ → ℤ} {S : Finset (Fin n → A)}
    {val : (Fin n → A) → ℕ → B} (hloc : PacketLocal z T S val)
    {x y : Fin n → A} (hx : x ∈ S) (hy : y ∈ S) {Γ : Finset ℕ}
    (hg : ∀ u ∈ Γ, val x u = val y u) (t : ℕ) (ht : t < T)
    (hin : ∀ (π : List ℕ), IsDepPath (fun j => z (some (some j))) T (t :: π) →
      LinNet.GFree Γ (t :: π) → ∀ i : Fin n,
        (i : ℤ) = z none ((t :: π).getLastD t) → x i = y i) :
    val x t = val y t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases htΓ : t ∈ Γ
    · exact hg t htΓ
    apply hloc x hx y hy t ht
    · intro u hu
      by_cases huΓ : u ∈ Γ
      · exact hg u huΓ
      apply ih u (depStep_lt hu).1 ((depStep_lt hu).1.trans ht)
      intro π hπ hfree i hi
      apply hin (u :: π) ⟨hu, hπ⟩ (gfree_cons_cons.mpr ⟨huΓ, hfree⟩) i
      rwa [LinNet.getLastD_cons_cons]
    · exact hin [] trivial (gfree_singleton Γ t)

open Classical in
/-- A largest common genie fibre is a storage code on the actual append-time cone.
The integer inequality pays exactly the number of distinct revealed words within this schedule. -/
theorem PacketLocal.exists_cone_code {z : Tp k → ℕ → ℤ} {S : Finset (Fin n → A)}
    {val : (Fin n → A) → ℕ → B} (hloc : PacketLocal z T S val) (hne : S.Nonempty)
    (Γ : Finset ℕ) (ot dm : ℕ → ℕ) (ht : ∀ q : Fin n, ot (dm q) < T)
    (houtput : ∀ x ∈ S, ∀ y ∈ S, ∀ q : Fin n,
      val x (ot (dm q)) = val y (ot (dm q)) → x q = y q) :
    ∃ C ⊆ S, C.Nonempty ∧ IsStorageCode (coneRel 1 z T Γ ot (fun q : Fin n => dm q)) C ∧
      S.card ≤ (S.image (fun x u => val x (u : Γ))).card * C.card := by
  let msg := fun (x : Fin n → A) (u : Γ) => val x u
  obtain ⟨m, hm, hcard⟩ := exists_large_observation_fibre hne msg
  refine ⟨S.filter (fun x => msg x = m), filter_subset _ _, ?_, ?_, hcard⟩
  · obtain ⟨x, hx, hxm⟩ := mem_image.mp hm
    exact ⟨x, mem_filter.mpr ⟨hx, hxm⟩⟩
  · intro x hx y hy q hagree
    obtain ⟨hxS, hxm⟩ := mem_filter.mp hx
    obtain ⟨hyS, hym⟩ := mem_filter.mp hy
    apply houtput x hxS y hyS q
    apply hloc.record_eq hxS hyS (fun u hu => congrFun (hxm.trans hym.symm) ⟨u, hu⟩)
      (ot (dm q)) (ht q)
    intro π hπ hfree i hi
    apply hagree i
    simp only [coneRel, mem_filter, mem_univ, true_and, Nat.cast_one, skel_one, Int.ediv_one]
    exact ⟨π, hπ, hfree, hi⟩

open Classical in
/-- Whole-step depth reduction, for packet records. No assumption on the frequency of visits to
a cell or on the schedule outside the chosen class is required. -/
theorem PacketLocal.paid_cone_code {z : Tp k → ℕ → ℤ} {S : Finset (Fin n → A)}
    {val : (Fin n → A) → ℕ → B} (hloc : PacketLocal z T S val) (hne : S.Nonempty)
    [Fintype B] {β : ℕ} (hβ : 1 ≤ β) (hB : Fintype.card B ≤ 2 ^ β) (hn : 1 ≤ n)
    {c ε : ℝ} (hc : 1 ≤ c) (hε : 0 < ε) (htime : (T : ℝ) ≤ c * (n + 1))
    (hwalk : ∀ j, IsWalk (z (some (some j)))) (ot dm : ℕ → ℕ)
    (ht : ∀ q : Fin n, ot (dm q) < T)
    (houtput : ∀ x ∈ S, ∀ y ∈ S, ∀ q : Fin n,
      val x (ot (dm q)) = val y (ot (dm q)) → x q = y q) :
    ∃ (Γ : Finset ℕ) (C : Finset (Fin n → A)), C ⊆ S ∧ C.Nonempty ∧
      IsStorageCode (coneRel 1 z T Γ ot (fun q : Fin n => dm q)) C ∧
      (β * Γ.card : ℝ) ≤ ε * n ∧ S.card ≤ 2 ^ (β * Γ.card) * C.card ∧
      ∀ π, IsDepPath (fun j => z (some (some j))) T π → LinNet.GFree Γ π →
        π.length ≤ BoundedStackDepth.genieDepth k β c ε := by
  obtain ⟨Γ, hcost, hdepth⟩ := BoundedStackDepth.genie_cost hβ hn hc hε htime _ hwalk
  obtain ⟨C, hCS, hCne, hC, hcard⟩ := hloc.exists_cone_code hne Γ ot dm ht houtput
  refine ⟨Γ, C, hCS, hCne, hC, hcost, hcard.trans (Nat.mul_le_mul_right _ ?_), hdepth⟩
  calc
    (S.image (fun x u => val x (u : Γ))).card ≤ Fintype.card (Γ → B) := card_le_univ _
    _ = (Fintype.card B) ^ Γ.card := by simp
    _ ≤ (2 ^ β) ^ Γ.card := Nat.pow_le_pow_left hB _
    _ = _ := (pow_mul _ _ _).symm

end Frozen

/-- A successful common-schedule class at one packet dimension. Correctness is required only on
the indicated set of payloads. Records use β bits, with any unused values allowed. -/
structure PacketClass (k s β d b : ℕ) where
  time : ℕ
  words : Finset (Fin (d * d * b) → Fin s → Bool)
  nonempty : words.Nonempty
  walks : Tp k → ℕ → ℤ
  unit_walk : ∀ j, IsWalk (walks j)
  record : (Fin (d*d*b) → Fin s → Bool) → ℕ → Fin (2^β)
  local_record : PacketLocal walks time words record
  outputTime : ℕ → ℕ
  outputPosition : ∀ q : Fin (d*d*b), outputTime (tpos d b q) < time ∧
    (tpos d b q : ℤ) = walks (some none) (outputTime (tpos d b q))
  outputDetermined : ∀ x ∈ words, ∀ y ∈ words, ∀ q : Fin (d*d*b),
    record x (outputTime (tpos d b q)) = record y (outputTime (tpos d b q)) → x q = y q

/-- On unbounded dimensions a packet class costs at most A bits per input packet. -/
def HasPacketClasses (k s β A : ℕ) (c : ℝ) : Prop :=
  ∀ d₀, ∃ d ≥ d₀, ∃ b, 1 ≤ b ∧ ∃ W : PacketClass k s β d b,
    (W.time : ℝ) ≤ c * ((d*d*b : ℕ) + 1) ∧
    2 ^ (s * (d*d*b)) ≤ 2 ^ (A * (d*d*b)) * W.words.card

end TapeStorageRates
