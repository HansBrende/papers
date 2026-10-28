import LeanMachine.MonotonePatches
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Complete finite action orbits with deterministic continuation after the first step. -/

namespace LeanMachine.FiniteOrbits

open Classical Finset MonotonePatches

noncomputable section

/-- All values reachable in at most `N` nonidentity steps. -/
def cloud (s : ℕ → Finset ℕ) : ℕ → ℕ → Finset ℕ
  | 0, t => {t}
  | N + 1, t => insert t ((s t).biUnion (cloud s N))

theorem mem_cloud_self (s : ℕ → Finset ℕ) (N t : ℕ) : t ∈ cloud s N t := by
  cases N <;> simp [cloud]

theorem cloud_mono (s : ℕ → Finset ℕ) {N D : ℕ} (h : N ≤ D) (t : ℕ) :
    cloud s N t ⊆ cloud s D t := by
  suffices ∀ n t, cloud s n t ⊆ cloud s (n + 1) t from
    monotone_nat_of_le_succ (fun n => this n t) h
  intro n
  induction n with
  | zero => intro t; simp [cloud]
  | succ n ih =>
    intro t
    exact insert_subset_insert t (biUnion_mono (fun u _ => ih u))

/-- Each post-step state has at most one successor. The initial state may branch. -/
def DeterministicAfterStep (s : ℕ → Finset ℕ) : Prop :=
  ∀ t, ∀ u ∈ s t, (s u).card ≤ 1

theorem cloud_card_le_chain {s : ℕ → Finset ℕ} (hs : DeterministicAfterStep s)
    (N t : ℕ) (ht : (s t).card ≤ 1) : (cloud s N t).card ≤ N + 1 := by
  induction N generalizing t with
  | zero => simp [cloud]
  | succ N ih =>
    calc
      _ ≤ 1 + ∑ u ∈ s t, (cloud s N u).card :=
        (card_insert_le _ _).trans (by have := card_biUnion_le (s := s t) (t := cloud s N); omega)
      _ ≤ 1 + ∑ _u ∈ s t, (N + 1) := by
        gcongr with u hu; exact ih u (hs t u hu)
      _ ≤ N + 1 + 1 := by simp only [sum_const, smul_eq_mul]; nlinarith

/-- The complete bounded orbit is one root plus one deterministic chain per
distinct first-step value. Collisions only improve this bound. -/
theorem cloud_card_le {s : ℕ → Finset ℕ} (hs : DeterministicAfterStep s)
    (N t : ℕ) : (cloud s N t).card ≤ 1 + N * (s t).card := by
  cases N with
  | zero => simp [cloud]
  | succ N =>
    calc
      _ ≤ 1 + ∑ u ∈ s t, (cloud s N u).card :=
        (card_insert_le _ _).trans (by have := card_biUnion_le (s := s t) (t := cloud s N); omega)
      _ ≤ 1 + ∑ _u ∈ s t, (N + 1) := by
        gcongr with u hu; exact cloud_card_le_chain hs N u (hs t u hu)
      _ = _ := by simp [mul_comm]

variable {A : Type*}

def successors (I : Finset A) (F : A → Action) (t : ℕ) : Finset ℕ :=
  (I.filter (fun a => (F a).apply t ≠ t)).image (fun a => (F a).apply t)

def wordOrbit (I : Finset A) (F : A → Action) (t : ℕ) : Set ℕ :=
  {u | ∃ w : List A, (∀ a ∈ w, a ∈ I) ∧ Action.endpoint (w.map F) t = u}

theorem wordOrbit_mono {I J : Finset A} (F : A → Action) (hIJ : I ⊆ J) {t u : ℕ}
    (hu : u ∈ wordOrbit I F t) : u ∈ wordOrbit J F t := by
  obtain ⟨w, hw, he⟩ := hu
  exact ⟨w, fun a ha => hIJ (hw a ha), he⟩

theorem wordOrbit_trans {I : Finset A} {F : A → Action} {t u v : ℕ}
    (hu : u ∈ wordOrbit I F t) (hv : v ∈ wordOrbit I F u) : v ∈ wordOrbit I F t := by
  obtain ⟨w, hw, rfl⟩ := hu
  obtain ⟨z, hz, rfl⟩ := hv
  refine ⟨w ++ z, ?_, ?_⟩
  · intro a ha
    exact (List.mem_append.mp ha).elim (hw a) (hz a)
  simp only [List.map_append, Action.endpoint_append]

/-- Relabeling an indexed family preserves its full word orbit, even if labels collide. -/
theorem wordOrbit_image {B : Type*} [DecidableEq B]
    (I : Finset A) (f : A → B) (F : B → Action) (t : ℕ) :
    wordOrbit (I.image f) F t = wordOrbit I (F ∘ f) t := by
  have lift (w : List B) (hw : ∀ b ∈ w, b ∈ I.image f) :
      ∃ v : List A, (∀ a ∈ v, a ∈ I) ∧ v.map f = w := by
    induction w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons b w ih =>
      obtain ⟨a, ha, rfl⟩ := mem_image.mp (hw b (List.mem_cons_self ..))
      obtain ⟨v, hv, he⟩ := ih (fun b hb => hw b (List.mem_cons_of_mem _ hb))
      exact ⟨a :: v, by simpa using And.intro ha hv, by simp [he]⟩
  ext u
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨v, hv, hmap⟩ := lift w hw
    refine ⟨v, hv, ?_⟩
    rw [← List.map_map, hmap]
    exact he
  · rintro ⟨w, hw, he⟩
    refine ⟨w.map f, ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact mem_image_of_mem f (hw a ha)
    · simpa only [List.map_map] using he

/-- Erase inactive actions while preserving indices, membership and the endpoint. -/
theorem reduce_word (F : A → Action) (w : List A) (t : ℕ) :
    ∃ v : List A, v.Sublist w ∧ t ∈ Action.success (v.map F) ∧
      Action.endpoint (v.map F) t = Action.endpoint (w.map F) t := by
  induction w generalizing t with
  | nil => exact ⟨[], .refl _, Set.mem_univ _, rfl⟩
  | cons a w ih =>
    obtain ⟨v, hv, hs, he⟩ := ih ((F a).apply t)
    by_cases ha : (F a).apply t = t
    · refine ⟨v, hv.cons a, ?_, ?_⟩
      · simpa only [ha] using hs
      · simpa only [List.map_cons, Action.endpoint, ha] using he
    · exact ⟨a :: v, hv.cons_cons a,
        (Action.success_cons_iff _ _ _).mpr ⟨ha, hs⟩, he⟩

theorem endpoint_mem_cloud (I : Finset A) (F : A → Action) (w : List A)
    (hw : ∀ a ∈ w, a ∈ I) (t : ℕ) :
    Action.endpoint (w.map F) t ∈ cloud (successors I F) w.length t := by
  induction w generalizing t with
  | nil => simp [Action.endpoint, cloud]
  | cons a w ih =>
    have htail := ih (fun b hb => hw b (List.mem_cons_of_mem a hb)) ((F a).apply t)
    change Action.endpoint (w.map F) ((F a).apply t) ∈
      insert t ((successors I F t).biUnion (cloud (successors I F) w.length))
    by_cases ha : (F a).apply t = t
    · simpa only [ha, cloud] using cloud_mono (successors I F) (Nat.le_succ w.length) t
        (by simpa only [ha] using htail)
    · apply mem_insert_of_mem
      exact mem_biUnion.mpr ⟨(F a).apply t,
        mem_image.mpr ⟨a, mem_filter.mpr ⟨hw a (List.mem_cons_self ..), ha⟩, rfl⟩, htail⟩

theorem cloud_subset_orbit (I : Finset A) (F : A → Action) (N t : ℕ) :
    (cloud (successors I F) N t : Set ℕ) ⊆ wordOrbit I F t := by
  induction N generalizing t with
  | zero =>
    intro u hu
    have : u = t := mem_singleton.mp hu
    subst u; exact ⟨[], by simp, rfl⟩
  | succ N ih =>
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact ⟨[], by simp, rfl⟩
    obtain ⟨v, hv, hu⟩ := mem_biUnion.mp hu
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hv
    obtain ⟨w, hw, he⟩ := ih _ hu
    exact ⟨a :: w, by simpa using And.intro (mem_filter.mp ha).1 hw, he⟩

/-- A bound on successful words bounds the full orbit of arbitrary words.
Inactive actions, repeated stopping points and the empty word are included. -/
theorem orbit_eq_cloud (I : Finset A) (F : A → Action) (N t : ℕ)
    (hN : ∀ w : List A, (∀ a ∈ w, a ∈ I) → t ∈ Action.success (w.map F) → w.length ≤ N) :
    wordOrbit I F t = (cloud (successors I F) N t : Set ℕ) := by
  apply Set.Subset.antisymm
  · rintro u ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hs, he⟩ := reduce_word F w t
    have hvI : ∀ a ∈ v, a ∈ I := fun a ha => hw a (hv.subset ha)
    rw [← he]
    exact cloud_mono (successors I F) (hN v hvI hs) t (endpoint_mem_cloud I F v hvI t)
  · exact cloud_subset_orbit I F N t

end
end LeanMachine.FiniteOrbits
