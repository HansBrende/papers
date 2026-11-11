import LeanMachine.BlockProgram

/-! Exact paid fields for a block producer: complete state at owner switches,
and each dated value used by another owner, counted once. -/

namespace LeanMachine.BlockProgram

open Finset Classical
variable {O S A : Type*} {R : O → Type*} (p : BlockProgram O R S A)

noncomputable def stateExports (T : ℕ) : Finset ℕ :=
  (range T).filter (fun t => t + 1 < T ∧ p.owner t ≠ p.owner (t + 1))

noncomputable def versionExports (T : ℕ) : Finset ℕ :=
  (range T).filter (fun t => ∃ u < T, t ∈ p.reads u ∧ p.owner t ≠ p.owner u)

theorem even_export_iff (T t : ℕ) :
    2 * t ∈ p.fields.exports (2 * T) ↔ t ∈ p.stateExports T := by
  have hd : 2 * t / 2 = t := by omega
  constructor
  · intro h
    obtain ⟨ht, v, hv, hparent, howner⟩ := mem_filter.mp h
    change 2 * t ∈ p.fieldParents (v / 2) at hparent
    change p.owner (2 * t / 2) ≠ p.owner (v / 2) at howner
    rw [hd] at howner
    have hv' : v / 2 < T := by omega
    rcases mem_union.mp hparent with hs | hr
    · by_cases hz : v / 2 = 0
      · simp [hz] at hs
      · have he : 2 * t = 2 * (v / 2 - 1) := by simpa only [hz, ite_false, mem_singleton] using hs
        have he' : v / 2 = t + 1 := by omega
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), by simpa only [he'] using And.intro hv' howner⟩
    · obtain ⟨j, _, hj⟩ := mem_image.mp hr
      omega
  · intro h
    obtain ⟨_, ht, ho⟩ := mem_filter.mp h
    apply p.fields.mem_exports (t := 2 * (t + 1)) (by omega)
    · change 2 * t ∈ p.fieldParents (2 * (t + 1) / 2)
      have he : 2 * (t + 1) / 2 = t + 1 := by omega
      rw [he]
      simpa only [Nat.add_sub_cancel] using p.state_parent_mem (by omega : t + 1 ≠ 0)
    · change p.owner (2 * t / 2) ≠ p.owner (2 * (t + 1) / 2)
      have he : 2 * (t + 1) / 2 = t + 1 := by omega
      simpa only [hd, he] using ho

theorem odd_export_iff (T t : ℕ) :
    2 * t + 1 ∈ p.fields.exports (2 * T) ↔ t ∈ p.versionExports T := by
  have hd : (2 * t + 1) / 2 = t := by omega
  constructor
  · intro h
    obtain ⟨ht, v, hv, hparent, howner⟩ := mem_filter.mp h
    change 2 * t + 1 ∈ p.fieldParents (v / 2) at hparent
    change p.owner ((2 * t + 1) / 2) ≠ p.owner (v / 2) at howner
    rw [hd] at howner
    have hv' : v / 2 < T := by omega
    rcases mem_union.mp hparent with hs | hr
    · by_cases hz : v / 2 = 0
      · simp [hz] at hs
      · have he : 2 * t + 1 = 2 * (v / 2 - 1) := by simpa only [hz, ite_false, mem_singleton] using hs
        omega
    · obtain ⟨j, hj, he⟩ := mem_image.mp hr
      have he' : j = t := by omega
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp ht; omega),
        v / 2, hv', he' ▸ hj, howner⟩
  · intro h
    obtain ⟨_, v, hv, hr, ho⟩ := mem_filter.mp h
    apply p.fields.mem_exports (t := 2 * v) (by omega)
    · change 2 * t + 1 ∈ p.fieldParents (2 * v / 2)
      have he : 2 * v / 2 = v := by omega
      rw [he]
      exact p.read_parent_mem hr
    · change p.owner ((2 * t + 1) / 2) ≠ p.owner (2 * v / 2)
      have he : 2 * v / 2 = v := by omega
      simpa only [hd, he] using ho

noncomputable def transcript (T : ℕ) (x : (o : O) → R o) :
    (p.stateExports T → S) × (p.versionExports T → A) :=
  ((fun t => (p.eval x t.val).1), fun t => (p.eval x t.val).2)

/-- The field transcript contains precisely the paid state and version values;
its extra coordinates are public constants. -/
theorem transcript_eq_iff_fields {T : ℕ} {x y : (o : O) → R o} :
    p.transcript T x = p.transcript T y ↔
      p.fields.transcript (2 * T) x = p.fields.transcript (2 * T) y := by
  constructor
  · intro h
    funext n
    have hdiv : n.val = 2 * (n.val / 2) + n.val % 2 := by omega
    have heven := (p.fields_eval x (n.val / 2)).1
    have heven' := (p.fields_eval y (n.val / 2)).1
    have hodd := (p.fields_eval x (n.val / 2)).2
    have hodd' := (p.fields_eval y (n.val / 2)).2
    change p.fields.eval x n.val = p.fields.eval y n.val
    by_cases hm : n.val % 2 = 0
    · have hn : n.val = 2 * (n.val / 2) := by omega
      have ht := (p.even_export_iff T (n.val / 2)).mp (hn ▸ n.property)
      rw [hn, heven, heven']
      exact Prod.ext (congrFun (congrArg Prod.fst h) ⟨n.val / 2, ht⟩) rfl
    · have hn : n.val = 2 * (n.val / 2) + 1 := by omega
      have ht := (p.odd_export_iff T (n.val / 2)).mp (hn ▸ n.property)
      rw [hn, hodd, hodd']
      exact Prod.ext rfl (congrFun (congrArg Prod.snd h) ⟨n.val / 2, ht⟩)
  · intro h
    apply Prod.ext
    · funext t
      have he := congrFun h ⟨2 * t.val, (p.even_export_iff T t.val).mpr t.property⟩
      change p.fields.eval x (2 * t.val) = p.fields.eval y (2 * t.val) at he
      rw [(p.fields_eval x t.val).1, (p.fields_eval y t.val).1] at he
      have hh := congrArg Prod.fst he
      exact hh
    · funext t
      have he := congrFun h ⟨2 * t.val + 1, (p.odd_export_iff T t.val).mpr t.property⟩
      change p.fields.eval x (2 * t.val + 1) = p.fields.eval y (2 * t.val + 1) at he
      rw [(p.fields_eval x t.val).2, (p.fields_eval y t.val).2] at he
      have hh := congrArg Prod.snd he
      exact hh

/-- The literal switch-state/dated-version transcript has full product fibres. -/
theorem transcript_mix (T : ℕ) (xs : O → ((o : O) → R o))
    (base : (o : O) → R o) (h : ∀ o, p.transcript T (xs o) = p.transcript T base) :
    p.transcript T (fun o => xs o o) = p.transcript T base := by
  apply p.transcript_eq_iff_fields.mpr
  apply p.fields.transcript_mix
  exact fun o => p.transcript_eq_iff_fields.mp (h o)

end LeanMachine.BlockProgram
