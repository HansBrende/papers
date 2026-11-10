import SwapRigidity.ClassUniform

/-!
# Rules whose decoders change at single entries

A subspace `𝒳` of matrices indexed by `ZMod n` is a code of the *entry rule* `a` if every entry
`X c r` of every `X ∈ 𝒳` is the linear functional `a c r` applied to `rot c X`
(`IsEntryRuleCode`).  A class-uniform rule is the case in which `a c r` depends on `c` only
through the class of `c` (`IsClassUniformCode.exists_isEntryRuleCode`).

* `IsEntryRuleCode.apply_succ_eq`: if `X` and `rot 1 X` lie in the code and
  `a c r = a (c + 1) r`, then `X (c + 1) r = X c (r + 1)`.
* `IsEntryRuleCode.two_mul_finrank_le`: if a set `P` of positions contains `(c + 1, r)` whenever
  `a c r ≠ a (c + 1) r`, and meets every anti-diagonal, then `2 * dim 𝒳 ≤ n ^ 2 + |P|`.
* `IsEntryRuleCode.two_mul_finrank_le_of_changes`: if `B` contains every pair `(c, r)` with
  `a c r ≠ a (c + 1) r`, then `2 * dim 𝒳 ≤ n ^ 2 + n + |B|`.
* `IsEntryRuleCode.two_mul_finrank_le_of_rows`: if the decoders change only at the rows of a
  non-empty set `S`, then `2 * dim 𝒳 ≤ n ^ 2 + n * |S|`, the bound of Theorem TP for the unit
  shift.
-/

namespace SwapRigidity

open Module

variable {F : Type*} [Field F] {n : ℕ} {κ : Type*}

/-- A subspace `𝒳` of matrices is a code of the entry rule `a` if the entry `(c, r)` of every
`X ∈ 𝒳` is the functional `a c r` applied to `X` with its columns rotated by `c`. -/
def IsEntryRuleCode (a : ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F))
    (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) : Prop :=
  ∀ X ∈ 𝒳, ∀ c r, X c r = a c r (rot c X)

/-- A class-uniform code is a code of an entry rule whose functionals depend on the row only
through its class. -/
theorem IsClassUniformCode.exists_isEntryRuleCode {cls : ZMod n → κ}
    {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)} (h : IsClassUniformCode cls 𝒳) :
    ∃ a : κ → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F),
      IsEntryRuleCode (fun c r => a (cls c) r) 𝒳 := by
  obtain ⟨dec, hdec⟩ := h
  exact ⟨fun k r => LinearMap.proj r ∘ₗ dec k, fun X hX c r => congrFun (hdec X hX c) r⟩

namespace IsEntryRuleCode

variable {a : ZMod n → ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] F)}
  {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)}

/-- **One step along an anti-diagonal.**  If `X` and its rotate by one column both lie in the
code, and the functionals of the entries `(c, r)` and `(c + 1, r)` agree, then
`X (c + 1) r = X c (r + 1)`. -/
theorem apply_succ_eq (h : IsEntryRuleCode a 𝒳) {X : Matrix (ZMod n) (ZMod n) F} (hX : X ∈ 𝒳)
    (hX1 : rot 1 X ∈ 𝒳) {c r : ZMod n} (hcr : a c r = a (c + 1) r) :
    X (c + 1) r = X c (r + 1) := by
  have h1 := h X hX (c + 1) r
  have h2 := h _ hX1 c r
  rw [rot_rot] at h2
  rw [h1, ← hcr, ← h2]
  rfl

variable [NeZero n]

/-- **Changes that affect single entries.**  Let `P` be a set of positions that contains
`(c + 1, r)` whenever the functionals of the entries `(c, r)` and `(c + 1, r)` differ, and that
meets every anti-diagonal `{(i, j) | i + j = t}`.  Then `2 * dim 𝒳 ≤ n ^ 2 + |P|`.  The least
size of such a set is `∑ t, max 1 (m t)`, where `m t` is the number of changes on the
anti-diagonal `t`. -/
theorem two_mul_finrank_le (h : IsEntryRuleCode a 𝒳) {P : Finset (ZMod n × ZMod n)}
    (hP : ∀ c r, (c + 1, r) ∉ P → a c r = a (c + 1) r)
    (hdiag : ∀ t : ZMod n, ∃ p ∈ P, p.1 + p.2 = t) :
    2 * finrank F 𝒳 ≤ n ^ 2 + P.card := by
  -- the matrices of the code whose rotate by one column also lies in the code
  set 𝒳' : Submodule F (Matrix (ZMod n) (ZMod n) F) :=
    ⨅ δ ∈ ({0, 1} : Finset (ZMod n)), 𝒳.comap (rot δ) with h𝒳'
  have hmem : ∀ X ∈ 𝒳', X ∈ 𝒳 ∧ rot 1 X ∈ 𝒳 := by
    intro X hX
    simp only [h𝒳', Submodule.mem_iInf, Submodule.mem_comap] at hX
    have h0 := hX 0 (by simp)
    have e : rot (0 : ZMod n) X = X := by
      ext i j
      simp
    rw [e] at h0
    exact ⟨h0, hX 1 (by simp)⟩
  -- pigeonhole: this space is large
  have hcount : ({0, 1} : Finset (ZMod n)).card * finrank F 𝒳 + n * n ≤
      ({0, 1} : Finset (ZMod n)).card * (n * n) + finrank F 𝒳' := by
    have := card_mul_finrank_add_le_iInf_comap ({0, 1} : Finset (ZMod n)) 𝒳 (fun δ => rot δ)
    rwa [finrank_matrix_zmod] at this
  -- walking up an anti-diagonal from `(i, j)` until it meets `P`
  have hstep : ∀ X ∈ 𝒳', (∀ p ∈ P, X p.1 p.2 = 0) → ∀ k : ℕ, ∀ i j : ZMod n,
      (i - (k : ZMod n), j + (k : ZMod n)) ∈ P → X i j = 0 := by
    intro X hX hzero k
    induction k with
    | zero =>
      intro i j hij
      have hij' : (i, j) ∈ P := by simpa using hij
      exact hzero _ hij'
    | succ k ih =>
      intro i j hij
      by_cases hP' : (i, j) ∈ P
      · exact hzero _ hP'
      · have hsame : a (i - 1) j = a (i - 1 + 1) j :=
          hP (i - 1) j (by rwa [sub_add_cancel])
        have hrel := h.apply_succ_eq (hmem X hX).1 (hmem X hX).2 hsame
        rw [sub_add_cancel] at hrel
        rw [hrel]
        apply ih
        have e : (i - 1 - (k : ZMod n), j + 1 + (k : ZMod n)) =
            (i - ((k + 1 : ℕ) : ZMod n), j + ((k + 1 : ℕ) : ZMod n)) := by
          push_cast
          exact Prod.ext (by ring) (by ring)
        rwa [e]
  -- restriction to the positions in `P` is injective on this space
  let res : 𝒳' →ₗ[F] (P → F) :=
    { toFun := fun X p => (X : Matrix (ZMod n) (ZMod n) F) p.1.1 p.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    funext i j
    obtain ⟨p, hp, hpt⟩ := hdiag (i + j)
    have hzero : ∀ q ∈ P, (X : Matrix (ZMod n) (ZMod n) F) q.1 q.2 = 0 :=
      fun q hq => congrFun hX ⟨q, hq⟩
    refine hstep X X.2 hzero (i - p.1).val i j ?_
    have h2 : p.2 = i + j - p.1 := by
      rw [← hpt]
      ring
    have e : (i - (((i - p.1).val : ℕ) : ZMod n), j + (((i - p.1).val : ℕ) : ZMod n)) = p := by
      rw [ZMod.natCast_zmod_val]
      refine Prod.ext (by simp) ?_
      simp only
      rw [h2]
      ring
    rwa [e]
  have hdim : finrank F 𝒳' ≤ P.card := by
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hpi : finrank F (P → F) = P.card := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    rwa [hpi] at hle
  by_cases h01 : (0 : ZMod n) = 1
  · -- `n = 1`: the two shifts coincide, and the trivial bound suffices
    have hD : finrank F 𝒳 ≤ n * n := finrank_matrix_zmod (F := F) (n := n) ▸ 𝒳.finrank_le
    rw [← h01, Finset.pair_eq_singleton, Finset.card_singleton] at hcount
    rw [pow_two]
    omega
  · rw [Finset.card_pair h01] at hcount
    rw [pow_two]
    omega

/-- **Half a symbol for each change.**  If `B` contains every pair `(c, r)` at which the
functional changes from row `c` to row `c + 1`, then `2 * dim 𝒳 ≤ n ^ 2 + n + |B|`. -/
theorem two_mul_finrank_le_of_changes (h : IsEntryRuleCode a 𝒳) {B : Finset (ZMod n × ZMod n)}
    (hB : ∀ c r, (c, r) ∉ B → a c r = a (c + 1) r) :
    2 * finrank F 𝒳 ≤ n ^ 2 + n + B.card := by
  let P : Finset (ZMod n × ZMod n) :=
    B.image (fun p => (p.1 + 1, p.2)) ∪ Finset.univ.image (fun t : ZMod n => ((0 : ZMod n), t))
  have hP : ∀ c r, (c + 1, r) ∉ P → a c r = a (c + 1) r := by
    intro c r hcr
    refine hB c r fun hmem => hcr ?_
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(c, r), hmem, rfl⟩)
  have hdiag : ∀ t : ZMod n, ∃ p ∈ P, p.1 + p.2 = t := fun t =>
    ⟨(0, t), Finset.mem_union_right _ (Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩), by simp⟩
  have hcard : P.card ≤ B.card + n := by
    refine (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le ?_)
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ZMod.card]
  have := h.two_mul_finrank_le hP hdiag
  omega

/-- **Changes at whole rows.**  If the functionals change only at the rows of a non-empty set
`S`, that is, `a c r = a (c + 1) r` for all `r` whenever `c + 1 ∉ S`, then
`2 * dim 𝒳 ≤ n ^ 2 + n * |S|`.  This is the bound of Theorem TP for the unit shift. -/
theorem two_mul_finrank_le_of_rows (h : IsEntryRuleCode a 𝒳) {S : Finset (ZMod n)}
    (hS : S.Nonempty) (hrow : ∀ c, c + 1 ∉ S → ∀ r, a c r = a (c + 1) r) :
    2 * finrank F 𝒳 ≤ n ^ 2 + n * S.card := by
  have hP : ∀ c r, (c + 1, r) ∉ S ×ˢ (Finset.univ : Finset (ZMod n)) → a c r = a (c + 1) r := by
    intro c r hcr
    exact hrow c (fun hc => hcr (Finset.mem_product.2 ⟨hc, Finset.mem_univ _⟩)) r
  have hdiag : ∀ t : ZMod n, ∃ p ∈ S ×ˢ (Finset.univ : Finset (ZMod n)), p.1 + p.2 = t := by
    intro t
    obtain ⟨s, hs⟩ := hS
    exact ⟨(s, t - s), Finset.mem_product.2 ⟨hs, Finset.mem_univ _⟩, by simp⟩
  have := h.two_mul_finrank_le hP hdiag
  rw [Finset.card_product, Finset.card_univ, ZMod.card] at this
  rwa [mul_comm n S.card]

end IsEntryRuleCode

end SwapRigidity
