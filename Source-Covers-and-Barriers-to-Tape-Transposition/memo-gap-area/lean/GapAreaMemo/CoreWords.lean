import GapAreaMemo.Funnels

set_option autoImplicit false

/-!
# Successful core words: branches, producers and leaves

Successful core words from a fixed root that start with the same family are
prefixes of one another, because after a nonidentity step at most one core
family can act. A successful word is a simple path of the overlap forest, so
its internal letters are nonleaves. Hence a root has at most two branches,
each branch uses a family at most once, and leaves occur only at the two ends
of a branch. These facts give production counts that are linear in the
number of roots.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- A core word is successful from `t`: every letter acts nontrivially in turn. -/
abbrev CoreSuccess (w : List (CoreFamily K)) (t : ℕ) : Prop :=
  t ∈ Action.success (w.map coreAction)

abbrev coreEndpoint (w : List (CoreFamily K)) (t : ℕ) : ℕ :=
  Action.endpoint (w.map coreAction) t

theorem coreSuccess_cons_iff (q : CoreFamily K) (w : List (CoreFamily K)) (t : ℕ) :
    CoreSuccess (q :: w) t ↔ q.val.shadow t ≠ t ∧ CoreSuccess w (q.val.shadow t) :=
  Action.success_cons_iff _ _ t

theorem coreSuccess_append_singleton (w : List (CoreFamily K)) (q : CoreFamily K) (t : ℕ) :
    CoreSuccess (w ++ [q]) t ↔
      CoreSuccess w t ∧ q.val.shadow (coreEndpoint w t) ≠ coreEndpoint w t := by
  simp only [CoreSuccess, coreEndpoint, List.map_append, List.map_cons, List.map_nil,
    Action.success_append, Action.success_cons_iff]
  simp [Action.success, coreAction, ActualFamily.shadow]

theorem coreEndpoint_append_singleton (w : List (CoreFamily K)) (q : CoreFamily K) (t : ℕ) :
    coreEndpoint (w ++ [q]) t = q.val.shadow (coreEndpoint w t) := by
  simp only [coreEndpoint, List.map_append, List.map_cons, List.map_nil, Action.endpoint_append]
  rfl

theorem exists_eq_append_singleton {α : Type*} {l : List α} (h : l ≠ []) :
    ∃ p a, l = p ++ [a] := by
  rcases List.eq_nil_or_concat l with h' | ⟨p, a, rfl⟩
  · exact absurd h' h
  · exact ⟨p, a, List.concat_eq_append ..⟩

/-- Successful words with a common first letter are comparable under prefixes. -/
theorem coreSuccess_prefix_or (hc : HasSpanColoring K 2) :
    ∀ {q : CoreFamily K} {w₁ w₂ : List (CoreFamily K)} {t : ℕ},
      CoreSuccess (q :: w₁) t → CoreSuccess (q :: w₂) t →
        (q :: w₁) <+: (q :: w₂) ∨ (q :: w₂) <+: (q :: w₁)
  | q, [], w₂, t, _, _ => Or.inl (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
  | q, a :: w₁, [], t, _, _ => Or.inr (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
  | q, a :: w₁, b :: w₂, t, h₁, h₂ => by
    have h₁' := (coreSuccess_cons_iff _ _ _).mp h₁
    have h₂' := (coreSuccess_cons_iff _ _ _).mp h₂
    have ha := ((coreSuccess_cons_iff _ _ _).mp h₁'.2).1
    have hb := ((coreSuccess_cons_iff _ _ _).mp h₂'.2).1
    have hab : a = b := core_unique_after hc q h₁'.1 ha hb
    subst hab
    rcases coreSuccess_prefix_or hc h₁'.2 h₂'.2 with h | h
    · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
    · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

/-- An internal letter of a successful word is a nonleaf of the overlap forest. -/
theorem coreSuccess_internal_nonleaf {w : List (CoreFamily K)} {t : ℕ} (hs : CoreSuccess w t)
    {p s : List (CoreFamily K)} {b : CoreFamily K} (hw : w = p ++ b :: s)
    (hp : p ≠ []) (hs' : s ≠ []) : (coreModel K).Nonleaf b := by
  have hchain := core_success_chain w hs
  have hnodup := core_success_nodup w hs
  obtain ⟨p', a, rfl⟩ := exists_eq_append_singleton hp
  obtain ⟨c, s'', rfl⟩ := List.exists_cons_of_ne_nil hs'
  rw [hw] at hchain hnodup
  have hch : List.IsChain (coreModel K).graph.Adj (p' ++ [a]) ∧ (coreModel K).graph.Adj a b ∧
      (coreModel K).graph.Adj b c ∧ List.IsChain (coreModel K).graph.Adj (c :: s'') := by
    simpa [List.append_assoc] using hchain
  have h1 := hch.2.1
  have h2 := hch.2.2.1
  have hac : a ≠ c := (List.nodup_append.mp hnodup).2.2 a (by simp) c (by simp)
  exact ⟨a, c, h1.symm, h2, hac⟩

/-- The endpoint of a nonempty successful word lies in the lower region of its last letter. -/
theorem coreSuccess_endpoint_lower {w : List (CoreFamily K)} {t : ℕ} (hs : CoreSuccess w t)
    {G : CoreFamily K} (hG : w.getLast? = some G) :
    G.val.start < coreEndpoint w t ∧ coreEndpoint w t ≤ G.val.owner := by
  obtain ⟨p, rfl⟩ : ∃ p, w = p ++ [G] := by
    rcases List.eq_nil_or_concat' w with h | ⟨p, a, rfl⟩
    · simp [h] at hG
    · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at hG
      exact ⟨p, by rw [Option.some_inj.mp hG]⟩
  have h := (coreSuccess_append_singleton p G t).mp hs
  have hb := G.val.shadow_active_bounds ((G.val.shadow_ne_self_iff _).mp h.2)
  rw [coreEndpoint_append_singleton]
  exact ⟨hb.1, hb.2.1⟩

/-- Core families acting nontrivially at a time. -/
def activeAt (K : Finset (ActualFamily xs T)) (t : ℕ) : Finset (CoreFamily K) :=
  univ.filter (fun q => q.val.shadow t ≠ t)

theorem activeAt_card (hc : HasSpanColoring K 2) (t : ℕ) : (activeAt K t).card ≤ 2 := by
  have h := card_le_card_of_injOn (coreColor hc) (s := activeAt K t) (t := range 2)
    (fun q _ => mem_range.mpr (coreColor_lt hc q)) ?_
  · simpa only [card_range] using h
  · intro a ha b hb he
    have ha' := a.val.shadow_active_bounds ((a.val.shadow_ne_self_iff t).mp (mem_filter.mp ha).2)
    have hb' := b.val.shadow_active_bounds ((b.val.shadow_ne_self_iff t).mp (mem_filter.mp hb).2)
    exact core_eq_of_same_color hc
      ⟨a.val.owner_bounds.1.trans ha'.2.2.1, ha'.2.2.2⟩
      ⟨b.val.owner_bounds.1.trans hb'.2.2.1, hb'.2.2.2⟩ he

theorem head_mem_activeAt {w : List (CoreFamily K)} {t : ℕ} (hs : CoreSuccess w t)
    {q : CoreFamily K} (hq : w.head? = some q) : q ∈ activeAt K t := by
  obtain ⟨w', rfl⟩ : ∃ w', w = q :: w' := by
    cases w with
    | nil => simp at hq
    | cons a w' => exact ⟨w', by rw [Option.some_inj.mp hq]⟩
  exact mem_filter.mpr ⟨mem_univ _, ((coreSuccess_cons_iff _ _ _).mp hs).1⟩

/-- Comparable words: two successful words with the same first letter, one a
prefix of the other. If their last letters agree, they are equal. -/
theorem coreSuccess_eq_of_head_last (hc : HasSpanColoring K 2) {w₁ w₂ : List (CoreFamily K)}
    {t : ℕ} (h₁ : CoreSuccess w₁ t) (h₂ : CoreSuccess w₂ t) (hne : w₁ ≠ [])
    (hhead : w₁.head? = w₂.head?) (hlast : w₁.getLast? = w₂.getLast?) : w₁ = w₂ := by
  obtain ⟨q, a, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b, rfl⟩ : ∃ b, w₂ = q :: b := by
    cases w₂ with
    | nil => simp at hhead
    | cons c b => simp only [List.head?_cons, Option.some_inj] at hhead; exact ⟨b, by rw [hhead]⟩
  have key : ∀ {u v : List (CoreFamily K)}, CoreSuccess v t → u ≠ [] → u <+: v →
      u.getLast? = v.getLast? → u = v := by
    intro u v hv hu huv hl
    obtain ⟨s, rfl⟩ := huv
    rcases eq_or_ne s [] with hs | hs
    · simp [hs]
    · exfalso
      obtain ⟨G, hG⟩ := Option.ne_none_iff_exists'.mp (by simpa using hu : u.getLast? ≠ none)
      have hGs : s.getLast? = some G := by
        rw [List.getLast?_append_of_ne_nil _ hs] at hl
        exact hl.symm.trans hG
      have hnd := List.nodup_append.mp (core_success_nodup _ hv)
      exact hnd.2.2 G (List.mem_of_getLast? hG) G (List.mem_of_getLast? hGs) rfl
  rcases coreSuccess_prefix_or hc h₁ h₂ with h | h
  · exact key h₂ (by simp) h hlast
  · exact (key h₁ (by simp) h hlast.symm).symm

/-- A word ending in a leaf, of length at least two, cannot be a proper prefix
of another successful word. -/
theorem coreSuccess_eq_of_head_leaf (hc : HasSpanColoring K 2) {w₁ w₂ : List (CoreFamily K)}
    {t : ℕ} (h₁ : CoreSuccess w₁ t) (h₂ : CoreSuccess w₂ t) (hhead : w₁.head? = w₂.head?)
    (hl₁ : 2 ≤ w₁.length) (hl₂ : 2 ≤ w₂.length)
    (hleaf₁ : ∀ G, w₁.getLast? = some G → ¬ (coreModel K).Nonleaf G)
    (hleaf₂ : ∀ G, w₂.getLast? = some G → ¬ (coreModel K).Nonleaf G) : w₁ = w₂ := by
  have key : ∀ {u v : List (CoreFamily K)}, CoreSuccess v t → 2 ≤ u.length → u <+: v →
      (∀ G, u.getLast? = some G → ¬ (coreModel K).Nonleaf G) → u = v := by
    intro u v hv hu huv hleaf
    obtain ⟨s, rfl⟩ := huv
    rcases eq_or_ne s [] with hs | hs
    · simp [hs]
    · exfalso
      obtain ⟨p, G, rfl⟩ := exists_eq_append_singleton (by
        rintro rfl; simp at hu : u ≠ [])
      have hp : p ≠ [] := by
        rintro rfl
        simp at hu
      exact hleaf G (by simp) (coreSuccess_internal_nonleaf hv (p := p) (s := s) (b := G)
        (by simp [List.append_assoc]) hp hs)
  obtain ⟨q, a, rfl⟩ := List.exists_cons_of_ne_nil (by rintro rfl; simp at hl₁ : w₁ ≠ [])
  obtain ⟨b, rfl⟩ : ∃ b, w₂ = q :: b := by
    cases w₂ with
    | nil => simp at hl₂
    | cons c b => simp only [List.head?_cons, Option.some_inj] at hhead; exact ⟨b, by rw [hhead]⟩
  rcases coreSuccess_prefix_or hc h₁ h₂ with h | h
  · exact key h₂ hl₁ h hleaf₁
  · exact (key h₁ hl₂ h hleaf₂).symm

/-- **Production count at one root.** Points reached from `r` by nonempty
successful words that end in a nonleaf from `Φ`, or in a leaf: at most
`2 |Φ| + 4` of them, whatever words are chosen to reach them. -/
theorem core_root_count (hc : HasSpanColoring K 2) (r : ℕ) (X : Finset ℕ)
    (Φ : Finset (CoreFamily K)) (w : ℕ → List (CoreFamily K))
    (hw : ∀ v ∈ X, w v ≠ [] ∧ CoreSuccess (w v) r ∧ coreEndpoint (w v) r = v)
    (hΦ : ∀ v ∈ X, ∀ G, (w v).getLast? = some G → (coreModel K).Nonleaf G → G ∈ Φ) :
    X.card ≤ 2 * Φ.card + 4 := by
  classical
  let X₁ := X.filter (fun v => ∃ G, (w v).getLast? = some G ∧ (coreModel K).Nonleaf G)
  let X₂ := X.filter (fun v => ¬ ∃ G, (w v).getLast? = some G ∧ (coreModel K).Nonleaf G)
  have hsplit : X.card = X₁.card + X₂.card := (card_filter_add_card_filter_not _).symm
  have headOf : ∀ v ∈ X, ∃ q, (w v).head? = some q := fun v hv =>
    Option.ne_none_iff_exists'.mp (by simpa using (hw v hv).1)
  have lastOf : ∀ v ∈ X, ∃ G, (w v).getLast? = some G := fun v hv =>
    Option.ne_none_iff_exists'.mp (by simpa using (hw v hv).1)
  -- nonleaf endings: inject into (first letter, last letter)
  have h₁ : X₁.card ≤ 2 * Φ.card := by
    let f : ℕ → Option (CoreFamily K) × Option (CoreFamily K) :=
      fun v => ((w v).head?, (w v).getLast?)
    have hmaps : ∀ v ∈ X₁, f v ∈ (activeAt K r).image some ×ˢ Φ.image some := by
      intro v hv
      have hvX := (mem_filter.mp hv).1
      obtain ⟨G, hG, hn⟩ := (mem_filter.mp hv).2
      obtain ⟨q, hq⟩ := headOf v hvX
      refine mem_product.mpr ⟨?_, ?_⟩
      · change (w v).head? ∈ _
        rw [hq]
        exact mem_image_of_mem _ (head_mem_activeAt (hw v hvX).2.1 hq)
      · change (w v).getLast? ∈ _
        rw [hG]
        exact mem_image_of_mem _ (hΦ v hvX G hG hn)
    have hinj : Set.InjOn f X₁ := by
      intro v hv v' hv' he
      have hvX := (mem_filter.mp hv).1
      have hvX' := (mem_filter.mp hv').1
      have he' := Prod.ext_iff.mp he
      have heq := coreSuccess_eq_of_head_last hc (hw v hvX).2.1 (hw v' hvX').2.1 (hw v hvX).1
        he'.1 he'.2
      rw [← (hw v hvX).2.2, ← (hw v' hvX').2.2, heq]
    have := card_le_card_of_injOn f hmaps hinj
    rw [card_product] at this
    have hA := (card_image_le (s := activeAt K r) (f := some)).trans (activeAt_card hc r)
    have hB := card_image_le (s := Φ) (f := some)
    nlinarith
  -- leaf endings: inject into (first letter, whether the word has length one)
  have h₂ : X₂.card ≤ 4 := by
    let f : ℕ → Option (CoreFamily K) × Bool := fun v => ((w v).head?, decide ((w v).length = 1))
    have hmaps : ∀ v ∈ X₂, f v ∈ (activeAt K r).image some ×ˢ (univ : Finset Bool) := by
      intro v hv
      have hvX := (mem_filter.mp hv).1
      obtain ⟨q, hq⟩ := headOf v hvX
      refine mem_product.mpr ⟨?_, mem_univ _⟩
      change (w v).head? ∈ _
      rw [hq]
      exact mem_image_of_mem _ (head_mem_activeAt (hw v hvX).2.1 hq)
    have hinj : Set.InjOn f X₂ := by
      intro v hv v' hv' he
      have hvX := (mem_filter.mp hv).1
      have hvX' := (mem_filter.mp hv').1
      have hleaf : ∀ u ∈ X₂, ∀ G, (w u).getLast? = some G → ¬ (coreModel K).Nonleaf G := by
        intro u hu G hG hn
        exact (mem_filter.mp hu).2 ⟨G, hG, hn⟩
      have he' := Prod.ext_iff.mp he
      have hhead : (w v).head? = (w v').head? := he'.1
      have hlen : decide ((w v).length = 1) = decide ((w v').length = 1) := he'.2
      have heq : w v = w v' := by
        by_cases h1 : (w v).length = 1
        · have h1' : (w v').length = 1 := by simpa [h1] using hlen.symm
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
          obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp h1'
          rw [ha, hb] at hhead ⊢
          simpa using hhead
        · have h1' : ¬ (w v').length = 1 := by simpa [h1] using hlen
          have hl : 2 ≤ (w v).length := by
            have := List.length_pos_of_ne_nil (hw v hvX).1
            omega
          have hl' : 2 ≤ (w v').length := by
            have := List.length_pos_of_ne_nil (hw v' hvX').1
            omega
          exact coreSuccess_eq_of_head_leaf hc (hw v hvX).2.1 (hw v' hvX').2.1 hhead hl hl'
            (hleaf v hv) (hleaf v' hv')
      rw [← (hw v hvX).2.2, ← (hw v' hvX').2.2, heq]
    have := card_le_card_of_injOn f hmaps hinj
    rw [card_product, card_univ, Fintype.card_bool] at this
    have hA := (card_image_le (s := activeAt K r) (f := some)).trans (activeAt_card hc r)
    omega
  omega

end
end SourceCovers
