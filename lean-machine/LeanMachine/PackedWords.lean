import LeanMachine.IntervalComponents
import LeanMachine.SourceBank
import Mathlib.Data.Sym.Card

/-! Pack successful words of interval-supported actions by their unordered
endpoint labels. An owner is crossed strictly by each nonidentity action.
A forest gives word uniqueness; component-wise injective labels give a
uniform bank independent of the number of components.
-/

namespace LeanMachine.PackedWords

open Classical Finset MonotonePatches SimpleGraph

noncomputable section

structure System (V : Type*) where
  patch : V → Patch
  nonempty : ∀ v, (patch v).left < (patch v).right
  owner : V → ℕ
  crosses : ∀ v t, t ∈ (patch v).action.domain →
    (patch v).action.map t ≤ owner v ∧ owner v < t

namespace System

variable {V : Type*} (S : System V)

def model : ThinIntervals.Model V := ⟨fun v => (S.patch v).left,
  fun v => (S.patch v).right, S.nonempty⟩

abbrev action (v : V) := (S.patch v).action

theorem active_owner {a : V} {t : ℕ} (ha : t ∈ (S.action a).domain) :
    (S.action a).apply t ≤ S.owner a ∧ S.owner a < t := by
  rw [(S.action a).apply_eq ha]; exact S.crosses a t ha

theorem success_owner (w : List V) {t : ℕ}
    (hs : t ∈ Action.success (w.map S.action)) : ∀ v ∈ w, S.owner v < t := by
  induction w generalizing t with
  | nil => simp
  | cons a w ih =>
    have ha := S.active_owner hs.1
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha.2
    · exact (ih hs.2 v hv).trans_le (S.action a |>.apply_le t)

theorem success_pairwise (w : List V) {t : ℕ}
    (hs : t ∈ Action.success (w.map S.action)) :
    w.Pairwise (fun a b => S.owner b < S.owner a) := by
  induction w generalizing t with
  | nil => exact .nil
  | cons a w ih =>
    exact List.pairwise_cons.mpr ⟨fun b hb =>
      (S.success_owner w hs.2 b hb).trans_le (S.active_owner hs.1).1, ih hs.2⟩

theorem success_nodup (w : List V) {t : ℕ}
    (hs : t ∈ Action.success (w.map S.action)) : w.Nodup :=
  (S.success_pairwise w hs).imp (fun h he => by subst he; exact (lt_irrefl _ h))

theorem success_chain (w : List V) {t : ℕ}
    (hs : t ∈ Action.success (w.map S.action)) : w.IsChain S.model.graph.Adj := by
  induction w generalizing t with
  | nil => exact .nil
  | cons a w ih =>
    rcases w with _ | ⟨b, w⟩
    · exact .singleton _
    have ha := (S.patch a).mapsTo hs.1
    rw [← (S.action a).apply_eq hs.1] at ha
    have hb := (S.patch b).domain_subset hs.2.1
    have hn := List.nodup_cons.mp (S.success_nodup (a :: b :: w) hs)
    exact List.IsChain.cons_cons
      ⟨fun h => hn.1 (by simp [h]), ha.1.trans_le hb.2, hb.1.trans_le ha.2⟩ (ih hs.2)

theorem head_last_order {w : List V} (hw : w ≠ [])
    (hp : w.Pairwise (fun a b => S.owner b < S.owner a)) :
    S.owner (w.getLast hw) ≤ S.owner (w.head hw) ∧
    (S.owner (w.head hw) ≤ S.owner (w.getLast hw) → w.head hw = w.getLast hw) := by
  rcases w with _ | ⟨a, w⟩
  · exact (hw rfl).elim
  rcases w with _ | ⟨b, w⟩
  · simp
  have h := (List.pairwise_cons.mp hp).1 ((b :: w).getLast (by simp)) (List.getLast_mem _)
  simpa using And.intro h.le (fun hn => False.elim (not_lt_of_ge hn h))

variable [Fintype V] {Λ : Type*} [Fintype Λ]

omit [Fintype V] in
theorem success_component {w : List V} (hw : w ≠ []) {t : ℕ}
    (hs : t ∈ Action.success (w.map S.action)) {v : V} (hv : v ∈ w) :
    S.model.graph.connectedComponentMk v = S.model.graph.connectedComponentMk (w.head hw) := by
  let p := SimpleGraph.Walk.ofSupport w hw (S.success_chain w hs)
  have hp : v ∈ p.support := by simpa [p] using hv
  obtain ⟨i, hi, hv⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hp
  rw [← hi]
  exact (ConnectedComponent.sound (p.take i).reachable).symm

omit [Fintype V] in
/-- Successful words in a forest are determined by their unordered endpoints.
The owner order chooses the orientation, including one-letter words. -/
theorem word_unique (hforest : S.model.graph.IsAcyclic)
    {v w : List V} (hv : v ≠ []) (hw : w ≠ []) {s t : ℕ}
    (hvs : s ∈ Action.success (v.map S.action)) (hws : t ∈ Action.success (w.map S.action))
    (he : s(v.head hv, v.getLast hv) = s(w.head hw, w.getLast hw)) : v = w := by
  have hvp := S.head_last_order hv (S.success_pairwise v hvs)
  have hwp := S.head_last_order hw (S.success_pairwise w hws)
  have ends : v.head hv = w.head hw ∧ v.getLast hv = w.getLast hw := by
    rcases Sym2.eq_iff.mp he with h | ⟨h₁, h₂⟩
    · exact h
    · have hve := hvp.2 (by rw [h₁, h₂]; exact hwp.1)
      exact ⟨hve.trans h₂, hve.symm.trans h₁⟩
  let p := SimpleGraph.Walk.ofSupport v hv (S.success_chain v hvs)
  let q := (SimpleGraph.Walk.ofSupport w hw (S.success_chain w hws)).copy ends.1.symm ends.2.symm
  have hp : p.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    simpa only [p, SimpleGraph.Walk.support_ofSupport] using S.success_nodup v hvs)
  have hq : q.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    simpa only [q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]
      using S.success_nodup w hws)
  have he' := (hforest.subsingleton_path _ _).elim (⟨p, hp⟩ : S.model.graph.Path _ _) ⟨q, hq⟩
  have := congrArg (fun r : S.model.graph.Path _ _ => r.val.support) he'
  simpa only [p, q, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport] using this

variable (label : V → Λ)

/-- A nonempty successful word with a specified component and unordered labels. -/
def WordAt (c : S.model.Component) (p : Sym2 Λ) (w : List V) : Prop :=
  ∃ hw : w ≠ [], (∃ t, t ∈ Action.success (w.map S.action)) ∧
    S.model.graph.connectedComponentMk (w.head hw) = c ∧
    s(label (w.head hw), label (w.getLast hw)) = p

omit [Fintype V] [Fintype Λ] in
theorem wordAt_unique (hforest : S.model.graph.IsAcyclic)
    (hlabel : ∀ a b, S.model.graph.Reachable a b → label a = label b → a = b)
    {c : S.model.Component} {p : Sym2 Λ} {v w : List V}
    (hv : S.WordAt label c p v) (hw : S.WordAt label c p w) : v = w := by
  obtain ⟨hv, ⟨s, hvs⟩, hvc, hvp⟩ := hv
  obtain ⟨hw, ⟨t, hws⟩, hwc, hwp⟩ := hw
  have vc (a) (ha : a ∈ v) : S.model.graph.connectedComponentMk a = c :=
    (S.success_component hv hvs ha).trans hvc
  have wc (a) (ha : a ∈ w) : S.model.graph.connectedComponentMk a = c :=
    (S.success_component hw hws ha).trans hwc
  have eqs (a) (ha : a ∈ v) (b) (hb : b ∈ w) (he : label a = label b) : a = b :=
    hlabel a b (ConnectedComponent.eq.mp ((vc a ha).trans (wc b hb).symm)) he
  apply S.word_unique hforest hv hw hvs hws
  apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp (hvp.trans hwp.symm) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨eqs _ (List.head_mem hv) _ (List.head_mem hw) h₁,
      eqs _ (List.getLast_mem hv) _ (List.getLast_mem hw) h₂⟩
  · exact Or.inr ⟨eqs _ (List.head_mem hv) _ (List.getLast_mem hw) h₁,
      eqs _ (List.getLast_mem hv) _ (List.head_mem hw) h₂⟩

def chosenWord (c : S.model.Component) (p : Sym2 Λ) : List V :=
  if h : ∃ w, S.WordAt label c p w then h.choose else []

omit [Fintype V] [Fintype Λ] in
theorem chosenWord_spec (c : S.model.Component) (p : Sym2 Λ) :
    S.chosenWord label c p = [] ∨ S.WordAt label c p (S.chosenWord label c p) := by
  unfold chosenWord
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

omit [Fintype V] [Fintype Λ] in
theorem chosenWord_eq (hforest : S.model.graph.IsAcyclic)
    (hlabel : ∀ a b, S.model.graph.Reachable a b → label a = label b → a = b)
    {c : S.model.Component} {p : Sym2 Λ} {w : List V}
    (hw : S.WordAt label c p w) : S.chosenWord label c p = w := by
  have he : ∃ w, S.WordAt label c p w := ⟨w, hw⟩
  rw [chosenWord, dite_eq_left he]
  exact S.wordAt_unique label hforest hlabel he.choose_spec hw

omit [Fintype Λ] in
theorem chosenWord_members (c : S.model.Component) (p : Sym2 Λ)
    {v : V} (hv : v ∈ S.chosenWord label c p) : v ∈ S.model.componentVertices c := by
  rcases S.chosenWord_spec label c p with he | ⟨hw, ⟨t, hs⟩, hc, _⟩
  · simp [he] at hv
  · exact S.model.mem_componentVertices.mpr ((S.success_component hw hs hv).trans hc)

theorem endpoint_component (c : S.model.Component) (w : List V)
    (hw : ∀ v ∈ w, v ∈ S.model.componentVertices c) {t : ℕ}
    (ht : t ∈ Set.Ioc (S.model.componentLeft c) (S.model.componentRight c)) :
    Action.endpoint (w.map S.action) t ∈
      Set.Ioc (S.model.componentLeft c) (S.model.componentRight c) := by
  induction w generalizing t with
  | nil => exact ht
  | cons a w ih =>
    apply ih (fun v hv => hw v (List.mem_cons_of_mem a hv))
    by_cases ha : t ∈ (S.action a).domain
    · rw [(S.action a).apply_eq ha]
      exact S.model.component_span_contains (hw a (List.mem_cons_self ..)) ((S.patch a).mapsTo ha)
    · rwa [(S.action a).apply_eq_self ha]

def wordPatch (c : S.model.Component) (p : Sym2 Λ) : Patch where
  left := S.model.componentLeft c
  right := S.model.componentRight c
  action := Action.successfulAction ((S.chosenWord label c p).map S.action)
  domain_subset := by
    intro t ht
    cases hw : S.chosenWord label c p with
    | nil => simp [hw, Action.successfulAction] at ht
    | cons a w =>
      have hs : t ∈ Action.success ((a :: w).map S.action) := by
        simpa only [hw, List.map_cons, Action.successfulAction, List.cons_ne_nil, ite_false] using ht
      have ha : t ∈ (S.action a).domain := hs.1
      exact S.model.component_span_contains (S.chosenWord_members label c p (by simp [hw]))
        ((S.patch a).domain_subset ha)
  mapsTo := by
    intro t ht
    have hspan : t ∈ Set.Ioc (S.model.componentLeft c) (S.model.componentRight c) := by
      cases hw : S.chosenWord label c p with
      | nil => simp [hw, Action.successfulAction] at ht
      | cons a w =>
        have hs : t ∈ Action.success ((a :: w).map S.action) := by
          simpa only [hw, List.map_cons, Action.successfulAction, List.cons_ne_nil, ite_false] using ht
        have ha : t ∈ (S.action a).domain := hs.1
        exact S.model.component_span_contains (S.chosenWord_members label c p (by simp [hw]))
          ((S.patch a).domain_subset ha)
    exact S.endpoint_component c _ (fun v hv => S.chosenWord_members label c p hv) hspan

def packedMap (p : Sym2 Λ) : ℕ → ℕ := Patch.pack univ (S.wordPatch label · p)

omit [Fintype Λ] in
theorem wordPatches_separated (p : Sym2 Λ) : Patch.Separated univ (S.wordPatch label · p) := by
  intro c _ d _ hcd
  exact S.model.component_spans_disjoint hcd

def bank : SourceBank.Bank := id :: (univ : Finset (Sym2 Λ)).toList.map (S.packedMap label)

theorem bank_length : (S.bank label).length = 1 + (Fintype.card Λ + 1).choose 2 := by
  simp [bank, Sym2.card, Nat.add_comm]

theorem bank_bounded : SourceBank.Bounded (S.bank label)
    (1 + 3 * ((Fintype.card Λ + 1).choose 2 : ℕ)) := by
  intro X _ Y n
  have h := List.sum_le_sum (l := (univ : Finset (Sym2 Λ)).toList)
    (f := fun p => variation (Y ∘ S.packedMap label p) n)
    (g := fun _ => 3 * variation Y n)
    (fun p _ => variation_pack Y univ (S.wordPatch label · p) (S.wordPatches_separated label p) n)
  simp only [List.map_const', List.sum_replicate, Finset.length_toList, card_univ,
    Sym2.card, nsmul_eq_mul] at h
  change variation (Y ∘ id) n +
    (((univ : Finset (Sym2 Λ)).toList.map (S.packedMap label)).map
      (fun a => variation (Y ∘ a) n)).sum ≤ _
  rw [List.map_map]
  change variation Y n +
    (((univ : Finset (Sym2 Λ)).toList).map
      (fun p => variation (Y ∘ S.packedMap label p) n)).sum ≤ _
  calc
    _ ≤ variation Y n + ((Fintype.card Λ + 1).choose 2 : ℕ) * (3 * variation Y n) :=
      add_le_add le_rfl h
    _ = _ := by ring

omit [Fintype Λ] in
theorem packedMap_sound (p : Sym2 Λ) (t : ℕ) :
    S.packedMap label p t ∈ FiniteOrbits.wordOrbit univ S.action t := by
  rcases Patch.pack_cases univ (S.wordPatch label · p) t with he | ⟨c, _, _, he⟩
  · exact ⟨[], by simp, he.symm⟩
  rw [packedMap, he]
  change (Action.successfulAction ((S.chosenWord label c p).map S.action)).apply t ∈ _
  rw [Action.successfulAction_apply]
  by_cases hs : t ∈ Action.success ((S.chosenWord label c p).map S.action)
  · rw [Action.successfulMap, ite_eq_left hs]
    exact ⟨S.chosenWord label c p, by simp, rfl⟩
  · rw [Action.successfulMap, ite_eq_right hs]
    exact ⟨[], by simp, rfl⟩

theorem bank_exact (hforest : S.model.graph.IsAcyclic)
    (hlabel : ∀ a b, S.model.graph.Reachable a b → label a = label b → a = b) (t : ℕ) :
    (SourceBank.values (S.bank label) t : Set ℕ) = FiniteOrbits.wordOrbit univ S.action t := by
  ext u
  constructor
  · intro hu
    obtain ⟨a, ha, rfl⟩ := SourceBank.mem_values.mp hu
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[], by simp, rfl⟩
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact S.packedMap_sound label p t
  · rintro ⟨w, _, rfl⟩
    obtain ⟨v, _, hs, he⟩ := FiniteOrbits.reduce_word S.action w t
    rw [← he]
    by_cases hv : v = []
    · subst v
      exact SourceBank.mem_values.mpr ⟨id, List.mem_cons_self .., rfl⟩
    let c := S.model.graph.connectedComponentMk (v.head hv)
    let p := s(label (v.head hv), label (v.getLast hv))
    have hvp : S.WordAt label c p v := ⟨hv, ⟨t, hs⟩, rfl, rfl⟩
    have hc : t ∈ Set.Ioc (S.model.componentLeft c) (S.model.componentRight c) := by
      cases hve : v with
      | nil => exact (hv hve).elim
      | cons a v' =>
        have hs' : t ∈ Action.success ((a :: v').map S.action) := by simpa only [hve] using hs
        have ha : t ∈ (S.action a).domain := hs'.1
        apply S.model.component_span_contains (v := a) _ ((S.patch a).domain_subset ha)
        apply S.model.mem_componentVertices.mpr
        simp [c, hve]
    apply SourceBank.mem_values.mpr
    refine ⟨S.packedMap label p, ?_, ?_⟩
    · apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨p, by simp, rfl⟩
    · rw [packedMap, Patch.pack_eq_on _ _ (S.wordPatches_separated label p) (mem_univ c) hc]
      change (Action.successfulAction ((S.chosenWord label c p).map S.action)).apply t = _
      rw [Action.successfulAction_apply, S.chosenWord_eq label hforest hlabel hvp]
      exact ite_eq_left hs

end System
end
end LeanMachine.PackedWords
