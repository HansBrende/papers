import SharedDecoders.CompositionAnchoredGroup

/-! # A concrete anchored two-class impossibility in every dimension at least three -/

namespace SharedDecoders

variable {d b : ℕ} [NeZero d] [NeZero b]

omit [NeZero d] in
lemma ClassUniform.comp_equivariant {A κ : Type*} {p : ZMod d → κ}
    {K B : State d A → State d A} (hK : ClassUniform p K) (hB : Equivariant B) :
    ClassUniform p (K ∘ B) := by
  obtain ⟨f,hf⟩ := hK
  refine ⟨fun j X => f j (B X),?_⟩
  intro X c i
  change K (B X) i c = f (p c) (B (rot c X)) i
  rw [hf,hB]

/-- Exactness forces a proper coloring of adjacent receiver positions. -/
theorem anchored_adjacent_classes_distinct {κ : Type*} (hd : 3 ≤ d)
    (p : ZMod d → κ) (K B H : State d (Fin b → ZMod 2) → State d (Fin b → ZMod 2))
    (hK : ClassUniform p K) (hB : Equivariant B) (hH : Equivariant H)
    (hexact : ∀ X, K (B (wordwise (anchoredDifference (ZMod 2) d) (H X))) = swap X)
    (c : ZMod d) : p c ≠ p (c+1) := by
  intro he
  apply transitive_pair_impossible (by omega) (0 : ZMod 2)
    (anchoredDifference (ZMod 2) d) anchoredDifference_zero p (K ∘ B) H hH
    (hK.comp_equivariant hB) hexact c (c+1) he
  intro x hx y hy
  exact anchored_adjacent_pair_transitive hd c x y hx hy

omit [NeZero d] in
lemma two_color_period (p : ZMod d → Fin 2)
    (h : ∀ c, p c ≠ p (c+1)) : ∀ c, p (c+2) = p c := by
  intro c
  have h0 := h c
  have h1 := h (c+1)
  have he : c+1+1 = c+2 := by ring
  rw [he] at h1
  have hf (a b e : Fin 2) (hab : a ≠ b) (hbe : b ≠ e) : e=a := by omega
  exact hf _ _ _ h0 h1

/-- The fully concrete all-width endpoint. No transitivity, covariance, balance,
or global invertibility certificate is assumed. -/
theorem anchored_two_classes_impossible (hd : 3 ≤ d)
    (p : ZMod d → Fin 2) (K B H : State d (Fin b → ZMod 2) → State d (Fin b → ZMod 2))
    (hK : ClassUniform p K) (hB : Equivariant B) (hH : Equivariant H)
    (hexact : ∀ X, K (B (wordwise (anchoredDifference (ZMod 2) d) (H X))) = swap X) :
    False := by
  have hp := two_color_period p (anchored_adjacent_classes_distinct hd p K B H hK hB hH hexact)
  have hper := anchored_final_mask_aperiodic p id K B H (by intro s X; rfl) hB hH hK hexact 2 hp
  have hn : (2 : ZMod d) ≠ 0 := by
    simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  exact hn hper

/-- The label type may be any finite set with at most two elements. -/
theorem anchored_at_most_two_classes_impossible {κ : Type*} [Fintype κ]
    (hd : 3 ≤ d) (hκ : Fintype.card κ ≤ 2)
    (p : ZMod d → κ) (K B H : State d (Fin b → ZMod 2) → State d (Fin b → ZMod 2))
    (hK : ClassUniform p K) (hB : Equivariant B) (hH : Equivariant H)
    (hexact : ∀ X, K (B (wordwise (anchoredDifference (ZMod 2) d) (H X))) = swap X) :
    False := by
  let e : κ ↪ Fin 2 := (Fintype.equivFin κ).toEmbedding.trans (Fin.castLEEmb hκ)
  have hproper : ∀ c, e (p c) ≠ e (p (c+1)) := by
    intro c he
    exact anchored_adjacent_classes_distinct hd p K B H hK hB hH hexact c (e.injective he)
  have hp : ∀ c, p (c+2) = p c := fun c =>
    e.injective (two_color_period (e ∘ p) hproper c)
  have hper := anchored_final_mask_aperiodic p id K B H (by intro s X; rfl) hB hH hK hexact 2 hp
  have hn : (2 : ZMod d) ≠ 0 := by
    simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  exact hn hper

end SharedDecoders
