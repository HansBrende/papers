import SharedDecoders.CompositionSingleSiteGroup
import SharedDecoders.CompositionAnchoredEndpoint

/-! # The complete single-site strengthening, with arbitrary nonlinear lane mixing -/

namespace SharedDecoders

open scoped CharTwo

variable {d b : ℕ} [NeZero d] [NeZero b]

theorem single_conjugate_no_period (hd : 2 ≤ d) (s : ZMod d)
    (h : ∀ y, singleSite hd (scalarRotation 1
      ((singleSite hd).symm (scalarRotation s y))) =
        scalarRotation s (singleSite hd (scalarRotation 1 ((singleSite hd).symm y)))) : s=0 := by
  have hf : ∃ x : BitWord d, scalarRotation 1 x=x ∧
      singleSite hd x=singleSite hd (fun _ => 1) := ⟨fun _ => 1,rfl,rfl⟩
  obtain ⟨z,hz,he⟩ := fixed_image_preserved (singleSite hd)
    (scalarRotation 1) (scalarRotation s) h hf
  by_contra hs
  have hz1 := scalarRotation_one_fixed z hz 1
  have hh := congrFun he 0
  simp [singleSite,neighborUpdate,scalarRotation,hs,hz1] at hh

theorem single_final_mask_aperiodic {κ : Type*} (hd : 2 ≤ d)
    (p : ZMod d → κ) (U K B H : State d (Fin b → ZMod 2) → State d (Fin b → ZMod 2))
    (hU : Equivariant U) (hB : Equivariant B) (hH : Equivariant H)
    (hK : ClassUniform p K)
    (hexact : ∀ X, U (K (B (wordwise (singleSite hd) (H X)))) = swap X)
    (s : ZMod d) (hp : ∀ c,p (c+s)=p c) : s=0 := by
  obtain ⟨LE,hLE,hcomm⟩ := literal_period_complete hU hB hH hK hexact
  have heq : LE=wordwise (singleSite hd) := Equiv.ext hLE
  subst LE
  apply single_conjugate_no_period hd s
  intro y
  funext j
  let X : State d (Fin b → ZMod 2) := fun _ c _ => y c
  exact congrFun (congrFun (congrFun (hcomm s hp X) 0) j) 0

theorem single_adjacent_classes_distinct {κ : Type*} (hd : 3 ≤ d)
    (p : ZMod d → κ) (K B H : State d (Fin b → ZMod 2) → State d (Fin b → ZMod 2))
    (hK : ClassUniform p K) (hB : Equivariant B) (hH : Equivariant H)
    (hexact : ∀ X, K (B (wordwise (singleSite (by omega : 2 ≤ d)) (H X))) = swap X)
    (c : ZMod d) : p c ≠ p (c+1) := by
  intro he
  apply transitive_pair_impossible (by omega) (0 : ZMod 2)
    (singleSite (by omega : 2 ≤ d)) (singleSite_zero _) p (K ∘ B) H hH
    (hK.comp_equivariant hB) hexact c (c+1) he
  intro x hx y hy
  exact single_adjacent_pair_transitive hd c x y hx hy

/-- A single literal neighbor update cannot be completed by two shared classes.
The group action, its transitivity and the complete-state balance are derived. -/
theorem single_at_most_two_classes_impossible {κ : Type*} [Fintype κ]
    (hd : 3 ≤ d) (hκ : Fintype.card κ ≤ 2)
    (p : ZMod d → κ) (K B H : State d (Fin b → ZMod 2) → State d (Fin b → ZMod 2))
    (hK : ClassUniform p K) (hB : Equivariant B) (hH : Equivariant H)
    (hexact : ∀ X, K (B (wordwise (singleSite (by omega : 2 ≤ d)) (H X))) = swap X) : False := by
  let e : κ ↪ Fin 2 := (Fintype.equivFin κ).toEmbedding.trans (Fin.castLEEmb hκ)
  have hproper : ∀ c, e (p c) ≠ e (p (c+1)) := by
    intro c he
    exact single_adjacent_classes_distinct hd p K B H hK hB hH hexact c (e.injective he)
  have hp : ∀ c, p (c+2)=p c := fun c => e.injective (two_color_period (e ∘ p) hproper c)
  have hper := single_final_mask_aperiodic (by omega : 2 ≤ d) p id K B H
    (by intro s X; rfl) hB hH hK hexact 2 hp
  have hn : (2 : ZMod d) ≠ 0 := by
    simpa using small_index_ne (d := d) 2 0 (by omega) (by omega) (by omega)
  exact hn hper

end SharedDecoders
