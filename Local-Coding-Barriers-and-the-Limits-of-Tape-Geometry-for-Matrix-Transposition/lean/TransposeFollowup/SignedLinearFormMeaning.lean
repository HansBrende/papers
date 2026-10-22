import TransposeFollowup.SignedLinearFormRun
import TransposeFollowup.SourceEndpointsMeaning

/-! The prepared endpoint triples satisfy every fit premise of the native
linear form. Both numerator and denominator components at both endpoints
are covered, even when the clipped interval is empty. This theorem calls
one linear form; the four-call image controller is not supplied here. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler SignedComponents
set_option autoImplicit false

def coefficients (F : RationalMobius) (denominator : Bool) : ℤ × ℤ :=
  if denominator then (F.integralC,F.integralD) else (F.integralA,F.integralB)

def imageComponent (F : RationalMobius) (p : ℤ × ℤ) (denominator : Bool) : Pair :=
  if denominator then (F.imageComponents (RationalMobius.endpointComponents p)).2
  else (F.imageComponents (RationalMobius.endpointComponents p)).1

theorem image_components (F : RationalMobius) (p : ℤ × ℤ) (hp : 0≤p.2) (denominator : Bool) :
    components (coefficients F denominator).1 (coefficients F denominator).2
      p.1.toNat (-p.1).toNat p.2.toNat=imageComponent F p denominator := by
  have hz : (-p.2).toNat=0 := by omega
  cases denominator <;> simp [coefficients,imageComponent,components_spec,
    RationalMobius.imageComponents,RationalMobius.endpointComponents,Pair.ofInt,hz]

theorem image_component_bound (F : RationalMobius) {N : ℕ} (i : Fin N) (upper denominator : Bool) :
    (imageComponent F (if upper then F.rightPair i else F.leftPair i) denominator).mass ≤
      F.integerOperandConstant*(N+1) := by
  have h := F.componentImage_endpoint_bounds i
  cases upper <;> cases denominator
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

def endpointWords (F : RationalMobius) (source iw : List Bool) (upper : Bool) : Fin 3 → List Bool :=
  SourceEndpoints.outputWords (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F)
    (SourceEndpoints.negative F) (PaddedWord.word (PaddedWord.commonConstant F) id source) iw upper

theorem endpointWords_length (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (upper : Bool) (j : Fin 3) :
    (endpointWords F source iw upper j).length=
      (PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  apply SourceEndpoints.outputWords_length _ _ _ _ _ _ hl
  rw [PaddedWord.word_length]
  unfold PaddedWord.commonConstant
  omega

theorem endpoint_components (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper denominator : Bool) :
    let w := endpointWords F source iw upper
    components (coefficients F denominator).1 (coefficients F denominator).2
      (Counter.value (w 0)) (Counter.value (w 1)) (Counter.value (w 2))=
      imageComponent F (if upper then F.rightPair i else F.leftPair i) denominator := by
  dsimp only
  have hx := SourceEndpoints.rational_words F source i iw hl hv upper
  change (Counter.value (endpointWords F source iw upper 0),Counter.value (endpointWords F source iw upper 1),
    Counter.value (endpointWords F source iw upper 2))=_ at hx
  rcases Prod.mk.inj hx with ⟨h0,hrest⟩
  rcases Prod.mk.inj hrest with ⟨h1,h2⟩
  rw [h0,h1,h2]
  apply image_components
  cases upper
  · exact (F.leftPair_den_pos i).le
  · exact (F.rightPair_den_pos i).le

theorem endpoint_mass_fits (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper denominator : Bool) :
    let w := endpointWords F source iw upper
    (components (coefficients F denominator).1 (coefficients F denominator).2
      (Counter.value (w 0)) (Counter.value (w 1)) (Counter.value (w 2))).mass<2^(w 0).length := by
  dsimp only
  rw [endpoint_components F source i iw hl hv upper denominator,endpointWords_length F source iw hl upper 0]
  apply lt_of_le_of_lt (image_component_bound F i upper denominator)
  rw [PaddedWord.word_length]
  apply SeedMultiple.common_small_multiple_fits F source _ _ _ le_rfl
  nlinarith [F.integerOperandConstant_pos]

theorem rational_complete_trace (F : RationalMobius) (source : List Bool)
    (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper denominator : Bool) (pos : Port → ℤ) :
    let uv := coefficients F denominator
    let xs := endpointWords F source iw upper
    ∃ t≤budget uv.1 uv.2 (PaddedWord.word (PaddedWord.commonConstant F) id source).length,
      ∃ w : Bool → List Bool,
        Trace uv.1 uv.2 t (cfg (.init 0 (.init (.erase 0))) (initial xs) pos)
          (cfg .done (final uv.1 uv.2 xs) pos) ∧
        (∀ b,(final uv.1 uv.2 xs).out b=Counter.marked (w b)) ∧
        (∀ b,(w b).length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) ∧
        Pair.mk (Counter.value (w false)) (Counter.value (w true))=
          imageComponent F (if upper then F.rightPair i else F.leftPair i) denominator := by
  dsimp only
  have hlen := endpointWords_length F source iw hl upper
  have heq (j : Fin 3) : (endpointWords F source iw upper j).length=
      (endpointWords F source iw upper 0).length := (hlen j).trans (hlen 0).symm
  obtain ⟨t,ht,w,htr,hout,hsize,hvalue⟩ := exact_components
    (coefficients F denominator).1 (coefficients F denominator).2 (endpointWords F source iw upper)
    heq (endpoint_mass_fits F source i iw hl hv upper denominator) pos
  rw [hlen 0] at ht hsize
  refine ⟨t,ht,w,htr,hout,hsize,?_⟩
  rw [← components_spec] at hvalue
  exact hvalue.trans (endpoint_components F source i iw hl hv upper denominator)

end TransposeFollowup.SignedLinearForm
