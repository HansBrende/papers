import TransposeFollowup.TimedRowWalk

namespace TransposeFollowup.TimedRowWalk
set_option autoImplicit false
variable {q : ℕ}

theorem locate (rows : List (OpcodeDecoder.Ops q)) (hne : rows≠[]) (stride offset t : ℕ)
    (hs : 0<stride) (hl : offset ≤ t) (hu : t ≤ offset+stride*rows.length) :
    ∃ front tail ops s,rows=front++ops::tail ∧ s ≤ stride ∧ t=offset+stride*front.length+s := by
  let d:=t-offset
  let j:=min (d/stride) (rows.length-1)
  have hlen : 0<rows.length:=List.length_pos_iff.mpr hne
  have hj : j<rows.length:=lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
  have hjdiv : j ≤ d/stride:=Nat.min_le_left _ _
  have hjmul : stride*j ≤ d:=by
    have hm:=Nat.mul_le_mul_left stride hjdiv
    have hd:=Nat.div_mul_le_self d stride
    nlinarith
  have hdtop : d ≤ stride*(j+1) := by
    by_cases hlt : d/stride<rows.length
    · have he : j=d/stride:=Nat.min_eq_left (by omega)
      have hm:=Nat.mod_lt d hs
      have hd:=Nat.mod_add_div d stride
      rw [he]
      nlinarith
    · have he : j=rows.length-1:=Nat.min_eq_right (by omega)
      have hd : d ≤ stride*rows.length:=by dsimp [d];omega
      have he' : j+1=rows.length:=by rw [he];omega
      rwa [he']
  let front:=rows.take j
  let tail:=rows.drop (j+1)
  let ops:=rows[j]
  have hf : front.length=j:=by simp only [front,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)]
  refine ⟨front,tail,ops,d-stride*j,?_,by nlinarith [Nat.sub_add_cancel hjmul],?_⟩
  · dsimp only [front,tail,ops]
    rw [← List.drop_eq_getElem_cons hj,List.take_append_drop]
  · rw [hf]
    dsimp [d] at hjmul ⊢
    omega

theorem rowwise_eq (R stride delay offset : ℕ) (hs : delay+5*R ≤ stride) (hstride : 0<stride)
    (rows : List (OpcodeDecoder.Ops q)) (hne : rows≠[]) (p : Fin q) (h : ℕ → ℤ)
    (hrow : ∀ front tail ops,rows=front++ops::tail → ∀ s,s ≤ stride →
      h (offset+front.length*stride+s)=displacement R front p+(ops p).direction*cappedRamp (4*R) R (s-delay))
    (t : ℕ) (hl : offset ≤ t) (hu : t ≤ offset+stride*rows.length) :
    h t=walk R stride delay offset rows p t := by
  obtain ⟨front,tail,ops,s,he,hss,ht⟩:=locate rows hne stride offset t hstride hl hu
  have ha:=hrow front tail ops he s hss
  have hb:=at_row R stride delay offset hs front tail ops p s hss
  rw [← he,← ht] at hb
  have ht' : offset+front.length*stride+s=t:=by rw [Nat.mul_comm front.length stride];exact ht.symm
  rw [ht'] at ha
  exact ha.trans hb.symm

end TransposeFollowup.TimedRowWalk
