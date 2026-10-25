import SubcubicMemo.SquareSeed
import SubcubicMemo.LadderClosure
import SubcubicMemo.LadderSpanning

/-! The connected square-covered graph theorem, using a longest ladder. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem ladder_size_le {n : ℕ} (L : Ladder G n) : n ≤ Fintype.card V := by
  have hh := Fintype.card_le_of_injective L.vert L.vert.injective
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
  omega

theorem connected_target (h : Hyp G) (hc : G.Preconnected) :
    Nonempty (G →g circularClique 8 3) := by
  by_contra hn
  obtain ⟨L₀⟩ := three_rung_seed h hc hn
  let S := (range (Fintype.card V+1)).filter fun n => Nonempty (Ladder G n)
  have hmem {n : ℕ} (L : Ladder G n) : n ∈ S :=
    mem_filter.mpr ⟨mem_range.mpr (by have := ladder_size_le L; omega),⟨L⟩⟩
  obtain ⟨n,hnS,hmax⟩ := exists_max_image S id ⟨3,hmem L₀⟩
  have h3 : 3 ≤ n := hmax 3 (hmem L₀)
  obtain ⟨L⟩ := (mem_filter.mp hnS).2
  have hnext : ¬ Nonempty (Ladder G (n+1)) := by
    rintro ⟨L'⟩
    have := hmax (n+1) (hmem L')
    simp only [id_eq] at this
    omega
  obtain ⟨m,rfl⟩ : ∃ m, n=m+3 := ⟨n-3,by omega⟩
  have hcL := L.longest_closed h hc hn hnext
  let U : Finset V := univ.image L.vert
  have hcover : ∀ x, x ∈ U := closed_covers G hc
    (show U.Nonempty from ⟨L.v 0 false,mem_image.mpr ⟨(0,false),mem_univ _,rfl⟩⟩) (by
      intro u hu x hux
      obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_image.mp hu
      obtain ⟨j,c,he⟩ := hcL i b x hux
      exact mem_image.mpr ⟨(j,c),mem_univ _,he.symm⟩)
  apply hn (L.closed_target h ?_)
  intro x
  obtain ⟨p,_,he⟩ := mem_image.mp (hcover x)
  exact ⟨p,he⟩

end SubcubicMemo.Squares
