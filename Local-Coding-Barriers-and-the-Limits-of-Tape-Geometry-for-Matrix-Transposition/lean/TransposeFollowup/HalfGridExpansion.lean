import TransposeFollowup.OverlapExpansion

/-! A half-measure subset of a grid-cell union can use half cells. This
proof-only refinement removes the parity restriction without modifying
the generated graph, its native computation or its expansion constant. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
set_option autoImplicit false

def halfCellEmbedding (n : ℕ) : (Fin n × Fin 2) ↪ Fin (2*n) where
  toFun p:=⟨2*p.1.val+p.2.val,by have := p.1.isLt;have := p.2.isLt;omega⟩
  inj':=by
    intro a b h
    have hv:=congrArg Fin.val h
    change 2*a.1.val+a.2.val=2*b.1.val+b.2.val at hv
    have ha:=a.2.isLt
    have hb:=b.2.isLt
    apply Prod.ext <;> apply Fin.ext <;> omega

def halfCells {n : ℕ} (A : Finset (Fin n)) : Finset (Fin (2*n)) :=
  (A.product Finset.univ).map (halfCellEmbedding n)

theorem halfCells_card {n : ℕ} (A : Finset (Fin n)) : (halfCells A).card=2*A.card := by
  simp [halfCells,Finset.card_product,Nat.mul_comm]

theorem halfCell_subset {n : ℕ} (i : Fin n) (b : Fin 2) :
    gridCell (halfCellEmbedding n (i,b))⊆gridCell i := by
  intro x hx
  change (((2*i.val+b.val : ℕ):ℝ)<((2*n : ℕ):ℝ)*x ∧
    ((2*n : ℕ):ℝ)*x<((2*i.val+b.val : ℕ):ℝ)+1) at hx
  push_cast at hx
  have hb0 : (0:ℝ)≤b.val:=Nat.cast_nonneg _
  have hb1 : (b.val:ℝ)≤1:=by exact_mod_cast (show b.val≤1 by have := b.isLt;omega)
  change ((i.val : ℝ) < (n : ℝ)*x) ∧ ((n : ℝ)*x < (i.val : ℝ)+1)
  constructor <;> nlinarith [hx.1,hx.2]

theorem halfCells_subset {n : ℕ} (A : Finset (Fin n)) : gridCells (halfCells A)⊆gridCells A := by
  intro x hx
  obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hx
  obtain ⟨hjA,hxj⟩:=Set.mem_iUnion.mp hj
  obtain ⟨⟨i,b⟩,hib,rfl⟩:=Finset.mem_map.mp hjA
  have hi : i∈A:=(Finset.mem_product.mp hib).1
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,halfCell_subset i b hxj⟩⟩

theorem gridCells_half_subset {n : ℕ} (hn : 0<n) (A : Finset (Fin n)) (hA : n≤2*A.card) :
    ∃ C : Finset (Fin (2*n)),gridCells C⊆gridCells A ∧ volume.real (gridCells C)=1/2 := by
  have hc : n≤(halfCells A).card:=by rw [halfCells_card];exact hA
  obtain ⟨C,hC,hcard⟩:=Finset.exists_subset_card_eq hc
  refine ⟨C,?_,?_⟩
  · intro x hx
    apply halfCells_subset A
    obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hx
    obtain ⟨hjC,hxj⟩:=Set.mem_iUnion.mp hj
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hC hjC,hxj⟩⟩
  · rw [gridCells_volume_real,hcard]
    have hn' : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
    push_cast
    field_simp

theorem mapImageUnion_mono {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) : Monotone (mapImageUnion F) := by
  intro A D hAD y hy
  obtain ⟨p,x,⟨hxd,hxA⟩,rfl⟩:=Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨p,x,⟨hxd,hAD hxA⟩,rfl⟩

theorem overlap_right_large {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B) (hn : 0<n)
    (hmap : ∀ p,MapsTo (F p).map (F p).domain (Icc (0:ℝ) 1)) (eps : ℝ)
    (hexp : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion F S))
    (A : Finset (Fin n)) (hA : n≤2*A.card) :
    (1+eps)*((n:ℝ)/2)≤(bipartiteRight (overlapEdges F n) A).card := by
  obtain ⟨C,hC,hvol⟩:=gridCells_half_subset hn A hA
  have he:=hexp (gridCells C) (gridCells_measurable C) (hC.trans (gridCells_subset_unit A)) (by rw [hvol])
  have hcover:=(mapImageUnion_mono F hC).trans (mapImageUnion_grid_cover F hn hmap A)
  have hv:=volume_real_le_cells_of_cover _ hcover
  rw [hvol] at he
  have hn' : (0:ℝ)<n:=by exact_mod_cast hn
  have h:=(le_div_iff₀ hn').mp (he.trans hv)
  nlinarith

theorem overlap_right_capped {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B) (hn : 0<n)
    (hmap : ∀ p,MapsTo (F p).map (F p).domain (Icc (0:ℝ) 1)) (eps : ℝ)
    (hexp : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion F S)) (A : Finset (Fin n)) :
    (1+eps)*min (A.card:ℝ) ((n:ℝ)/2)≤(bipartiteRight (overlapEdges F n) A).card := by
  by_cases ha : 2*A.card≤n
  · have ha' : (A.card:ℝ)≤(n:ℝ)/2 := by
      have h : 2*(A.card:ℝ)≤(n:ℝ):=by exact_mod_cast ha
      linarith
    rw [min_eq_left ha']
    exact overlap_right_expansion F hn hmap eps hexp A ha
  · have ha' : (n:ℝ)/2≤(A.card:ℝ) := by
      have h : (n:ℝ)≤2*(A.card:ℝ):=by exact_mod_cast (show n≤2*A.card by omega)
      linarith
    rw [min_eq_right ha']
    exact overlap_right_large F hn hmap eps hexp A (by omega)

end TransposeFollowup
