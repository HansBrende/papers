import SharedDecoders.CapacityMaskGraphQuotient

/-! # The actual two graph counts of the eight-block structured family -/

namespace SharedDecoders.CapacityMaskStructured

open CapacityMaskGraph

variable {ℓ : ℕ} [NeZero ℓ]

/-- The low coordinate runs fastest, exactly as in `a + ℓ r`. -/
def positionEquiv : (Fin ℓ × Fin 8) ≃ ZMod (8*ℓ) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (ZMod.finEquiv (8*ℓ)).toEquiv)

def position (a : Fin ℓ) (r : Fin 8) : ZMod (8*ℓ) := positionEquiv (a,r)

theorem position_formula (a : Fin ℓ) (r : Fin 8) :
    position a r=(a.val : ZMod (8*ℓ))+(ℓ : ZMod (8*ℓ))*r.val := by
  have he {n : ℕ} [NeZero n] (i : Fin n) : (ZMod.finEquiv n) i=(i.val : ZMod n) := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
      apply Fin.ext
      change i.val=i.val%(n+1)
      exact (Nat.mod_eq_of_lt i.isLt).symm
  change (ZMod.finEquiv (8*ℓ)) (finProdFinEquiv (r,a))=_
  rw [he]
  change (((a.val+ℓ*r.val : ℕ) : ZMod (8*ℓ)))=_
  push_cast
  rfl

@[simp] theorem position_inverse (a : Fin ℓ) (r : Fin 8) :
    positionEquiv.symm (position a r)=(a,r) := positionEquiv.symm_apply_apply _

def seed : Fin 8 → Bool := ![false,true,true,false,true,false,false,true]
def root (z : Bool) : Fin 8 := if z then 1 else 0

@[simp] theorem seed_root (z : Bool) : seed (root z)=z := by cases z <;> decide

def mask (v : Fin ℓ → Bool) (c : ZMod (8*ℓ)) : Bool :=
  v (positionEquiv.symm c).1 ^^ seed (positionEquiv.symm c).2

@[simp] theorem mask_position (v : Fin ℓ → Bool) (a : Fin ℓ) (r : Fin 8) :
    mask v (position a r)=(v a ^^ seed r) := by simp only [mask,position_inverse]

def firstShifts : Finset (ZMod (8*ℓ)) := extendShifts {0} (3*ℓ)
def secondShifts : Finset (ZMod (8*ℓ)) := extendShifts firstShifts 1

omit [NeZero ℓ] in
theorem period : (ℓ : ZMod (8*ℓ))*8=0 := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using ZMod.natCast_self (8*ℓ)

theorem position_shift_three (a : Fin ℓ) (r : Fin 8) :
    position a (r+3)=position a r+3*ℓ := by
  have hp := period (ℓ := ℓ)
  fin_cases r <;> norm_num [position_formula,Fin.val_add] <;> first | (ring; done) | linear_combination -hp

def SeedStep (r t : Fin 8) : Prop :=
  seed r=seed t ∧ (r=t ∨ t=r+3 ∨ r=t+3)

instance (r t : Fin 8) : Decidable (SeedStep r t) := inferInstanceAs (Decidable (_ ∧ _))

/-- Two intermediate high indices give an explicit path of length at most three. -/
theorem seed_path : ∀ r : Fin 8, ∃ i j : Fin 8,
    SeedStep r i ∧ SeedStep i j ∧ SeedStep j (root (seed r)) := by decide

theorem seedStep_connected (v : Fin ℓ → Bool) (a : Fin ℓ) {r t : Fin 8}
    (h : SeedStep r t) : Relation.EqvGen (Link (mask v) firstShifts) (position a r) (position a t) := by
  obtain ⟨hlabel,hpos|hpos|hpos⟩ := h
  · rw [hpos]
    exact .refl _
  · apply Relation.EqvGen.rel
    refine ⟨by simp only [mask_position,hlabel],3*ℓ,?_,0,?_,?_⟩
    · simp [firstShifts,extendShifts]
    · simp [firstShifts,extendShifts]
    · rw [hpos,position_shift_three,add_zero]
  · apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    refine ⟨by simp only [mask_position,hlabel],3*ℓ,?_,0,?_,?_⟩
    · simp [firstShifts,extendShifts]
    · simp [firstShifts,extendShifts]
    · rw [hpos,position_shift_three,add_zero]

theorem connected_to_seed_root (v : Fin ℓ → Bool) (a : Fin ℓ) (r : Fin 8) :
    Relation.EqvGen (Link (mask v) firstShifts) (position a r) (position a (root (seed r))) := by
  obtain ⟨i,j,hri,hij,hjt⟩ := seed_path r
  exact Relation.EqvGen.trans _ _ _ (seedStep_connected v a hri)
    (Relation.EqvGen.trans _ _ _ (seedStep_connected v a hij) (seedStep_connected v a hjt))

theorem connected_same_low (v : Fin ℓ → Bool) (a : Fin ℓ) (r t : Fin 8)
    (h : mask v (position a r)=mask v (position a t)) :
    Relation.EqvGen (Link (mask v) firstShifts) (position a r) (position a t) := by
  have he : seed r=seed t := by
    simpa only [mask_position,Bool.xor_right_inj] using h
  apply Relation.EqvGen.trans _ _ _ (connected_to_seed_root v a r)
  rw [he]
  exact Relation.EqvGen.symm _ _ (connected_to_seed_root v a t)

def lowProjection : ZMod (8*ℓ) →+* ZMod ℓ := ZMod.castHom (Nat.dvd_mul_left ℓ 8) (ZMod ℓ)

@[simp] theorem lowProjection_position (a : Fin ℓ) (r : Fin 8) :
    lowProjection (position a r)=(a.val : ZMod ℓ) := by
  simp [position_formula,lowProjection]

theorem low_of_connected (v : Fin ℓ → Bool) {x y : ZMod (8*ℓ)}
    (h : Relation.EqvGen (Link (mask v) firstShifts) x y) :
    lowProjection x=lowProjection y := by
  induction h with
  | rel x y h =>
    obtain ⟨_,u,hu,w,hw,he⟩ := h
    have hu0 : lowProjection u=0 := by
      simp only [firstShifts,extendShifts,Finset.image_singleton,zero_add,
        Finset.mem_union,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl <;> simp [lowProjection]
    have hw0 : lowProjection w=0 := by
      simp only [firstShifts,extendShifts,Finset.image_singleton,zero_add,
        Finset.mem_union,Finset.mem_singleton] at hw
      rcases hw with rfl|rfl <;> simp [lowProjection]
    have hh := congrArg lowProjection he
    simpa only [map_add,hu0,hw0,add_zero] using hh
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

def classifier (v : Fin ℓ → Bool) (c : ZMod (8*ℓ)) : Fin ℓ × Bool :=
  ((positionEquiv.symm c).1,mask v c)

def colorRoot (v : Fin ℓ → Bool) (a : Fin ℓ) (z : Bool) : ZMod (8*ℓ) :=
  position a (root (v a ^^ z))

@[simp] theorem colorRoot_label (v : Fin ℓ → Bool) (a : Fin ℓ) (z : Bool) :
    mask v (colorRoot v a z)=z := by
  simp only [colorRoot,mask_position,seed_root]
  cases v a <;> cases z <;> rfl

@[simp] theorem classifier_colorRoot (v : Fin ℓ → Bool) (a : Fin ℓ) (z : Bool) :
    classifier v (colorRoot v a z)=(a,z) := by
  unfold classifier
  rw [colorRoot_label]
  simp only [colorRoot,position_inverse]

theorem first_component_count (v : Fin ℓ → Bool) :
    componentCount (mask v) firstShifts=2*ℓ := by
  have he := componentCount_eq_card (mask v) firstShifts (classifier v)
    (by rintro ⟨a,z⟩; exact ⟨colorRoot v a z,classifier_colorRoot v a z⟩) ?_
  · simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm] using he
  intro x y
  obtain ⟨⟨a,r⟩,rfl⟩ := positionEquiv.surjective x
  obtain ⟨⟨b,t⟩,rfl⟩ := positionEquiv.surjective y
  change Relation.EqvGen (Link (mask v) firstShifts) (position a r) (position b t) ↔ _
  constructor
  · intro h
    have hl := low_of_connected v h
    simp only [lowProjection_position] at hl
    have hab : a=b := by
      apply Fin.ext
      have hh := congrArg ZMod.val hl
      simpa only [ZMod.val_natCast_of_lt a.isLt,ZMod.val_natCast_of_lt b.isLt] using hh
    subst b
    simpa only [classifier,← show positionEquiv (a,r)=position a r from rfl,
      ← show positionEquiv (a,t)=position a t from rfl,Equiv.symm_apply_apply] using
      (Prod.ext (rfl : a=a) (label_of_connected h))
  · intro h
    have hab : a=b := by
      simpa only [classifier,Equiv.symm_apply_apply] using congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    subst b
    exact connected_same_low v a r t hc



def bridge (z δ : Bool) : Fin 8 :=
  match z,δ with
  | false,false => 0
  | false,true => 6
  | true,false => 1
  | true,true => 2

theorem bridge_properties (z δ : Bool) :
    seed (bridge z δ)=z ∧ seed (bridge z δ+3)=(z ^^ δ) := by
  cases z <;> cases δ <;> decide

theorem position_neighbor (a b : Fin ℓ) (hab : b.val=a.val+1) (r : Fin 8) :
    position b (r+3)=position a r+(3*ℓ+1) := by
  rw [position_shift_three,position_formula,position_formula,hab,Nat.cast_add,Nat.cast_one]
  ring

omit [NeZero ℓ] in
theorem first_subset_second : firstShifts (ℓ := ℓ)⊆secondShifts := Finset.subset_union_left

theorem neighboring_colors_connected (v : Fin ℓ → Bool) (a b : Fin ℓ)
    (hab : b.val=a.val+1) (z : Bool) :
    Relation.EqvGen (Link (mask v) secondShifts) (colorRoot v a z) (colorRoot v b z) := by
  let r := bridge (v a ^^ z) (v a ^^ v b)
  have hr := bridge_properties (v a ^^ z) (v a ^^ v b)
  have ha : mask v (position a r)=z := by
    rw [mask_position,show seed r=(v a ^^ z) from hr.1]
    cases v a <;> cases z <;> rfl
  have hb : mask v (position b (r+3))=z := by
    rw [mask_position,show seed (r+3)=((v a ^^ z) ^^ (v a ^^ v b)) from hr.2]
    cases v a <;> cases v b <;> cases z <;> rfl
  have hbridge : Link (mask v) secondShifts (position a r) (position b (r+3)) := by
    refine ⟨ha.trans hb.symm,3*ℓ+1,?_,0,?_,?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨3*ℓ,by simp [firstShifts,extendShifts],rfl⟩)
    · exact first_subset_second (by simp [firstShifts,extendShifts])
    · rw [add_zero,position_neighbor a b hab r]
  have hleft := connected_mono first_subset_second
    (connected_same_low v a (root (v a ^^ z)) r (by
      change mask v (colorRoot v a z)=_
      rw [colorRoot_label,ha]))
  have hright := connected_mono first_subset_second
    (connected_same_low v b (r+3) (root (v b ^^ z)) (by
      change _=mask v (colorRoot v b z)
      rw [hb,colorRoot_label]))
  exact Relation.EqvGen.trans _ _ _ hleft
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hbridge) hright)

theorem colorRoot_connected_zero (v : Fin ℓ → Bool) (a : Fin ℓ) (z : Bool) :
    Relation.EqvGen (Link (mask v) secondShifts) (colorRoot v a z) (colorRoot v 0 z) := by
  have hh : ∀ n (hn : n<ℓ), Relation.EqvGen (Link (mask v) secondShifts)
      (colorRoot v ⟨n,hn⟩ z) (colorRoot v 0 z) := by
    intro n
    induction n with
    | zero =>
      intro hn
      have he : (⟨0,hn⟩ : Fin ℓ)=0 := Fin.ext rfl
      rw [he]
      exact .refl _
    | succ n ih =>
      intro hn
      have hn' : n<ℓ := by omega
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (neighboring_colors_connected v ⟨n,hn'⟩ ⟨n+1,hn⟩ rfl z))
        (ih hn')
  exact hh a.val a.isLt

theorem connected_to_colorRoot (v : Fin ℓ → Bool) (x : ZMod (8*ℓ)) :
    Relation.EqvGen (Link (mask v) secondShifts) x (colorRoot v 0 (mask v x)) := by
  obtain ⟨⟨a,r⟩,rfl⟩ := positionEquiv.surjective x
  change Relation.EqvGen _ (position a r) _
  have hh := connected_mono first_subset_second
    (connected_same_low v a r (root (v a ^^ mask v (position a r))) (by
      change _=mask v (colorRoot v a (mask v (position a r)))
      rw [colorRoot_label]))
  exact Relation.EqvGen.trans _ _ _ hh (colorRoot_connected_zero v a _)

theorem second_component_count (v : Fin ℓ → Bool) :
    componentCount (mask v) secondShifts=2 := by
  have he := componentCount_eq_card (mask v) secondShifts (mask v)
    (by intro z; exact ⟨colorRoot v 0 z,colorRoot_label v 0 z⟩) ?_
  · simpa only [Fintype.card_bool] using he
  intro x y
  constructor
  · exact label_of_connected
  · intro hxy
    apply Relation.EqvGen.trans _ _ _ (connected_to_colorRoot v x)
    rw [hxy]
    exact Relation.EqvGen.symm _ _ (connected_to_colorRoot v y)

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]

/-- The exhibited structured mask, actual quotient counts and actual nested
source inequality give the stated bound over every field and all entry lanes. -/
theorem structured_finrank_le (v : Fin ℓ → Bool) {C : Submodule F (State (8*ℓ) A)}
    (h : IsSharedCode F (mask v) C) :
    16*Module.finrank F C≤9*((8*ℓ)*(8*ℓ)*Module.finrank F A)+
      8*(8*ℓ)*Module.finrank F A := by
  have hh := h.four_mul_finrank_le (3*ℓ) 1
  change 4*Module.finrank F C≤2*((8*ℓ)*(8*ℓ)*Module.finrank F A)+
    (8*ℓ)*componentCount (mask v) firstShifts*Module.finrank F A+
    (8*ℓ)*componentCount (mask v) secondShifts*Module.finrank F A at hh
  rw [first_component_count,second_component_count] at hh
  nlinarith only [hh]

end SharedDecoders.CapacityMaskStructured
