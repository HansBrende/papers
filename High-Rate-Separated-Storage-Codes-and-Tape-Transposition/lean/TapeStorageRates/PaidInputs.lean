import TapeStorageRates.Conditioning
import MergeDepth.LowAdaptivity
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ragged packet inputs and transposition

An entry has `a` full packets of `s` bits and `r` final bits. Both the payload
and the tail use the same row-major matrix addresses as the native input.
The slice selected from a correct set can have an arbitrary fixed tail pattern.
-/

namespace TapeStorageRates.PaidInputs

open Finset

set_option autoImplicit false

/-- Row-major address of bit `t` of entry `(i,j)`. -/
def matrixAddr {d b : ℕ} (i j : Fin d) (t : Fin b) : Fin (d*d*b) :=
  finProdFinEquiv (finProdFinEquiv (i,j),t)

theorem matrixAddr_val {d b : ℕ} (i j : Fin d) (t : Fin b) :
    (matrixAddr i j t : ℕ) = (i.val*d+j.val)*b+t.val := by
  change t.val + b * (j.val + d * i.val) = _
  ring

@[simp] theorem tpos_matrixAddr {d b : ℕ} (i j : Fin d) (t : Fin b) :
    MergeDepth.tposOf d b (matrixAddr i j t) = matrixAddr j i t := by
  apply Fin.ext
  rw [MergeDepth.tposOf_val, matrixAddr_val, matrixAddr_val]
  exact Transpose.Tape.Impl.tpos_spec j.isLt t.isLt

/-- Split the flat raw address space into packet-and-lane positions and
the separate tail positions, preserving the literal order inside each entry. -/
def raggedAddress (d a s r : ℕ) :
    (Fin (d*d*a) × Fin s) ⊕ Fin (d*d*r) ≃ Fin (d*d*(a*s+r)) :=
  let payload : Fin (d*d*a) × Fin s ≃ Fin (d*d) × Fin (a*s) :=
    ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _)).trans ((Equiv.refl _).prodCongr finProdFinEquiv)
  (payload.sumCongr finProdFinEquiv.symm).trans
    ((Equiv.prodSumDistrib _ _ _).symm.trans
      (((Equiv.refl _).prodCongr finSumFinEquiv).trans finProdFinEquiv))

@[simp] theorem payload_address {d a s : ℕ} (r : ℕ) (i j : Fin d) (h : Fin a) (t : Fin s) :
    raggedAddress d a s r (.inl (matrixAddr i j h,t)) =
      matrixAddr i j (Fin.castAdd r (finProdFinEquiv (h,t))) := by
  simp [raggedAddress, matrixAddr]

@[simp] theorem tail_address {d r : ℕ} (a s : ℕ) (i j : Fin d) (t : Fin r) :
    raggedAddress d a s r (.inr (matrixAddr i j t)) =
      matrixAddr i j (Fin.natAdd (a*s) t) := by
  simp [raggedAddress, matrixAddr]

/-- Physical input address of a packet lane, using the packet's flat coarse address. -/
theorem payload_address_val {d a s : ℕ} (r : ℕ) (q : Fin (d*d*a)) (t : Fin s) :
    (raggedAddress d a s r (.inl (q,t)) : ℕ) =
      q.val / a * (a*s+r) + q.val % a * s + t.val := by
  change t.val + s * (q.val % a) + (a*s+r) * (q.val / a) = _
  ring

/-- Physical input address of a tail lane, using its flat address among the tails. -/
theorem tail_address_val {d r : ℕ} (a s : ℕ) (q : Fin (d*d*r)) :
    (raggedAddress d a s r (.inr q) : ℕ) =
      q.val / r * (a*s+r) + a*s + q.val % r := by
  change a*s + q.val % r + (a*s+r) * (q.val / r) = _
  ring

/-- Native transposition moves a payload packet intact and preserves its bit lane. -/
theorem tpos_payload {d a s : ℕ} (r : ℕ) (q : Fin (d*d*a)) (t : Fin s) :
    MergeDepth.tposOf d (a*s+r) (raggedAddress d a s r (.inl (q,t))) =
      raggedAddress d a s r (.inl (MergeDepth.tposOf d a q,t)) := by
  obtain ⟨⟨e,h⟩, rfl⟩ := (finProdFinEquiv : Fin (d*d) × Fin a ≃ _).surjective q
  obtain ⟨⟨i,j⟩, rfl⟩ := (finProdFinEquiv : Fin d × Fin d ≃ _).surjective e
  change MergeDepth.tposOf d _ (raggedAddress _ _ _ _ (.inl (matrixAddr i j h,t))) =
    raggedAddress _ _ _ _ (.inl (MergeDepth.tposOf d _ (matrixAddr i j h), t))
  simp

/-- Native transposition moves a tail lane to the corresponding transposed entry. -/
theorem tpos_tail {d r : ℕ} (a s : ℕ) (q : Fin (d*d*r)) :
    MergeDepth.tposOf d (a*s+r) (raggedAddress d a s r (.inr q)) =
      raggedAddress d a s r (.inr (MergeDepth.tposOf d r q)) := by
  obtain ⟨⟨e,t⟩, rfl⟩ := (finProdFinEquiv : Fin (d*d) × Fin r ≃ _).surjective q
  obtain ⟨⟨i,j⟩, rfl⟩ := (finProdFinEquiv : Fin d × Fin d ≃ _).surjective e
  change MergeDepth.tposOf d _ (raggedAddress _ _ _ _ (.inr (matrixAddr i j t))) =
    raggedAddress _ _ _ _ (.inr (MergeDepth.tposOf d _ (matrixAddr i j t)))
  simp

abbrev Raw (d b : ℕ) := Fin (d*d*b) → Bool
abbrev Payload (d a s : ℕ) := Fin (d*d*a) → Fin s → Bool

/-- Restrict a native word to its payload packets and its complete tail pattern. -/
def splitWord (d a s r : ℕ) : Raw d (a*s+r) ≃ Payload d a s × Raw d r where
  toFun x := (fun q t => x (raggedAddress d a s r (.inl (q,t))),
              fun q => x (raggedAddress d a s r (.inr q)))
  invFun ut i := Sum.elim (fun p => ut.1 p.1 p.2) ut.2 ((raggedAddress d a s r).symm i)
  left_inv x := by
    funext i
    obtain ⟨p,rfl⟩ := (raggedAddress d a s r).surjective i
    cases p <;> simp
  right_inv ut := by
    rcases ut with ⟨u,z⟩
    simp

@[simp] theorem rebuild_payload {d a s r : ℕ} (u : Payload d a s) (z : Raw d r)
    (q : Fin (d*d*a)) (t : Fin s) :
    (splitWord d a s r).symm (u,z) (raggedAddress d a s r (.inl (q,t))) = u q t := by
  simp [splitWord]

@[simp] theorem rebuild_tail {d a s r : ℕ} (u : Payload d a s) (z : Raw d r)
    (q : Fin (d*d*r)) :
    (splitWord d a s r).symm (u,z) (raggedAddress d a s r (.inr q)) = z q := by
  simp [splitWord]

/-- The payloads whose reconstruction with exactly this tail is in `G`. -/
noncomputable def payloadFibre {d a s r : ℕ} (G : Finset (Raw d (a*s+r)))
    (z : Raw d r) : Finset (Payload d a s) := by
  classical
  exact (G.filter fun x => (splitWord d a s r x).2 = z).image (fun x => (splitWord d a s r x).1)

@[simp] theorem mem_payloadFibre {d a s r : ℕ} {G : Finset (Raw d (a*s+r))}
    {z : Raw d r} {u : Payload d a s} :
    u ∈ payloadFibre G z ↔ (splitWord d a s r).symm (u,z) ∈ G := by
  classical
  constructor
  · intro hu
    obtain ⟨x,hx,hu⟩ := mem_image.mp hu
    obtain ⟨hxG,hz⟩ := mem_filter.mp hx
    have h : splitWord d a s r x = (u,z) := Prod.ext hu hz
    rwa [← h, Equiv.symm_apply_apply]
  · intro h
    exact mem_image.mpr ⟨_, mem_filter.mpr ⟨h, by simp⟩, by simp⟩

@[simp] theorem payloadFibre_univ {d a s r : ℕ} (z : Raw d r) :
    payloadFibre (a := a) (s := s) univ z = univ := by
  ext
  simp

/-- Fixing an attained joint assignment to the `d*d*r` tails leaves at least
`|G| / 2^(d*d*r)` distinct packet payloads. This is an integer bound valid for
every nonempty correct set, including when the all-zero-tail slice is empty. -/
theorem exists_large_payload_fibre {d a s r : ℕ} (G : Finset (Raw d (a*s+r)))
    (hG : G.Nonempty) :
    ∃ z : Raw d r, (payloadFibre (a := a) (s := s) G z).Nonempty ∧
      G.card ≤ 2 ^ (d*d*r) * (payloadFibre (a := a) (s := s) G z).card := by
  classical
  let e := splitWord d a s r
  obtain ⟨z,hz,h⟩ := exists_large_observation_fibre hG (fun x => (e x).2)
  obtain ⟨x,hx,hxz⟩ := mem_image.mp hz
  let F := G.filter fun x => (e x).2 = z
  have hF : F.Nonempty := ⟨x, mem_filter.mpr ⟨hx,hxz⟩⟩
  have hi : Set.InjOn (fun x => (e x).1) F := by
    intro x hx y hy hxy
    exact e.injective (Prod.ext hxy ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm))
  have hcard : (payloadFibre (a := a) (s := s) G z).card = F.card := card_image_iff.mpr hi
  refine ⟨z, hF.image (fun x => (e x).1), ?_⟩
  rw [hcard]
  apply h.trans (Nat.mul_le_mul_right _ _)
  simpa [Raw, Fintype.card_fun] using card_le_univ (G.image fun x => (e x).2)

/-- The absolute loss in bits on a largest common tail is at most the
absolute loss on the original raw cube, even for an arbitrary success set. -/
theorem exists_payload_deficit_le {d a s r : ℕ} (G : Finset (Raw d (a*s+r)))
    (hG : G.Nonempty) :
    ∃ z : Raw d r, (payloadFibre (a := a) (s := s) G z).Nonempty ∧
      ((d*d*a*s : ℕ) : ℝ) - Real.logb 2 (payloadFibre (a := a) (s := s) G z).card ≤
        ((d*d*(a*s+r) : ℕ) : ℝ) - Real.logb 2 G.card := by
  obtain ⟨z,hz,hcard⟩ := exists_large_payload_fibre G hG
  refine ⟨z,hz,?_⟩
  let F := payloadFibre (a := a) (s := s) G z
  have hF : 0 < (F.card : ℝ) := by exact_mod_cast hz.card_pos
  have hg : 0 < (G.card : ℝ) := by exact_mod_cast hG.card_pos
  have hlog : Real.logb 2 G.card ≤ ((d*d*r : ℕ) : ℝ) + Real.logb 2 F.card := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hg).mpr
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hF]
    exact_mod_cast hcard
  change _ - Real.logb 2 F.card ≤ _
  push_cast at hlog ⊢
  linarith

end TapeStorageRates.PaidInputs
