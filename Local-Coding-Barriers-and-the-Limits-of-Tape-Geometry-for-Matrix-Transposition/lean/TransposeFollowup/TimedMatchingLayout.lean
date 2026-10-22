import TransposeFollowup.TimedMatchingSchedule
import TransposeFollowup.ExcursionTransfer

namespace TransposeFollowup.NestedMatchingPages
open Classical Transpose.Tape
set_option autoImplicit false
variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj] (D : NestedMatchingPages G k)

theorem timed_nestedExcursion (r K stride offset delay : ℕ) (hr : 0<r) (hK : 0<K)
    (hs : 7*(K*r) ≤ stride) (e : G.edgeFinset) :
    NestedExcursion r K (timedStart stride offset delay (D.src e)+K*r)
      (timedStart stride offset delay (D.dst e)+K*r) (D.timedBase r K stride offset delay hr hK hs e)
      (D.timedWalk (K*r) stride offset delay (Nat.mul_pos hK hr) hs (D.page e)) := by
  let W:=D.timedSchedule (K*r) stride offset delay (Nat.mul_pos hK hr) hs
  have ho : W.opening e=timedStart stride offset delay (D.src e)+K*r:=rfl
  have hc : W.closing e=timedStart stride offset delay (D.dst e)+K*r:=rfl
  have hL : 4*(K*r) ≤ 7*(K*r):=by omega
  refine ⟨hr,hK,?_,?_,?_,?_⟩
  · simpa only [ho,hc,Nat.mul_assoc] using W.self_gap e
  · intro t ha ht
    have hw:=W.walk_rise hL e ha (by simpa only [ho,Nat.mul_assoc] using ht)
    rw [ho] at hw
    change W.walk (4*(K*r)) (W.page e) t=_
    rw [hw]
    dsimp [timedBase,W]
    ring
  · intro t ha hc
    have hw:=W.walk_middle hL e (by simpa only [ho,Nat.mul_assoc] using ha) hc
    change _ ≤ W.walk (4*(K*r)) (W.page e) t
    convert hw using 1
    dsimp [timedBase,W]
    ring
  · intro t hct ht
    have hw:=W.walk_fall hL e hct (by simpa only [hc,Nat.mul_assoc] using ht)
    rw [hc] at hw
    change W.walk (4*(K*r)) (W.page e) t=_
    rw [hw]
    dsimp [timedBase,W]
    ring

theorem timed_base_separated (r K stride offset delay : ℕ) (hr : 0<r) (hK : 0<K)
    (hs : 7*(K*r) ≤ stride) (e f : G.edgeFinset) (hne : e≠f) (hp : D.page e=D.page f) :
    D.timedBase r K stride offset delay hr hK hs e+4*K ≤ D.timedBase r K stride offset delay hr hK hs f ∨
    D.timedBase r K stride offset delay hr hK hs f+4*K ≤ D.timedBase r K stride offset delay hr hK hs e := by
  let W:=D.timedSchedule (K*r) stride offset delay (Nat.mul_pos hK hr) hs
  have hgap:=W.gap_pos
  have bound : ∀ e f,W.opening e<W.opening f → W.page e=W.page f →
      D.timedBase r K stride offset delay hr hK hs e+4*K ≤ D.timedBase r K stride offset delay hr hK hs f := by
    intro e f ho hpage
    have hd:=W.depth_strict hpage ho
    have hdi : (W.depth e:ℤ)+1 ≤ W.depth f:=by exact_mod_cast hd
    have hm:=mul_le_mul_of_nonneg_left hdi (by positivity : 0 ≤ 4*(K:ℤ))
    dsimp [timedBase,W] at *
    nlinarith
  rcases W.nested e f hne hp with hg|hg
  · exact Or.inl (bound e f (by omega) hp)
  · exact Or.inr (bound f e (by omega) hp.symm)

noncomputable def timedLayout (r K stride offset delay : ℕ) (hr : 0<r) (hK : 0<K)
    (hs : delay+7*(K*r) ≤ stride) :
    ExcursionLayout G r K k (timedHorizon (v:=v) stride offset)
      (D.timedWalk (K*r) stride offset delay (Nat.mul_pos hK hr) (by omega)) where
  r_pos:=hr
  K_pos:=hK
  start:=timedStart stride offset delay
  separated i j hne:=by
    have hvne : i.val≠j.val:=fun he => hne (Fin.ext he)
    rcases lt_or_gt_of_ne hvne with h|h
    · left;have hg:=timedStart_gap stride offset delay h
      have hh : 7*K*r ≤ stride:=by nlinarith
      omega
    · right;have hg:=timedStart_gap stride offset delay h
      have hh : 7*K*r ≤ stride:=by nlinarith
      omega
  within i:=by simpa only [Nat.mul_assoc] using timedStart_within (K*r) stride offset delay hs i
  src:=D.src
  dst:=D.dst
  edge_eq:=D.edge_eq
  page:=D.page
  base:=D.timedBase r K stride offset delay hr hK (by omega)
  excursion:=D.timed_nestedExcursion r K stride offset delay hr hK (by omega)
  slabs:=D.timed_base_separated r K stride offset delay hr hK (by omega)

theorem timed_cutIneq (r K stride offset delay : ℕ) (hr : 0<r) (hK : 0<K)
    (hs : delay+7*(K*r) ≤ stride)
    (eta : ℝ) (heta : 0<eta) (hexp : ∀ S : Finset (Fin v),2*S.card ≤ v → eta*S.card ≤ (outsideNeighbors G S).card)
    (q : ℕ) (hdegree : ∀ i,G.degree i ≤ q) (hstretch : 4 ≤ (4*K-1:ℕ)*eta) (hheads : 4*(q:ℝ) ≤ 3*k*eta)
    (hv : 2 ≤ v) (n cellBits : ℕ) (hn : n ≤ 2*v) (hscale : n*Transpose.entryBits n ≤ r*cellBits) :
    CutIneq n cellBits r (timedHorizon (v:=v) stride offset) 0 0
      (D.timedWalk (K*r) stride offset delay (Nat.mul_pos hK hr) (by omega)) :=
  (D.timedLayout r K stride offset delay hr hK hs).cutIneq eta heta
    (by simpa only [Fintype.card_fin] using hexp) q hdegree hstretch hheads
    (by simpa only [Fintype.card_fin] using hv) n cellBits (by simpa only [Fintype.card_fin] using hn) hscale

end TransposeFollowup.NestedMatchingPages
