import BitWord.GeometryStageScales

namespace BitWord
namespace Geometry.Stage
variable {P : ℕ}

 theorem good_image_bins_any (T : Stage P) {B : ℕ} (hB : 0 < B)
     (S : Finset ℕ) (hP : ∀ x ∈ S, x < P)
     (hgood : ∀ x ∈ S, x ∉ T.bad B) :
     (bins B (S.image (T.act false))).card ≤ (bins B S).card * 11 := by
   classical
   let piece := fun j => S.filter (fun x => x / B = j)
   have he : S.image (T.act false) = (bins B S).biUnion
       (fun j => (piece j).image (T.act false)) := by
     rw [← Finset.biUnion_image]
     exact congrArg (fun A : Finset ℕ => A.image (T.act false))
       (Finset.image_biUnion_filter_eq S (fun x => x / B)).symm
   rw [he]
   apply bins_biUnion_card_le
   intro j hj
   apply T.good_image_bins_le (j := j) false hB
   · intro x hx
     have he := (Finset.mem_filter.mp hx).2
     rw [← he]
     exact ⟨Nat.div_mul_le_self x B,
       (Nat.div_lt_iff_lt_mul hB).1 (Nat.lt_succ_self _)⟩
   · intro x hx
     exact hP x (Finset.mem_filter.mp hx).1
   · intro x hx
     exact hgood x (Finset.mem_filter.mp hx).1

end Geometry.Stage

namespace Compiler
open Geometry

abbrev Path (P : ℕ) := List (Stage P)

 def forward {P : ℕ} : Path P → ℕ → ℕ
   | [], x => x
   | T :: ts, x => forward ts (T.act false x)

 def Clean {P : ℕ} (B : ℕ) : Path P → ℕ → Prop
   | [], _ => True
   | T :: ts, x => x ∉ T.bad B ∧ Clean B ts (T.act false x)

 instance {P B : ℕ} (ts : Path P) (x : ℕ) : Decidable (Clean B ts x) := by
   induction ts generalizing x with
   | nil => exact inferInstanceAs (Decidable True)
   | cons T ts ih => unfold Clean; infer_instance

 theorem forward_lt {P : ℕ} (ts : Path P) {x : ℕ} (hx : x < P) :
     forward ts x < P := by
   induction ts generalizing x with
   | nil => exact hx
   | cons T ts ih => exact ih (finiteAct_lt T.endpoint hx)

 theorem clean_forward_bins_le {P B : ℕ} (ts : Path P) (hB : 0 < B)
     (S : Finset ℕ) (hP : ∀ x ∈ S, x < P)
     (hclean : ∀ x ∈ S, Clean B ts x) :
     (bins B (S.image (forward ts))).card ≤ (bins B S).card * 11 ^ ts.length := by
   induction ts generalizing S with
   | nil => simp [forward]
   | cons T ts ih =>
     have ht : ∀ x ∈ S, x ∉ T.bad B := fun x hx => (hclean x hx).1
     have hnewP : ∀ y ∈ S.image (T.act false), y < P := by
       intro y hy
       obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
       exact finiteAct_lt T.endpoint (hP x hx)
     have hnew : ∀ y ∈ S.image (T.act false), Clean B ts y := by
       intro y hy
       obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
       exact (hclean x hx).2
     have hi := ih (S.image (T.act false)) hnewP hnew
     have hs := T.good_image_bins_any hB S hP ht
     have he : S.image (forward (T :: ts)) =
         (S.image (T.act false)).image (forward ts) := by
       simp [forward, Finset.image_image, Function.comp_def]
     rw [he]
     calc
       _ ≤ (bins B (S.image (T.act false))).card * 11 ^ ts.length := hi
       _ ≤ ((bins B S).card * 11) * 11 ^ ts.length := Nat.mul_le_mul_right _ hs
       _ = (bins B S).card * 11 ^ (T :: ts).length := by
         simp [Nat.pow_succ]; ring

end Compiler
end BitWord
