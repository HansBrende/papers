import BitWord.CompilerPath

namespace BitWord.Compiler
open Geometry
open scoped BigOperators

 theorem stage_inverse {P : ℕ} (T : Stage P) (back : Bool) (x : ℕ) :
     T.act (!back) (T.act back x) = x := by
   cases back
   · exact finiteAct_symm_apply T.endpoint x
   · simpa [Stage.act, oriented] using finiteAct_symm_apply T.endpoint.symm x

 theorem stage_act_injective {P : ℕ} (T : Stage P) (back : Bool) :
     Function.Injective (T.act back) := by
   intro x y h
   have := congrArg (T.act (!back)) h
   simpa only [stage_inverse] using this

 noncomputable def dirty {P : ℕ} (B : ℕ) (ts : Path P) : Finset ℕ := by
   classical
   exact (Finset.range P).filter (fun x => ¬ Clean B ts x)

 @[simp] theorem mem_dirty {P B x : ℕ} {ts : Path P} :
     x ∈ dirty B ts ↔ x < P ∧ ¬ Clean B ts x := by
   classical
   simp only [dirty, Finset.mem_filter, Finset.mem_range]

 theorem dirty_cons {P B : ℕ} (T : Stage P) (ts : Path P) :
     dirty B (T :: ts) = T.bad B ∪ (dirty B ts).image (T.act true) := by
   classical
   ext x
   simp only [mem_dirty, Clean, Finset.mem_union, Finset.mem_image]
   constructor
   · rintro ⟨hxp, h⟩
     by_cases hb : x ∈ T.bad B
     · exact Or.inl hb
     · right
       refine ⟨T.act false x, ⟨finiteAct_lt T.endpoint hxp, ?_⟩, stage_inverse T false x⟩
       exact fun hc => h ⟨hb, hc⟩
   · intro h
     rcases h with hb | ⟨y, ⟨hyp, hy⟩, rfl⟩
     · refine ⟨Finset.mem_range.mp (T.bad_subset_range B hb), ?_⟩
       exact fun hc => hc.1 hb
     · refine ⟨finiteAct_lt T.endpoint.symm hyp, ?_⟩
       intro hc
       have hh := hc.2
       rw [show T.act false (T.act true y) = y from stage_inverse T true y] at hh
       exact hy hh

 theorem dirty_card_cons_le {P B : ℕ} (T : Stage P) (ts : Path P) :
     (dirty B (T :: ts)).card ≤ (T.bad B).card + (dirty B ts).card := by
   rw [dirty_cons]
   exact (Finset.card_union_le _ _).trans_eq (by
     rw [Finset.card_image_of_injective _ (stage_act_injective T true)])

 theorem total_dirty_volume_le {P m : ℕ} (ts : Path P) (B : Fin m → ℕ)
     (hsep : ∀ i j, i < j → volume (B i) ≤ B j) :
     ∑ i, (dirty (B i) ts).card ≤ ts.length * P := by
   induction ts with
   | nil => simp [dirty, Clean]
   | cons T ts ih =>
     calc
       _ ≤ ∑ i : Fin m, ((T.bad (B i)).card + (dirty (B i) ts).card) :=
         Finset.sum_le_sum (fun i _ => dirty_card_cons_le T ts)
       _ = (∑ i : Fin m, (T.bad (B i)).card) + ∑ i : Fin m, (dirty (B i) ts).card := Finset.sum_add_distrib
       _ ≤ P + ts.length * P := Nat.add_le_add (T.total_bad_volume_le B hsep) ih
       _ = (T :: ts).length * P := by simp; ring

 def endpoint {P : ℕ} : Path P → Equiv.Perm (Fin P)
   | [] => Equiv.refl _
   | T :: ts => T.endpoint.trans (endpoint ts)

 theorem endpoint_val {P : ℕ} (ts : Path P) (x : Fin P) :
     (endpoint ts x).val = forward ts x.val := by
   induction ts generalizing x with
   | nil => rfl
   | cons T ts ih =>
     change (endpoint ts (T.endpoint x)).val = forward ts (T.act false x.val)
     rw [ih]
     have he : T.act false x.val = (T.endpoint x).val := by
       simp [Stage.act, finiteAct, oriented, x.isLt]
     rw [he]

end BitWord.Compiler
