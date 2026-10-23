import BitWord.GeometryOperations

namespace BitWord.Geometry
namespace BlockOperation

 theorem act_inverse (op : BlockOperation) (back : Bool) {x : ℕ}
     (hx : x < op.length) : op.act (!back) (op.act back x) = x := by
   cases op with
   | entries k n hk hn e =>
     have hmod : x % k < k := Nat.mod_lt x hk
     have hdiv : entryMap k (finiteAct (oriented e back)) x / k =
         finiteAct (oriented e back) (x / k) := by
       simp [entryMap, Nat.mul_add_div hk, Nat.div_eq_of_lt hmod]
     have hrem : entryMap k (finiteAct (oriented e back)) x % k = x % k := by
       simp [entryMap]
     simp only [act, entryMap] at ⊢
     change k * finiteAct (oriented e (!back))
       (entryMap k (finiteAct (oriented e back)) x / k) +
       entryMap k (finiteAct (oriented e back)) x % k = x
     rw [hdiv, hrem]
     have hi : finiteAct (oriented e (!back)) (finiteAct (oriented e back) (x / k)) = x / k := by
       cases back
       · exact finiteAct_symm_apply e _
       · simpa [oriented] using finiteAct_symm_apply e.symm (x / k)
     rw [hi]
     exact Nat.div_add_mod x k
   | rotate n hn r =>
     simp only [act, length] at hx ⊢
     have hr : r.val ≤ n := Nat.le_of_lt r.isLt
     have he : n - r.val + r.val = n := Nat.sub_add_cancel hr
     have he' : r.val + (n - r.val) = n := Nat.add_sub_of_le hr
     cases back
     · simp only [rotationAmount, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
       rw [Nat.mod_add_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, he']
       simp [Nat.mod_eq_of_lt hx]
     · simp only [rotationAmount, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
       rw [Nat.mod_add_mod]
       rw [show x + (n - r.val) % n + r.val = x + ((n - r.val) % n + r.val) by omega]
       have hi : ((n - r.val) % n + r.val) % n = 0 := by
         rw [Nat.mod_add_mod, he, Nat.mod_self]
       rw [Nat.add_mod, hi, Nat.add_zero, Nat.mod_mod]
       exact Nat.mod_eq_of_lt hx
   | reverse n hn =>
     simp only [act, length] at hx ⊢
     omega

end BlockOperation
end BitWord.Geometry
