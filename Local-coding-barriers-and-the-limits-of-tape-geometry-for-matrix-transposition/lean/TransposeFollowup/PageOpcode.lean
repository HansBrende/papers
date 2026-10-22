import TransposeFollowup.MatchingPageDegree

/-! Three-symbol page records and their exact event meaning. A matching page
has at most one incident edge at a vertex, so an opening and closing cannot
be collapsed into the same record. -/

namespace TransposeFollowup

inductive PageOpcode where
  | idle
  | openEdge
  | closeEdge
  deriving DecidableEq, Repr

def PageOpcode.direction : PageOpcode → ℤ
  | .idle => 0
  | .openEdge => 1
  | .closeEdge => -1

namespace NestedMatchingPages

open Classical
set_option autoImplicit false

variable {v k : ℕ} {G : SimpleGraph (Fin v)} [DecidableRel G.Adj]
    (D : NestedMatchingPages G k)

def SourceEvent (u : Fin v) (p : Fin k) : Prop := ∃ e, D.src e = u ∧ D.page e = p

def TargetEvent (u : Fin v) (p : Fin k) : Prop := ∃ e, D.dst e = u ∧ D.page e = p

theorem source_unique {u : Fin v} {p : Fin k} {e f : G.edgeFinset}
    (he : D.src e = u ∧ D.page e = p) (hf : D.src f = u ∧ D.page f = p) : e = f := by
  apply D.shared_vertex_same_page (he.2.trans hf.2.symm) u
  · rw [← D.edge_eq e, Sym2.mem_iff]
    exact Or.inl he.1.symm
  · rw [← D.edge_eq f, Sym2.mem_iff]
    exact Or.inl hf.1.symm

theorem target_unique {u : Fin v} {p : Fin k} {e f : G.edgeFinset}
    (he : D.dst e = u ∧ D.page e = p) (hf : D.dst f = u ∧ D.page f = p) : e = f := by
  apply D.shared_vertex_same_page (he.2.trans hf.2.symm) u
  · rw [← D.edge_eq e, Sym2.mem_iff]
    exact Or.inr he.1.symm
  · rw [← D.edge_eq f, Sym2.mem_iff]
    exact Or.inr hf.1.symm

theorem events_disjoint (u : Fin v) (p : Fin k) : ¬(D.SourceEvent u p ∧ D.TargetEvent u p) := by
  rintro ⟨⟨e, he, hep⟩, ⟨f, hf, hfp⟩⟩
  have hef : e = f := by
    apply D.shared_vertex_same_page (hep.trans hfp.symm) u
    · rw [← D.edge_eq e, Sym2.mem_iff]
      exact Or.inl he.symm
    · rw [← D.edge_eq f, Sym2.mem_iff]
      exact Or.inr hf.symm
  subst f
  have hval := congrArg Fin.val (he.trans hf.symm)
  have := D.forward e
  omega

noncomputable def opcode (u : Fin v) (p : Fin k) : PageOpcode :=
  if D.SourceEvent u p then .openEdge else if D.TargetEvent u p then .closeEdge else .idle

theorem opcode_open_iff (u : Fin v) (p : Fin k) :
    D.opcode u p = .openEdge ↔ D.SourceEvent u p := by
  unfold opcode
  split_ifs <;> simp_all

theorem opcode_close_iff (u : Fin v) (p : Fin k) :
    D.opcode u p = .closeEdge ↔ D.TargetEvent u p := by
  have hd := D.events_disjoint u p
  unfold opcode
  split_ifs <;> simp_all

theorem opcode_idle_iff (u : Fin v) (p : Fin k) :
    D.opcode u p = .idle ↔ ¬D.SourceEvent u p ∧ ¬D.TargetEvent u p := by
  unfold opcode
  split_ifs <;> simp_all

theorem opcode_direction (u : Fin v) (p : Fin k) :
    (D.opcode u p).direction =
      (if D.SourceEvent u p then (1 : ℤ) else 0) - (if D.TargetEvent u p then 1 else 0) := by
  have hd := D.events_disjoint u p
  unfold opcode
  split_ifs <;> simp_all [PageOpcode.direction]

end NestedMatchingPages
end TransposeFollowup
