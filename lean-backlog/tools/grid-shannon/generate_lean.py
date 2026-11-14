#!/usr/bin/env python3
"""Render the saved grid certificate as semantic Lean proof obligations.

No solver is used. The independent exact verifier is replayed, then the
actual helper graph, finite automorphisms, paid recovery steps, and integer
combination are emitted for Lean's kernel to check. Generic polymatroid
proofs are imported from ShannonCertificate rather than regenerated here.
"""

import argparse
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent

PRELUDE = r'''import ShannonCertificate

/-!
# The paid grid Shannon certificate

Generated from the saved 18-term certificate by tools/grid-shannon/generate_lean.py.
Every finite map is checked against the actual residual grid helper relation.
Each certificate inequality follows from polymatroid submodularity, an explicit
coordinate purchase, or a paid recovery step. The final integer combination is
kernel-checked. No exact-recovery, capacity, or symmetry premise is imposed on
the paid theorem. In particular the upper bound is not asserted to be sharp.

The 36 coordinates are the nonincident pairs of nine point rows and six line
columns. A point p has grid coordinates (p / 3, p % 3); lines 0,1,2 fix the first
coordinate and lines 3,4,5 fix the second. The cell indexing is lexicographic.
-/

namespace LeanBacklog.GridCertificate

open Finset MotionDepthCodes SoftRecovery ShannonCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Cell := Fin 36

/-- Actual point-line incidence in the three-by-three grid. -/
def incident (p : Fin 9) (l : Fin 6) : Prop :=
  if l.val < 3 then p.val / 3 = l.val else p.val % 3 = l.val - 3

instance (p : Fin 9) (l : Fin 6) : Decidable (incident p l) := by
  unfold incident
  infer_instance
'''

UNIFORMITY = r'''
private theorem singleton_uniform {h : Finset Cell → ℝ}
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) (v : Cell) :
    h {v} = h {0} := by
  have h1 := hi (vertexAut v) (vertexAut_isAut v) {0}
  simp only [map_singleton] at h1
  change h {vertexAut v 0} = h {0} at h1
  simpa only [vertexAut_zero] using h1

private theorem error_uniform {h : Finset Cell → ℝ}
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) (v : Cell) :
    increment h (nbhd v) v = increment h (nbhd 0) 0 := by
  have hn := hi (vertexAut v) (vertexAut_isAut v) (nbhd 0)
  have hi' := hi (vertexAut v) (vertexAut_isAut v) (insert 0 (nbhd 0))
  rw [(vertexAut_isAut v) 0, vertexAut_zero] at hn
  rw [map_insert] at hi'
  change h (insert (vertexAut v 0) ((nbhd 0).map (vertexAut v).toEmbedding)) =
    h (insert 0 (nbhd 0)) at hi'
  rw [(vertexAut_isAut v) 0, vertexAut_zero] at hi'
  simp only [increment]
  rw [hn, hi']
'''

FINALE = r'''
/-- The paid inequality for the actual 36-coordinate residual helper graph. -/
theorem paid_grid (h : Finset Cell → ℝ) (hh : IsPolymatroid h) :
    30 * h univ ≤ 19 * ∑ v, h {v} + 11 * ∑ v, increment h (nbhd v) v := by
  have hp := paid_invariant (symmetrize nbhd h) (hh.symmetrize nbhd)
    (fun σ hσ S => symmetrize_invariant nbhd h hσ S)
  rwa [symmetrize_univ, sum_symmetrize_singleton, sum_symmetrize_error] at hp

/-- Exact recovery gives the weighted 19/30 bound without singleton caps. -/
theorem rateBound_grid : RateBound nbhd (19 / 30) := by
  intro h hh hv
  have hp := paid_grid h hh
  have he : (∑ v, increment h (nbhd v) v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp only [increment, hv v, sub_self]
  rw [he] at hp
  linarith

/-- Unit scalar capacities give the residual upper bound 114/5. -/
theorem residual_le (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hv : IsValid h nbhd) (hc : ∀ v, h {v} ≤ 1) : h univ ≤ 114 / 5 := by
  have hp := rateBound_grid h hh hv
  have hs : (∑ v, h {v}) ≤ 36 := by
    calc
      _ ≤ ∑ _ : Cell, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hc v)
      _ = 36 := by norm_num
  linarith

end LeanBacklog.GridCertificate

#print axioms LeanBacklog.GridCertificate.paid_grid
#print axioms LeanBacklog.GridCertificate.rateBound_grid
#print axioms LeanBacklog.GridCertificate.residual_le
#print axioms LeanBacklog.GridCertificate.loopless
#print axioms LeanBacklog.GridCertificate.mutual_triangle_free
'''


def generate():
    data = runpy.run_path(str(HERE / "verify_certificate.py"))
    cert = json.loads((HERE / "certificate.json").read_text())
    data["verify"](cert)
    _, cells, _, _, columns, helpers, group = data["host"]()
    perms = sorted(group)
    size, full = 36, (1 << 36) - 1
    image = data["move"]

    def closure(mask):
        return data["closure"](mask, helpers, columns)

    def canonical(mask):
        return min(image(mask, perm) for perm in perms)

    def fs(mask):
        if not mask:
            return "∅"
        if mask == full:
            return "univ"
        return "{" + ", ".join(str(i) for i in range(size) if mask >> i & 1) + "}"

    def steps(start):
        final, path = data["closure_path"](start, helpers, columns)
        current, result = start, []
        for step in path:
            added = step["added_mask"]
            result.append((current, current | added, added))
            current |= added
        assert current == final == closure(start)
        return result

    masks = set()
    for term in cert["terms"]:
        operands = term["sets"]
        if term["kind"] == "submodular":
            a, b = operands
            masks.update((a, b, a & b, closure(a | b)))
        else:
            masks.update(operands)
    orbit_maps = {mask: next(p for p in perms if image(mask, p) == canonical(mask))
                  for mask in sorted(masks) if canonical(mask) != mask}
    vertex_maps = [next(p for p in perms if p[0] == v) for v in range(size)]
    used = sorted(set(orbit_maps.values()) | set(vertex_maps))
    indices = {p: i for i, p in enumerate(used)}
    out = [PRELUDE]
    out.append("def row : Cell → Fin 9 := ![" +
               ", ".join(str(p) for p, _ in cells) + "]\n")
    out.append("def column : Cell → Fin 6 := ![" +
               ", ".join(str(c) for _, c in cells) + "]\n")
    out.append("/-- The twelve actual residual helper cells of each target. -/\n"
               "def nbhd : Cell → Finset Cell := ![\n  " +
               ",\n  ".join(fs(helpers[c]) for _, c in cells) + "]\n")
    out.append(r'''
theorem cells_nonincident : ∀ v, ¬incident (row v) (column v) := by decide
theorem cells_injective : Function.Injective (fun v : Cell => (row v, column v)) := by decide
theorem cells_complete : ∀ p l, ¬incident p l → ∃ v, row v = p ∧ column v = l := by decide
theorem nbhd_eq_incidence : ∀ v, nbhd v =
    univ.filter (fun w => incident (row w) (column v)) := by decide
theorem nbhd_iff (u v : Cell) : u ∈ nbhd v ↔ incident (row u) (column v) := by
  rw [nbhd_eq_incidence]
  simp
theorem nbhd_card : ∀ v, (nbhd v).card = 12 := by decide
theorem loopless : ∀ v, v ∉ nbhd v := by
  intro v
  rw [nbhd_iff]
  exact cells_nonincident v

/-- No three cells are pairwise mutual helpers; distinctness need not be assumed. -/
theorem mutual_triangle_free : ∀ u v : Cell, v ∈ nbhd u → u ∈ nbhd v →
    ∀ w : Cell, w ∈ nbhd u → u ∈ nbhd w → w ∈ nbhd v → v ∈ nbhd w → False := by
  decide
''')
    for number, perm in enumerate(used):
        inverse = [perm.index(i) for i in range(size)]
        out.append(f"private def aut{number} : Equiv.Perm Cell where\n"
                   f"  toFun := ![{', '.join(map(str, perm))}]\n"
                   f"  invFun := ![{', '.join(map(str, inverse))}]\n"
                   "  left_inv := by intro v; revert v; decide\n"
                   "  right_inv := by intro v; revert v; decide\n"
                   f"private theorem aut{number}_isAut : IsAut nbhd aut{number} := by decide\n")
    out.append("private def vertexAut : Cell → Equiv.Perm Cell := ![\n  " +
               ", ".join(f"aut{indices[p]}" for p in vertex_maps) + "]\n")
    out.append("private theorem vertexAut_isAut (v : Cell) : IsAut nbhd (vertexAut v) := by\n"
               "  fin_cases v\n" +
               "".join(f"  · exact aut{indices[p]}_isAut\n" for p in vertex_maps))
    out.append("private theorem vertexAut_zero : ∀ v, vertexAut v 0 = v := by decide\n")
    out.append(UNIFORMITY)
    out.append(r'''
private theorem paid_invariant (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) :
    30 * h univ ≤ 19 * ∑ v, h {v} + 11 * ∑ v, increment h (nbhd v) v := by
  let s := h ({0} : Finset Cell)
  let e := increment h (nbhd 0) 0
  have hs : ∀ v, h {v} = s := singleton_uniform hi
  have he : ∀ v, increment h (nbhd v) v = e := error_uniform hi
''')
    orbit_names = []
    for index, (mask, perm) in enumerate(orbit_maps.items()):
        name = f"o{index}"
        orbit_names.append(name)
        number = indices[perm]
        out.append(f"  have {name} : h {fs(mask)} = h {fs(canonical(mask))} := by\n"
                   f"    have hx := hi aut{number} aut{number}_isAut {fs(mask)}\n"
                   f"    rw [show ({fs(mask)} : Finset Cell).map aut{number}.toEmbedding = "
                   f"{fs(canonical(mask))} by decide] at hx\n"
                   "    exact hx.symm\n")

    def make_purchase(name, target, purchased):
        n = purchased.bit_count()
        out.append(f"  have {name} : h {fs(target)} ≤ h ∅ + {n} * s := by\n"
                   f"    exact purchase hh hs (A := {fs(target)}) (B := ∅) "
                   f"(D := {fs(purchased)}) (n := {n}) (by decide) (by decide)\n")

    def make_closure(name, start):
        path = steps(start)
        for j, (before, after, added) in enumerate(path):
            n = added.bit_count()
            prefix = "simpa only [Nat.cast_one] using (" if n == 1 else "exact "
            suffix = ")" if n == 1 else ""
            out.append(f"  have {name}_{j} : h {fs(after)} ≤ h {fs(before)} + {n} * e := by\n"
                       f"    {prefix}recover_paid hh he (A := {fs(after)}) (B := {fs(before)}) "
                       f"(D := {fs(added)}) (n := {n}) "
                       f"(by decide) (by decide) (by decide){suffix}\n")
        cost = (closure(start) & ~start).bit_count()
        out.append(f"  have {name} : h {fs(closure(start))} ≤ h {fs(start)} + {cost} * e := by\n"
                   + ("    linarith only [" + ", ".join(f"{name}_{j}" for j in range(len(path))) + "]\n"
                      if path else "    simp\n"))
        return cost

    total_purchase = total_error = 0
    for i, term in enumerate(cert["terms"]):
        kind, operands, weight = term["kind"], term["sets"], term["weight"]
        n = cost = 0
        if kind == "normalization":
            a, = operands
            assert a == 0
            out.append(f"  have e{i} : -h ∅ ≤ 0 := by rw [hh.empty]; norm_num\n")
        elif kind == "submodular":
            a, b = operands
            cost = make_closure(f"cl{i}", a | b)
            out.append(f"  have raw{i} : h {fs(a|b)} + h {fs(a&b)} ≤ h {fs(a)} + h {fs(b)} :=\n"
                       "    hh.elemental (by decide) (by decide)\n"
                       f"  have e{i} : h {fs(closure(a|b))} + h {fs(a&b)} ≤ "
                       f"h {fs(a)} + h {fs(b)} + {cost} * e := by\n"
                       f"    linarith only [raw{i}, cl{i}]\n")
        elif kind in ("singleton-cap", "generator-cap"):
            a, = operands
            purchased = a if kind == "singleton-cap" else cert["generator18"]
            make_purchase(f"buy{i}", purchased, purchased)
            cost = make_closure(f"cl{i}", purchased)
            assert closure(purchased) == a
            n = purchased.bit_count()
            out.append(f"  have e{i} : h {fs(a)} ≤ {n} * s + {cost} * e := by\n"
                       f"    linarith only [buy{i}, cl{i}, hh.empty]\n")
        else:
            raise AssertionError(kind)
        total_purchase += weight * n
        total_error += weight * cost
    assert (total_purchase, total_error) == (114, 66)
    out.append("  simp only [" + ", ".join(orbit_names) + "] at " +
               " ".join(f"e{i}" for i in range(len(cert["terms"]))) + "\n")
    out.append("  have certificate : 5 * h univ ≤ 114 * s + 66 * e := by\n"
               "    linear_combination " +
               " +\n      ".join(f"{term['weight']} * e{i}" for i, term in enumerate(cert["terms"])) + "\n")
    out.append(r'''
  have hs_sum : (∑ v, h {v}) = 36 * s := by simp_rw [hs]; simp
  have he_sum : (∑ v, increment h (nbhd v) v) = 36 * e := by simp_rw [he]; simp
  rw [hs_sum, he_sum]
  linarith only [certificate]
''')
    out.append(FINALE)
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE.parents[1] / "GridCertificate.lean")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = generate()
    if args.check:
        assert args.output.read_text() == source
        print("PASS: generated semantic grid certificate is unchanged.")
    else:
        args.output.write_text(source)
        print(f"Wrote {args.output.name}: {len(source.splitlines())} lines.")


if __name__ == "__main__":
    main()
