#!/usr/bin/env python3
"""Render the saved Fano certificate as semantic Lean proof obligations.

No solver is used. The existing exact verifier is replayed, then all finite
maps, helper containments and integer weights are emitted for Lean's kernel
to check. The generated file is not trusted merely because this script ran.
"""

import argparse
from contextlib import redirect_stdout
import io
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent

PRELUDE = r'''import ShannonCertificate

/-!
# The paid Fano Shannon certificate

Generated from the saved 33-term certificate by tools/fano-shannon/generate_lean.py.
Every finite map below is proved to be an automorphism of the actual residual
Fano helper relation. Every certificate inequality is derived from polymatroid
submodularity, a coordinate purchase, or a paid recovery step; none is supplied
as an unexplained premise. The final integer combination is kernel-checked.

The ground set is the 28 nonincident point-line pairs. Points and line normals
are the nonzero binary triples in lexicographic order, indexed by Fin 7.
The paid theorem needs no exact recovery, singleton caps or symmetry assumption.
The residual exact-recovery bound is its corollary. Companion modules prove
the full 49-cell contraction, Shannon attainment by explicit polymatroids,
and order value 41. The actual triangle-code realization remains written.
-/

namespace LeanBacklog.FanoCertificate

open Finset MotionDepthCodes SoftRecovery LeanBacklog.ShannonCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Cell := Fin 28

/-- Orthogonality of the nonzero binary triples encoded by p+1 and l+1. -/
def incident (p l : Fin 7) : Prop :=
  (((p.val + 1) % 2) * ((l.val + 1) % 2) +
   (((p.val + 1) / 2) % 2) * (((l.val + 1) / 2) % 2) +
   (((p.val + 1) / 4) % 2) * (((l.val + 1) / 4) % 2)) % 2 = 0

instance (p l : Fin 7) : Decidable (incident p l) := inferInstanceAs
  (Decidable (((p.val + 1) % 2 * ((l.val + 1) % 2) +
    ((p.val + 1) / 2 % 2) * ((l.val + 1) / 2 % 2) +
    ((p.val + 1) / 4 % 2) * ((l.val + 1) / 4 % 2)) % 2 = 0))
'''

GENERIC = r'''private theorem singleton_uniform {h : Finset Cell → ℝ}
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

FINALE = r'''/-- The paid Fano inequality on the actual 28-coordinate residual helper graph. -/
theorem paid_fano (h : Finset Cell → ℝ) (hh : IsPolymatroid h) :
    3 * h univ ≤ 2 * ∑ v, h {v} + ∑ v, increment h (nbhd v) v := by
  have hp := paid_invariant (symmetrize nbhd h) (hh.symmetrize nbhd)
    (fun σ hσ S => symmetrize_invariant nbhd h hσ S)
  rwa [symmetrize_univ, sum_symmetrize_singleton, sum_symmetrize_error] at hp

/-- Exact recovery gives the weighted two-thirds rate bound, without caps. -/
theorem rateBound_fano : RateBound nbhd (2 / 3) := by
  intro h hh hv
  have hp := paid_fano h hh
  have he : (∑ v, increment h (nbhd v) v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp only [increment, hv v, sub_self]
  rw [he] at hp
  linarith

/-- Unit scalar capacities give the residual bound 56/3. -/
theorem residual_le (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hv : IsValid h nbhd) (hc : ∀ v, h {v} ≤ 1) : h univ ≤ 56 / 3 := by
  have hp := rateBound_fano h hh hv
  have hs : (∑ v, h {v}) ≤ 28 := by
    calc
      _ ≤ ∑ _ : Cell, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hc v)
      _ = 28 := by norm_num
  linarith

end LeanBacklog.FanoCertificate

#print axioms LeanBacklog.FanoCertificate.paid_fano
#print axioms LeanBacklog.FanoCertificate.rateBound_fano
#print axioms LeanBacklog.FanoCertificate.residual_le
'''


def generate():
    with redirect_stdout(io.StringIO()):
        data = runpy.run_path(str(HERE / "verify_certificate.py"))
    cert, cells = data["certificate"], data["cells"]
    perms = sorted(data["perms"])
    helpers, columns, rows = data["helpers"], data["cols"], data["rows"]
    closure = data["closure"]
    full = (1 << 28) - 1

    def image(mask, perm):
        return sum(1 << perm[i] for i in range(28) if mask >> i & 1)

    def canonical(mask):
        return min(image(mask, perm) for perm in perms)

    def fs(mask):
        if not mask:
            return "∅"
        if mask == full:
            return "univ"
        return "{" + ", ".join(str(i) for i in range(28) if mask >> i & 1) + "}"

    def steps(start):
        current, result = start, []
        while True:
            old = current
            for H, C in zip(helpers, columns):
                if H & current == H and C & ~current:
                    following = current | C
                    result.append((current, following, following ^ current))
                    current = following
            if current == old:
                assert current == closure(start)
                return result

    masks = set()
    for term in cert["terms"]:
        kind, operands = term["kind"], term["sets"]
        if kind == "submodular":
            a, b = operands
            masks.update((a, b, a & b, closure(a | b)))
        elif kind == "closed-join-increment":
            a, b = operands
            masks.update((a, closure(a | b)))
        elif kind == "row-closure-cap":
            masks.add(operands[0])
        else:
            masks.update(operands)
    orbit_maps = {mask: next(p for p in perms if image(mask, p) == canonical(mask))
                  for mask in sorted(masks) if canonical(mask) != mask}
    vertex_maps = [next(p for p in perms if p[0] == v) for v in range(28)]
    used = sorted(set(orbit_maps.values()) | set(vertex_maps))
    indices = {p: i for i, p in enumerate(used)}
    out = [PRELUDE]
    out.append("def row : Cell → Fin 7 := ![" +
               ", ".join(str(p) for p, _ in cells) + "]\n")
    out.append("def column : Cell → Fin 7 := ![" +
               ", ".join(str(c) for _, c in cells) + "]\n")
    out.append("/-- The twelve residual helper cells of each target. -/\n"
               "def nbhd : Cell → Finset Cell := ![\n  " +
               ",\n  ".join(fs(helpers[c]) for _, c in cells) + "]\n")
    out.append(r'''
theorem cells_nonincident : ∀ v, ¬incident (row v) (column v) := by decide
theorem cells_injective : Function.Injective (fun v : Cell => (row v, column v)) := by decide
theorem cells_complete : ∀ p l, ¬incident p l → ∃ v, row v = p ∧ column v = l := by decide
theorem nbhd_eq_incidence : ∀ v, nbhd v =
    univ.filter (fun w => incident (row w) (column v)) := by decide
''')
    for number, perm in enumerate(used):
        inverse = [perm.index(i) for i in range(28)]
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
    out.append(GENERIC)
    out.append(r'''
private theorem paid_invariant (h : Finset Cell → ℝ) (hh : IsPolymatroid h)
    (hi : ∀ σ, IsAut nbhd σ → ∀ S, h (S.map σ.toEmbedding) = h S) :
    3 * h univ ≤ 2 * ∑ v, h {v} + ∑ v, increment h (nbhd v) v := by
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

    def make_purchase(name, a, b, purchased):
        n = purchased.bit_count()
        proof_prefix = f"simpa only [Nat.cast_{'zero' if n == 0 else 'one'}] using (" if n <= 1 else "exact "
        proof_suffix = ")" if n <= 1 else ""
        out.append(f"  have {name} : h {fs(a)} ≤ h {fs(b)} + {n} * s := by\n"
                   f"    {proof_prefix}purchase hh hs (A := {fs(a)}) (B := {fs(b)}) "
                   f"(D := {fs(purchased)}) (n := {n}) "
                   f"(by decide) (by decide){proof_suffix}\n")

    def make_closure(name, start):
        path = steps(start)
        for j, (before, after, added) in enumerate(path):
            n = added.bit_count()
            proof_prefix = "simpa only [Nat.cast_one] using (" if n == 1 else "exact "
            proof_suffix = ")" if n == 1 else ""
            out.append(f"  have {name}_{j} : h {fs(after)} ≤ h {fs(before)} + {n} * e := by\n"
                       f"    {proof_prefix}recover_paid hh he (A := {fs(after)}) (B := {fs(before)}) "
                       f"(D := {fs(added)}) (n := {n}) "
                       f"(by decide) (by decide) (by decide){proof_suffix}\n")
        cost = (closure(start) & ~start).bit_count()
        out.append(f"  have {name} : h {fs(closure(start))} ≤ h {fs(start)} + {cost} * e := by\n"
                   + ("    linarith only [" + ", ".join(f"{name}_{j}" for j in range(len(path))) + "]\n"
                      if path else "    simp\n"))
        return cost

    total_purchase = total_error = 0
    for i, term in enumerate(cert["terms"]):
        kind, operands, weight = term["kind"], term["sets"], term["weight"]
        if kind == "nonnegative":
            a, = operands
            out.append(f"  have e{i} : -h {fs(a)} ≤ 0 := by\n"
                       f"    have hn := hh.nonneg {fs(a)}\n    linarith\n")
            n = cost = 0
        elif kind == "submodular":
            a, b = operands
            cost = make_closure(f"cl{i}", a | b)
            out.append(f"  have raw{i} : h {fs(a|b)} + h {fs(a&b)} ≤ h {fs(a)} + h {fs(b)} :=\n"
                       "    hh.elemental (by decide) (by decide)\n"
                       f"  have e{i} : h {fs(closure(a|b))} + h {fs(a&b)} ≤ "
                       f"h {fs(a)} + h {fs(b)} + {cost} * e := by\n"
                       f"    linarith only [raw{i}, cl{i}]\n")
            n = 0
        elif kind == "increment":
            a, b = operands
            make_purchase(f"e{i}", a, b, a & ~b)
            n, cost = (a & ~b).bit_count(), 0
        elif kind == "closed-join-increment":
            a, b = operands
            make_purchase(f"buy{i}", a | b, a, b & ~a)
            cost = make_closure(f"cl{i}", a | b)
            n = (b & ~a).bit_count()
            out.append(f"  have e{i} : h {fs(closure(a|b))} ≤ h {fs(a)} + {n} * s + {cost} * e := by\n"
                       f"    linarith only [buy{i}, cl{i}]\n")
        elif kind == "row-closure-cap":
            a, pointmask = operands
            rowset = sum(rows[p] for p in range(7) if pointmask >> p & 1)
            make_purchase(f"buy{i}", rowset, 0, rowset)
            cost = make_closure(f"cl{i}", rowset)
            extra = a & ~closure(rowset)
            make_purchase(f"extra{i}", a, closure(rowset), extra)
            n = rowset.bit_count() + extra.bit_count()
            out.append(f"  have e{i} : h {fs(a)} ≤ {n} * s + {cost} * e := by\n"
                       f"    linarith only [buy{i}, cl{i}, extra{i}, hh.empty]\n")
        else:
            raise AssertionError(kind)
        total_purchase += weight * n
        total_error += weight * cost
    assert total_purchase == 4928 and total_error == 2464
    out.append("  simp only [" + ", ".join(orbit_names) + "] at " +
               " ".join(f"e{i}" for i in range(len(cert["terms"]))) + "\n")
    out.append("  have certificate : 264 * h univ ≤ 4928 * s + 2464 * e := by\n"
               "    linear_combination " +
               " +\n      ".join(f"{term['weight']} * e{i}" for i, term in enumerate(cert["terms"])) + "\n")
    out.append(r'''
  have hs_sum : (∑ v, h {v}) = 28 * s := by simp_rw [hs]; simp
  have he_sum : (∑ v, increment h (nbhd v) v) = 28 * e := by simp_rw [he]; simp
  rw [hs_sum, he_sum]
  linarith only [certificate]
''')
    out.append(FINALE)
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE.parents[1] / "FanoCertificate.lean")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = generate()
    if args.check:
        assert args.output.read_text() == text
        print("PASS: generated semantic Fano certificate is unchanged.")
    else:
        args.output.write_text(text)
        print(f"Wrote {args.output.name}: {len(text.splitlines())} lines.")


if __name__ == "__main__":
    main()
