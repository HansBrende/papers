import SourceCovers.CoreFractionalCover
import SourceCovers.FrozenSourceBank
import LeanMachine.IndexedSourceBank

/-! The exact list bank in the finite-family interface used by recovery and
cyclic freezing. No new bank is chosen, and coincident slots still pay motion. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped BigOperators
noncomputable section

def indexedRawBank (B : Bank) (x : ℕ → ℕ) (i : Fin B.length) (t : ℕ) : ℕ :=
  x (indexed B i t)

theorem indexedRawBank_values (B : Bank) (x : ℕ → ℕ) (t : ℕ) :
    residualBankValues (indexedRawBank B x) t = rawBankValues B x t := by
  rw [rawBankValues, ← indexed_values, image_image]
  rfl

theorem indexedRawBank_variation (B : Bank) (x : ℕ → ℕ) (n : ℕ) :
    (∑ i, MonotonePatches.variation (fun s => (indexedRawBank B x i s : ℝ)) n) =
      cost B (fun s => (x s : ℝ)) n :=
  indexed_cost B (fun s => (x s : ℝ)) n

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

theorem exactSourceBank_nonempty (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) :
    Nonempty (Fin (exactSourceBank (ρ := ρ) hc hM E).length) :=
  indexed_nonempty ((exactSourceBank_exact hc hM hρ E).root_mem 0)

theorem indexedRawBank_root (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ) (t : ℕ) :
    x t ∈ residualBankValues (indexedRawBank (exactSourceBank (ρ := ρ) hc hM E) x) t := by
  rw [indexedRawBank_values]
  exact exactSourceBank_raw_root hc hM hρ E x t

theorem indexedRawBank_range (hc : HasSpanColoring K 2) {M ρ n L : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ)
    (hx : ∀ s ≤ n, x s < L) :
    ∀ i s, s ≤ n → indexedRawBank (exactSourceBank (ρ := ρ) hc hM E) x i s < L := by
  intro i s hs
  have hmem : indexed (exactSourceBank (ρ := ρ) hc hM E) i s ∈
      shadowOrbit (retainedCore K M ρ ∪ E) s := by
    apply (exactSourceBank_exact hc hM hρ E s).subset
    rw [← indexed_values]
    exact mem_image_of_mem _ (mem_univ i)
  exact hx _ ((shadowOrbit_le hmem).trans hs)

end
end SourceCovers
