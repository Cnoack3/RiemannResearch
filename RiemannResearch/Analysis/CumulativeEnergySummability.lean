import RiemannResearch.LinearAlgebra.FiniteCumulativeCellEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Nonnegative prefix summability and full reset-correction energy

Source: user-provided continuation, Section 15. The reset has zero cumulative
tail; its full squared energy is the finite excess energy. Bounded nonnegative
prefixes are equivalent to summability, but no arithmetic bound is supplied.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.NonnegativeEnergy

/-- A uniform bound on the actual nonnegative prefix energies implies
summability. This does not provide the required arithmetic bound. -/
theorem summable_of_nonnegative_prefix_bound (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (C : ℝ)
    (hbound : ∀ N, (∑ n ∈ Finset.range N, f n) ≤ C) :
    Summable f := by
  apply summable_of_sum_le hf
  intro S
  have hsub : S ⊆ Finset.range (S.sup id + 1) := by
    intro n hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn hnot => hf n)).trans (hbound (S.sup id + 1))

/-- Summability is exactly boundedness of prefixes for nonnegative energies. -/
theorem summable_iff_nonnegative_prefix_bound (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ∃ C : ℝ, ∀ N, (∑ n ∈ Finset.range N, f n) ≤ C := by
  constructor
  · intro hs
    refine ⟨∑' n, f n, ?_⟩
    intro N
    exact Summable.sum_le_tsum (Finset.range N) (fun n hn => hf n) hs
  · rintro ⟨C, hC⟩
    exact summable_of_nonnegative_prefix_bound f hf C hC

end RiemannResearch.Analysis.NonnegativeEnergy

namespace RiemannResearch.LinearAlgebra.CumulativeCellEnergy

/-- The full squared cumulative-energy cost, not merely its finite window. -/
def totalCumulativeEnergy (w a : ℕ → ℝ) : ℝ :=
  ∑' i, w i * cumulative a (i + 1) ^ 2

theorem reset_total_energy (w a : ℕ → ℝ) (N : ℕ) :
    totalCumulativeEnergy w (resetJump a N) = weightedPrefixEnergy w a N := by
  unfold totalCumulativeEnergy
  rw [tsum_eq_sum (s := Finset.range N)]
  · exact weightedPrefixEnergy_reset w a N N le_rfl
  · intro i hi
    have hN : N ≤ i := by simpa using hi
    rw [resetJump_tail_zero a N (i + 1) (by omega)]
    simp

theorem reset_total_correction_energy_exact (N : ℕ) (w b d a : ℕ → ℝ)
    (hw : ∀ i ∈ Finset.range N, w i ≠ 0) :
    totalCumulativeEnergy w (resetJump (optimalJumpCorrection w b a) N) =
      signedCellEnergy N w b d a - freeCellEnergy N w b d := by
  rw [reset_total_energy]
  simpa [correctionEnergy, weightedPrefixEnergy] using
    (correction_energy_exact N w b d a 0 hw)

end RiemannResearch.LinearAlgebra.CumulativeCellEnergy
