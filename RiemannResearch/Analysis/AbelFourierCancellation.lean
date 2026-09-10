import RiemannResearch.Analysis.AbelCancellationMultiplier
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite Fourier cancellation and complete boundary-energy transfer

Source: `FourierBridgeUniformSignedEnergy20260910.md`, Sections 5–6,
September 10, 2026. This module formalizes the infinite-series deduction
from the separate scalar Fourier expansions to the exact actual remainder,
and transfers that identification to the complete boundary energy.

The Fourier expansions of the arithmetic family and comparison vector are
explicit hypotheses. This module does not prove those analytic hypotheses,
the residue-kernel continuation, Fourier reconstruction of periodized tents,
or the uniform Mertens-based arithmetic energy estimate. In particular, its
theorems are conditional bridges, not an unconditional proof of the full
Fourier theorem or of RH. There are no additional axioms or proof holes.

-/

namespace RiemannResearch.Analysis

open scoped BigOperators
noncomputable section

/-- Infinite cancellation of the zero-frequency term, with the main and
comparison Fourier series kept separate until after their convergence has
been supplied. This extends the finite cancellation identity to `HasSum`. -/
theorem abelCancellationMultiplier_hasSum_mean_cancellation
    {ι : Type*} (q : ℝ) (c0 g k : ℂ) (c z M : ι → ℂ)
    (hd : ∀ i, 1 - (q : ℂ) * z i ≠ 0)
    (hc : HasSum c (-c0))
    (hg : HasSum
      (fun i => c i * (M i * abelCancellationMultiplier q (z i))) (g - c0))
    (hk : HasSum
      (fun i => c i * ((1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i))) (-k)) :
    HasSum
      (fun i => c i * (M i - 1) * abelCancellationMultiplier q (z i))
      (g - k) := by
  have hsum := (hg.add hk).sub hc
  have hvalue : (g - c0) + -k - -c0 = g - k := by ring
  rw [hvalue] at hsum
  have hterm :
      (fun i => c i * (M i * abelCancellationMultiplier q (z i)) +
        c i * ((1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i)) - c i) =
      (fun i => c i * (M i - 1) * abelCancellationMultiplier q (z i)) := by
    funext i
    have hid := abelCancellationMultiplier_comparison_identity q (z i) (M i) (hd i)
    calc
      c i * (M i * abelCancellationMultiplier q (z i)) +
          c i * ((1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i)) - c i =
        c i * (M i * abelCancellationMultiplier q (z i) +
          (1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i)) - c i := by ring
      _ = c i * (1 + (M i - 1) * abelCancellationMultiplier q (z i)) - c i := by
        rw [hid]
      _ = _ := by ring

  rw [hterm] at hsum
  exact hsum

/-- The same deduction as an exact infinite-sum identity. -/
theorem abelCancellationMultiplier_tsum_mean_cancellation
    {ι : Type*} (q : ℝ) (c0 g k : ℂ) (c z M : ι → ℂ)
    (hd : ∀ i, 1 - (q : ℂ) * z i ≠ 0)
    (hc : HasSum c (-c0))
    (hg : HasSum
      (fun i => c i * (M i * abelCancellationMultiplier q (z i))) (g - c0))
    (hk : HasSum
      (fun i => c i * ((1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i))) (-k)) :
    g - k = ∑' i, c i * (M i - 1) * abelCancellationMultiplier q (z i) := by
  exact (abelCancellationMultiplier_hasSum_mean_cancellation
    q c0 g k c z M hd hc hg hk).tsum_eq.symm

/-- For finitely many boundary coordinates, the frequency net may be taken
to its scalar limit inside the full signed squared norm. This does not assert
convergence of a Hilbert-valued Fourier series or exchange two infinite limits. -/
theorem finite_coordinate_energy_tendsto_of_hasSum
    {ι : Type*} (s : Finset ℕ) (f : ℕ → ι → ℂ) (a : ℕ → ℂ)
    (hf : ∀ i, HasSum (f i) (a i)) :
    Filter.Tendsto
      (fun t : Finset ι =>
        ∑ i ∈ s, (1 / 4 : ℝ) * ‖∑ h ∈ t, f i h‖ ^ 2)
      Filter.atTop (nhds (∑ i ∈ s, (1 / 4 : ℝ) * ‖a i‖ ^ 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact tendsto_const_nhds
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have ht : Filter.Tendsto
          (fun t : Finset ι => ∑ h ∈ t, f i h)
          Filter.atTop (nhds (a i)) := hf i
      exact (tendsto_const_nhds.mul (ht.norm.pow 2)).add ih

end
end RiemannResearch.Analysis
