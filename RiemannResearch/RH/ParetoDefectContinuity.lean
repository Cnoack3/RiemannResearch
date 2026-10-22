import RiemannResearch.RH.ParetoNoiseSignal
import RiemannResearch.RH.ParetoBoundedInteraction
import Mathlib.Tactic.Positivity

/-!
# From full Pareto approximation to arithmetic defect convergence

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §§2,3,8.
The positive coordinate masses connect actual full Pareto squared error to
pointwise approximation and then to the finite Möbius difference functionals.
Each approximant is bounded separately; no bound uniform in the approximation
index is required. The zero coordinate must be anchored for defect convergence.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A single positive-coordinate squared error is dominated by the complete sum.
This also holds trivially at coordinate zero, whose Pareto weight is zero. -/
theorem paretoError_coordinate_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (k : ℕ) :
    positiveWeight k * (1 - f k)^2 ≤ paretoError f := by
  have hs := weighted_summable_of_bounded (error_square_bounded hf)
  have h := hs.sum_le_tsum ({k} : Finset ℕ)
    (fun j _ => mul_nonneg (positiveWeight_nonneg j) (sq_nonneg (1-f j)))
  simpa only [Finset.sum_singleton, paretoError, paretoInner, pow_two] using h

/-- Vanishing full Pareto squared error forces convergence at every positive coordinate.
The approximants need not share a common bound. -/
theorem paretoError_tendsto_coordinate {f : ℕ → ℕ → ℝ}
    (hf : ∀ t, ∃ C : ℝ, ∀ k, |f t k| ≤ C)
    (herr : Tendsto (fun t => paretoError (f t)) atTop (nhds 0))
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun t => f t k) atTop (nhds 1) := by
  have hw : 0 < positiveWeight k := by
    unfold positiveWeight
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < positiveWeight k * ε^2 := mul_pos hw (sq_pos_of_pos hε)
  have hev := (Metric.tendsto_nhds.mp herr) (positiveWeight k * ε^2) hδ
  apply hev.mono
  intro t ht
  obtain ⟨C,hC⟩ := hf t
  have hcoordinate := paretoError_coordinate_le hC k
  have hsmall : paretoError (f t) < positiveWeight k * ε^2 := by
    have habs : |paretoError (f t)| < positiveWeight k * ε^2 := by
      simpa only [Real.dist_eq, sub_zero] using ht
    exact lt_of_le_of_lt (le_abs_self _) habs
  rw [Real.dist_eq]
  by_contra hn
  have habs : ε ≤ |f t k - 1| := le_of_not_gt hn
  have hprod := mul_nonneg (sub_nonneg.mpr habs)
    (add_nonneg (abs_nonneg (f t k-1)) hε.le)
  have hsq : ε^2 ≤ (1 - f t k)^2 := by
    nlinarith [sq_abs (f t k - 1)]
  have hweighted := mul_le_mul_of_nonneg_left hsq hw.le
  linarith

/-- Norm convergence of anchored approximants forces each arithmetic defect to
approach the genuine Möbius value of the constant target. -/
theorem paretoError_tendsto_mobiusDifference {f : ℕ → ℕ → ℝ}
    (hf : ∀ t, ∃ C : ℝ, ∀ k, |f t k| ≤ C)
    (hf0 : ∀ t, f t 0 = 0)
    (herr : Tendsto (fun t => paretoError (f t)) atTop (nhds 0))
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun t => mobiusDifference m (f t)) atTop
      (nhds (ArithmeticFunction.moebius m : ℝ)) := by
  have hpoint (k : ℕ) : Tendsto (fun t => f t k) atTop
      (nhds (if k = 0 then 0 else 1)) := by
    by_cases hk : k = 0
    · subst k
      simpa only [hf0, ↓reduceIte] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · simpa only [if_neg hk] using
        paretoError_tendsto_coordinate hf herr k (Nat.pos_of_ne_zero hk)
  have h := mobiusDifference_tendsto m hpoint
  rw [mobiusDifference_one m hm] at h
  exact h

/-- Even with every prime available, a fixed bound on distinct-prime interaction
in all packet conductors prevents convergence in the actual full Pareto norm. -/
theorem boundedPrimeSupport_no_paretoError_limit (r : ℕ)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hs : ∀ t q, q ∈ s t → 0 < q ∧ q.primeFactors.card ≤ r) :
    ¬ Tendsto (fun t => paretoError
      (fun k => ∑ q ∈ s t, c t q * ramanujanPacket q k)) atTop (nhds 0) := by
  intro herr
  apply boundedPrimeSupport_no_pointwise_limit r s c hs
  intro k hk
  exact paretoError_tendsto_coordinate
    (fun t => packetCombination_bounded (s t) (c t)) herr k hk

end
end RiemannResearch.RH.Pareto
