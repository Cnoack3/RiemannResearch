import RiemannResearch.RH.ParetoResidueMicroscopicCertificate
import RiemannResearch.RH.ParetoResidueMicroscopicGram
import RiemannResearch.RH.ParetoResidueMovingCertificate
import RiemannResearch.RH.ParetoResidueCriticalGram
import RiemannResearch.RH.ParetoResidueCriticalGramRate
import RiemannResearch.RH.MellinCriticalPoint
import RiemannResearch.RH.ParetoResidueMovingGrowth
import RiemannResearch.Analysis.ActualZeroReciprocalConstant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Automatic source decay for microscopic zero certificates

Source: the counting argument in Section 11 of the user-provided
Ramanujan DPP / LCM handoff, 9 November 2026. Each signed comparison
entry contains at least the reciprocal logarithmic scale. Thus its
uniform row bound controls the number of ordinates, including empty
families. Combining this with the checked actual-zero reciprocal sum
removes a separate source-decay hypothesis. No remainder upper bound
or Riemann hypothesis is assumed or proved by the certificate theorem.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint)
open SpectralObstruction (reciprocalSquareMass)
open RiemannResearch.Analysis.ActualZeroReciprocalConstant (reciprocalConstant)

theorem microscopicCrossBudget_one_le (t u : ℝ) :
    1 ≤ microscopicCrossBudget t u := by
  have hr : 0 ≤ reciprocalSquareMass := tsum_nonneg (fun _ => by positivity)
  unfold microscopicCrossBudget
  nlinarith [sq_nonneg (1 + criticalTailMass), mul_nonneg hr
    (show 0 ≤ 1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖ +
      ‖((t-u : ℝ) : ℂ) * Complex.I + 1‖ by positivity)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every comparison row contains two entries per ordinate. -/
theorem microscopicRealRowBudget_card_le (γ : ι → ℝ) (N : ℕ)
    (hN : 0 < N) (i : ι × Bool) :
    2 * (Fintype.card ι : ℝ) / Real.log ((N : ℝ) + 1) ≤
      microscopicRealRowBudget γ N i := by
  have hlog : 0 < Real.log ((N : ℝ) + 1) := by
    apply Real.log_pos
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hentry (j : ι × Bool) : 1 / Real.log ((N : ℝ) + 1) ≤
      (microscopicCrossBudget (γ i.1) (γ j.1) +
       microscopicCrossBudget (γ i.1) (-γ j.1)) /
      (2 * Real.log ((N : ℝ) + 1)) := by
    apply (div_le_div_iff₀ hlog (by positivity)).mpr
    nlinarith [microscopicCrossBudget_one_le (γ i.1) (γ j.1),
      microscopicCrossBudget_one_le (γ i.1) (-γ j.1)]
  calc
    _ = ∑ _j : ι × Bool, 1 / Real.log ((N : ℝ) + 1) := by
      simp [Fintype.card_prod, Fintype.card_bool]
      ring
    _ ≤ microscopicRealRowBudget γ N i := by
      unfold microscopicRealRowBudget
      exact Finset.sum_le_sum (fun j _ =>
        (hentry j).trans (le_add_of_nonneg_left (abs_nonneg _)))

/-- The count bound remains valid when the family is empty. -/
theorem card_div_log_le_of_microscopic (γ : ι → ℝ) (N : ℕ) (hN : 0 < N)
    (d : ℝ) (hd : 0 ≤ d) (hrow : ∀ i, microscopicRealRowBudget γ N i ≤ d) :
    (Fintype.card ι : ℝ) / Real.log ((N : ℝ) + 1) ≤ d / 2 := by
  classical
  by_cases h : Nonempty ι
  · let i := Classical.choice h
    have hc := (microscopicRealRowBudget_card_le γ N hN (i, false)).trans (hrow _)
    rw [mul_div_assoc] at hc
    linarith only [hc]
  · haveI : IsEmpty ι := not_nonempty_iff.mp h
    simp only [Fintype.card_of_isEmpty, Nat.cast_zero, zero_div]
    positivity

theorem criticalSourceError_tendsto_zero :
    Tendsto criticalSourceError atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (1 + criticalTailMass) / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := 1 + criticalTailMass)).mul
        (tendsto_inv_atTop_zero.comp hN)
  exact squeeze_zero (fun N => (criticalSourceError_le_inv N).1)
    (fun N => (criticalSourceError_le_inv N).2) hlim

/-- Explicit source bound from the microscopic count bound and actual zeros. -/
theorem relativeCriticalSourceSq_div_log_le_of_microscopic
    (γ : ι → ℝ) (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (N : ℕ) (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d)
    (hrow : ∀ i, microscopicRealRowBudget γ N i ≤ d) :
    relativeCriticalSourceSq γ N / Real.log ((N : ℝ) + 1) ≤
      reciprocalConstant / (2 * Real.log ((N : ℝ) + 1)) +
      (d / 2) * (criticalSourceError N * (4 + criticalSourceError N)) := by
  have hlog : 0 < Real.log ((N : ℝ) + 1) := by
    apply Real.log_pos
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hc := card_div_log_le_of_microscopic γ N hN d hd hrow
  have hs := relativeCriticalSourceSq_error γ N
  have hzsum := criticalReciprocalSum_positive_le_half γ hγ hpos hz
  have hup : relativeCriticalSourceSq γ N ≤ reciprocalConstant / 2 +
      (Fintype.card ι : ℝ) * (criticalSourceError N * (4 + criticalSourceError N)) := by
    linarith only [hs, hzsum, le_abs_self
      (relativeCriticalSourceSq γ N - ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2)]
  calc
    _ ≤ (reciprocalConstant / 2 + (Fintype.card ι : ℝ) *
        (criticalSourceError N * (4 + criticalSourceError N))) /
        Real.log ((N : ℝ) + 1) := div_le_div_of_nonneg_right hup hlog.le
    _ = reciprocalConstant / (2 * Real.log ((N : ℝ) + 1)) +
        ((Fintype.card ι : ℝ) / Real.log ((N : ℝ) + 1)) *
        (criticalSourceError N * (4 + criticalSourceError N)) := by ring
    _ ≤ _ := by
      have he : 0 ≤ criticalSourceError N := (criticalSourceError_le_inv N).1
      have hp : 0 ≤ criticalSourceError N * (4 + criticalSourceError N) := by positivity
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hp)

/-- Source decay follows from the row bound, without an additional source premise. -/
theorem relativeCriticalSourceSq_div_log_tendsto_of_microscopic
    (κ : ℕ → Type*) [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (γ : ∀ j, κ j → ℝ)
    (hγ : ∀ j, Function.Injective (γ j)) (hpos : ∀ j i, 0 < γ j i)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (d : ℝ) (hd : 0 ≤ d)
    (hrow : ∀ᶠ j in atTop, ∀ i, microscopicRealRowBudget (γ j) (N j) i ≤ d) :
    Tendsto (fun j => relativeCriticalSourceSq (γ j) (N j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0) := by
  have hNat : Tendsto (fun j => (N j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by
      change (N j : ℝ) ≤ (N j : ℝ) + 1
      linarith) (tendsto_natCast_atTop_atTop.comp hN)
  have hlog := Real.tendsto_log_atTop.comp hNat
  have hinv := (tendsto_inv_atTop_zero.comp hlog).const_mul (reciprocalConstant / 2)
  have he := criticalSourceError_tendsto_zero.comp hN
  have hcor : Tendsto (fun j => (d / 2) *
      (criticalSourceError (N j) * (4 + criticalSourceError (N j)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul, mul_zero] using
      (he.mul (tendsto_const_nhds.add he)).const_mul (d / 2)
  have hB : Tendsto (fun j => reciprocalConstant / (2 * Real.log ((N j : ℝ) + 1)) +
      (d / 2) * (criticalSourceError (N j) * (4 + criticalSourceError (N j))))
      atTop (𝓝 0) := by
    have hh := hinv.add hcor
    simp only [Function.comp_def, mul_zero, zero_add] at hh
    convert hh using 1 <;> ext j <;> ring
  refine squeeze_zero' (Eventually.of_forall (fun j => by
    unfold relativeCriticalSourceSq
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (N j)])))) ?_ hB
  filter_upwards [hN.eventually (eventually_gt_atTop 0), hrow] with j hj hr
  exact relativeCriticalSourceSq_div_log_le_of_microscopic
    (γ j) (hγ j) (hpos j) (hz j) (N j) hj d hd hr

/-- Distinct positive actual zeros need only the uniform microscopic row margin.
Their normalized source decay is supplied by the preceding theorem. -/
theorem critical_certificate_tendsto_of_microscopic_actual_zeros
    (κ : ℕ → Type*) [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (γ : ∀ j, κ j → ℝ)
    (hγ : ∀ j, Function.Injective (γ j)) (hpos : ∀ j i, 0 < γ j i)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d < 1 / 2)
    (hrow : ∀ᶠ j in atTop, ∀ i, microscopicRealRowBudget (γ j) (N j) i ≤ d) :
    Tendsto (fun j => certificateEnergy (N j) (fun i => criticalPoint (γ j i)))
      atTop (𝓝 0) :=
  critical_certificate_tendsto_of_microscopic κ N γ
    (hN.eventually (eventually_gt_atTop 0)) hz d hd hd' hrow
    (relativeCriticalSourceSq_div_log_tendsto_of_microscopic κ N hN γ hγ hpos hz d hd hrow)

end RiemannResearch.RH.Pareto.ResidueMellin
