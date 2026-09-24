import RiemannResearch.RH.HardyMobiusFamily
import RiemannResearch.RH.ParetoMellinHardyEndpoint
import RiemannResearch.RH.EndpointResidueCorrection
import RiemannResearch.RH.MobiusQuantitativeRate

/-!
# Hardy endpoint convergence of the Möbius sums

Source for the raw family and normalization: Manzur, Noor, Quintero,
https://arxiv.org/html/2606.16097v1 (2026). The proof assembly and corrected
family follow HardyEndpointCompactness20260924.md. The raw conditional
statement records its scalar arithmetic rate explicitly; the final theorem
discharges it through the quantitative prime number theorem.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto
open MeasureTheory Filter
open scoped Topology

/-- Convergence of the actual corrected zeta sums, uniformly over all interior lines. -/
theorem correctedHardyMobiusSum_endpoint :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, 1 < σ →
      (∫ w : ℝ, ‖1 / WeightedMellin.verticalPoint σ w -
        correctedHardyMobiusSum N (WeightedMellin.verticalPoint σ w)‖ ^ 2) < ε := by
  intro ε hε
  filter_upwards [canonicalMobiusResidual_hardy_endpoint ε hε] with N hN
  intro σ hσ
  have he (w : ℝ) :
      paretoMellin (hilbertOne - canonicalMobiusHilbert N)
        (WeightedMellin.verticalPoint σ w) =
      1 / WeightedMellin.verticalPoint σ w -
        correctedHardyMobiusSum N (WeightedMellin.verticalPoint σ w) := by
    apply canonicalMobiusResidual_mellin
    simp only [WeightedMellin.verticalPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith
  simpa only [he] using hN σ hσ

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open MeasureTheory Filter
open scoped BigOperators Topology

theorem exactEndpointCellEnergy_add_le (x y : ThresholdHilbert) :
    exactEndpointCellEnergy (x + y) ≤
      2 * exactEndpointCellEnergy x + 2 * exactEndpointCellEnergy y := by
  have hx := (exactEndpointCellEnergy_summable x).mul_left 2
  have hy := (exactEndpointCellEnergy_summable y).mul_left 2
  unfold exactEndpointCellEnergy
  rw [← tsum_mul_left, ← tsum_mul_left, ← hx.tsum_add hy]
  apply (exactEndpointCellEnergy_summable (x + y)).tsum_le_tsum _ (hx.add hy)
  intro n
  have he := congrFun (hilbertSequenceLinear.map_add x y) n
  change hilbertSequence (x + y) n = hilbertSequence x n + hilbertSequence y n at he
  rw [he]
  have hp := mul_nonneg (exactEndpointCellWeight_nonneg n)
    (sq_nonneg (hilbertSequence x n - hilbertSequence y n))
  nlinarith

theorem rawMobiusResidual_eq_corrected_add (N : ℕ) :
    hilbertOne - rawMobiusHilbert N =
      (hilbertOne - canonicalMobiusHilbert N) +
        (((N + 1 : ℕ) : ℝ) * mobiusReciprocalSum N) •
          normalizedResidueHilbert (N + 1) (Nat.succ_pos _) := by
  rw [canonicalMobiusHilbert_eq_raw_add]
  abel

/-- The scalar rate sufficient for the raw family; an unconditional provider is below. -/
def RawMobiusEndpointHeadRate : Prop :=
  Tendsto (fun N : ℕ => mobiusReciprocalSum N ^ 2 *
    ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ)) + 1)) atTop (𝓝 0)

/-- Complete infinite energy convergence, conditional only on the displayed scalar rate. -/
theorem rawMobiusResidual_cellEnergy_tendsto_of_headRate
    (hrate : RawMobiusEndpointHeadRate) :
    Tendsto (fun N => exactEndpointCellEnergy (hilbertOne - rawMobiusHilbert N))
      atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => mobiusReciprocalSum N ^ 2 *
      ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ)) + 1)) atTop (𝓝 (0 : ℝ)) := hrate
  have hup : Tendsto (fun N : ℕ =>
      2 * exactEndpointCellEnergy (hilbertOne - canonicalMobiusHilbert N) +
      2 * (mobiusReciprocalSum N ^ 2 *
        ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ)) + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_add] using
      (canonicalMobiusResidual_exactEndpointCellEnergy_tendsto_zero.const_mul 2).add
        (hr.const_mul 2)
  have hbound (N : ℕ) :
      exactEndpointCellEnergy (hilbertOne - rawMobiusHilbert N) ≤
        2 * exactEndpointCellEnergy (hilbertOne - canonicalMobiusHilbert N) +
        2 * (mobiusReciprocalSum N ^ 2 *
          ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ)) + 1)) := by
    let c : ThresholdHilbert :=
      (((N + 1 : ℕ) : ℝ) * mobiusReciprocalSum N) •
        normalizedResidueHilbert (N + 1) (Nat.succ_pos N)
    have hc : exactEndpointCellEnergy c ≤
        mobiusReciprocalSum N ^ 2 *
          ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ)) + 1) :=
      boundaryCorrection_exactEndpointCellEnergy_le (N + 1) (Nat.succ_pos N)
        (mobiusReciprocalSum N)
    have he : exactEndpointCellEnergy (hilbertOne - rawMobiusHilbert N) =
        exactEndpointCellEnergy ((hilbertOne - canonicalMobiusHilbert N) + c) :=
      congrArg exactEndpointCellEnergy (rawMobiusResidual_eq_corrected_add N)
    have ha := exactEndpointCellEnergy_add_le (hilbertOne - canonicalMobiusHilbert N) c
    exact he.le.trans (ha.trans
      (add_le_add (le_refl (2 * exactEndpointCellEnergy (hilbertOne - canonicalMobiusHilbert N)))
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))))
  exact squeeze_zero
    (fun N : ℕ => exactEndpointCellEnergy_nonneg (hilbertOne - rawMobiusHilbert N))
    hbound hup

theorem rawMobiusResidual_mellin (N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertOne - rawMobiusHilbert N) s =
      1 / s - rawHardyMobiusSum N s := by
  change (paretoMellinContinuous s hs) (hilbertOne - rawMobiusHilbert N) = _
  rw [map_sub]
  exact congrArg₂ (· - ·) (paretoMellin_one s hs) (rawMobiusHilbert_mellin N s hs)

/-- The raw Hardy endpoint theorem with its precise remaining arithmetic premise. -/
theorem rawHardyMobiusSum_endpoint_of_headRate (hrate : RawMobiusEndpointHeadRate) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, 1 < σ →
      (∫ w : ℝ, ‖1 / WeightedMellin.verticalPoint σ w -
        rawHardyMobiusSum N (WeightedMellin.verticalPoint σ w)‖ ^ 2) < ε := by
  intro ε hε
  have ht := paretoMellin_hardy_endpoint_tendsto_of_cellEnergy
    (fun N => hilbertOne - rawMobiusHilbert N)
    (rawMobiusResidual_cellEnergy_tendsto_of_headRate hrate) ε hε
  filter_upwards [ht] with N hN
  intro σ hσ
  have he (w : ℝ) :
      paretoMellin (hilbertOne - rawMobiusHilbert N)
        (WeightedMellin.verticalPoint σ w) =
      1 / WeightedMellin.verticalPoint σ w -
        rawHardyMobiusSum N (WeightedMellin.verticalPoint σ w) := by
    apply rawMobiusResidual_mellin
    simp only [WeightedMellin.verticalPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith
  simpa only [he] using hN σ hσ

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open MeasureTheory Filter
open scoped Topology
/-- The scalar arithmetic rate is supplied unconditionally by quantitative PNT. -/
theorem rawMobiusEndpointHeadRate : RawMobiusEndpointHeadRate :=
  mobiusReciprocalSum_sq_mul_harmonic_tendsto_zero

/-- Full raw endpoint energy, including every tail cell, converges to zero. -/
theorem rawMobiusResidual_cellEnergy_tendsto_zero :
    Tendsto (fun N => exactEndpointCellEnergy (hilbertOne - rawMobiusHilbert N))
      atTop (𝓝 0) :=
  rawMobiusResidual_cellEnergy_tendsto_of_headRate rawMobiusEndpointHeadRate

/-- Unconditional convergence of the raw Möbius sums at the Hardy endpoint Re(s)=1. -/
theorem rawHardyMobiusSum_endpoint :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ σ : ℝ, 1 < σ →
      (∫ w : ℝ, ‖1 / WeightedMellin.verticalPoint σ w -
        rawHardyMobiusSum N (WeightedMellin.verticalPoint σ w)‖ ^ 2) < ε :=
  rawHardyMobiusSum_endpoint_of_headRate rawMobiusEndpointHeadRate
end RiemannResearch.RH.Pareto
