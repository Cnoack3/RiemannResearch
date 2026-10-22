import RiemannResearch.RH.DyadicFiniteBoundaryCoordinates
import RiemannResearch.RH.DyadicRegularizedBoundaryEnergy
import RiemannResearch.RH.DyadicRegularizedSignedGram
import RiemannResearch.RH.DyadicArithmeticResidueTelescoping

/-!
# Actual signed boundary coefficients of the arithmetic remainder

Source: user-provided DyadicSignedMeanEnergyVerification20260910(1).md,
September 10, 2026, next bounded arithmetic target. The exact residue cocycle
is applied before the convergent product-index sum. Every Möbius sign and
the complete comparison coefficient remain present. Positive damping supplies
convergence; no bound uniform in damping or full legal approximation is claimed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem dyadicBoundaryCoordinate_add (f g : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate (f + g) i =
      dyadicBoundaryCoordinate f i + dyadicBoundaryCoordinate g i := by
  simp only [dyadicBoundaryCoordinate, inner_add_right, mul_add]

theorem dyadicBoundaryCoordinate_sub (f g : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate (f - g) i =
      dyadicBoundaryCoordinate f i - dyadicBoundaryCoordinate g i := by
  simp only [dyadicBoundaryCoordinate, inner_sub_right, mul_sub]

theorem dyadicBoundaryCoordinate_smul (c : ℝ) (f : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate (c • f) i = c * dyadicBoundaryCoordinate f i := by
  simp only [dyadicBoundaryCoordinate, real_inner_smul_right]
  ring

theorem dyadicBoundaryCoordinate_projection (f : ThresholdHilbert) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicQuotientProjection f) i =
      dyadicBoundaryCoordinate f i := by
  unfold dyadicBoundaryCoordinate
  rw [← dyadicQuotientProjection_inner, dyadicBoundaryVector_projection]

theorem dyadicBoundaryCoordinate_tsum {ι : Type*} (f : ι → ThresholdHilbert)
    (hf : Summable f) (i : ℕ) :
    dyadicBoundaryCoordinate (∑' p, f p) i =
      ∑' p, dyadicBoundaryCoordinate (f p) i := by
  unfold dyadicBoundaryCoordinate
  calc
    _ = 4 * ∑' p, inner ℝ (dyadicBoundaryVector i) (f p) :=
      congrArg (fun x : ℝ => 4 * x) ((innerSL ℝ (dyadicBoundaryVector i)).map_tsum hf)
    _ = _ := (tsum_mul_left).symm

/-- Each actual product term is a signed successive-conductor difference in
the complete physical boundary coordinate. No terminal term has been removed. -/
theorem dyadicRegularizedTerm_boundaryCoordinate (ε : ℝ) (p : ℕ × ℕ) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicRegularizedTerm ε p) i =
      dyadicRegularizationCoefficient ε p.1 p.2 *
        (dyadicBoundaryCoordinate
          (hilbertResidue ((p.1 + 1) * 3 ^ (p.2 + 1)) (by positivity)) i -
         dyadicBoundaryCoordinate
          (hilbertResidue ((p.1 + 1) * 3 ^ p.2) (by positivity)) i) := by
  rw [dyadicRegularizedTerm, dyadicBoundaryCoordinate_smul,
    dyadicBoundaryCoordinate_projection, hilbertDilation_residue_eq_sub,
    dyadicBoundaryCoordinate_sub]
  simp only [pow_succ, Nat.mul_assoc]

/-- The actual arithmetic coefficient, with both conductor-boundary terms and
every Möbius sign retained inside the convergent product-index sum. -/
def dyadicSignedBoundaryCoefficient (ε : ℝ) (i : ℕ) : ℝ :=
  dyadicRegularizationNormalization ε *
    ∑' p : ℕ × ℕ,
      ((ArithmeticFunction.moebius (p.1 + 1) : ℝ) /
        (p.1 + 1 : ℝ) ^ (1 + ε) * triadicDampingRatio ε ^ p.2) *
        (dyadicBoundaryCoordinate
          (hilbertResidue ((p.1 + 1) * 3 ^ (p.2 + 1)) (by positivity)) i -
         dyadicBoundaryCoordinate
          (hilbertResidue ((p.1 + 1) * 3 ^ p.2) (by positivity)) i)

theorem dyadicRegularizedTerm_boundaryCoordinate_abs_summable
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      |dyadicBoundaryCoordinate (dyadicRegularizedTerm ε p) i|) := by
  have hs := (dyadicRegularizedTerm_pairing_abs_summable hε
    (dyadicBoundaryVector i)).mul_left 4
  apply hs.congr
  intro p
  rw [dyadicBoundaryCoordinate, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [real_inner_comm]

theorem dyadicSignedBoundaryCoefficient_series_abs_summable
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    Summable (fun p : ℕ × ℕ =>
      |((ArithmeticFunction.moebius (p.1 + 1) : ℝ) /
        (p.1 + 1 : ℝ) ^ (1 + ε) * triadicDampingRatio ε ^ p.2) *
        (dyadicBoundaryCoordinate
          (hilbertResidue ((p.1 + 1) * 3 ^ (p.2 + 1)) (by positivity)) i -
         dyadicBoundaryCoordinate
          (hilbertResidue ((p.1 + 1) * 3 ^ p.2) (by positivity)) i)|) := by
  simpa only [dyadicRegularizedTerm_boundaryCoordinate,
    dyadicRegularizationCoefficient] using
      dyadicRegularizedTerm_boundaryCoordinate_abs_summable hε i

/-- The explicit signed scalar series is the actual full-H boundary coefficient. -/
theorem dyadicRegularizedFamily_boundaryCoordinate
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i =
      dyadicSignedBoundaryCoefficient ε i := by
  rw [dyadicRegularizedFamily, dyadicBoundaryCoordinate_smul,
    dyadicBoundaryCoordinate_tsum _ (dyadicRegularizedTerm_summable hε)]
  simp only [dyadicSignedBoundaryCoefficient,
    dyadicRegularizedTerm_boundaryCoordinate, dyadicRegularizationCoefficient]

/-- The actual Abel step coefficient; the entire orbit remains in the series. -/
theorem dyadicStepAbelOrbit_boundaryCoordinate {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicStepAbelOrbit ε) i =
      (1 - triadicDampingRatio ε) *
        ∑' j : ℕ, triadicDampingRatio ε ^ j *
          dyadicBoundaryCoordinate (dyadicProjectedStep (3 ^ (j + 1))
            (by positivity)) i := by
  rw [dyadicStepAbelOrbit, dyadicBoundaryCoordinate_smul,
    dyadicBoundaryCoordinate_tsum _ (dyadicStepAbelOrbit_series_summable ε hε)]
  simp only [dyadicBoundaryCoordinate_smul, dyadicProjectedStep]

/-- The actual remainder coefficient, including the signed comparison terms. -/
def dyadicNormalizationBoundaryCoefficient (ε : ℝ) (i : ℕ) : ℝ :=
  dyadicSignedBoundaryCoefficient ε i -
    (Real.log 2)⁻¹ * dyadicBoundaryCoordinate (hilbertResidue 2 (by norm_num)) i +
    (1 - triadicDampingRatio ε) *
      ∑' j : ℕ, triadicDampingRatio ε ^ j *
        dyadicBoundaryCoordinate (dyadicProjectedStep (3 ^ (j + 1))
          (by positivity)) i

theorem dyadicNormalizationRemainder_boundaryCoordinate
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    dyadicBoundaryCoordinate (dyadicNormalizationRemainder ε) i =
      dyadicNormalizationBoundaryCoefficient ε i := by
  rw [dyadicNormalizationRemainder, dyadicBoundaryCoordinate_sub,
    dyadicRegularizedFamily_boundaryCoordinate hε,
    dyadicNormalizationComparison, dyadicBoundaryCoordinate_sub,
    dyadicBoundaryCoordinate_add, dyadicBoundaryCoordinate_smul,
    dyadicBoundaryCoordinate_projection, dyadicBoundaryCoordinate_projection,
    dyadicBoundaryCoordinate_one, dyadicStepAbelOrbit_boundaryCoordinate hε]
  unfold dyadicNormalizationBoundaryCoefficient
  ring

end
end RiemannResearch.RH.Pareto
