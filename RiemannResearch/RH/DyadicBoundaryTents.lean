import RiemannResearch.RH.DyadicFiniteBoundaryCoordinates
import RiemannResearch.Analysis.DyadicSequenceInterpolation

/-!
# Exact affine pieces of actual dyadic boundary tents

Source: user-provided DyadicSignedBoundaryAbelVerification20260910(1).md
and the retained DyadicBoundaryFourierResearchNote20260910.md, September 10, 2026.
The present proofs establish the stated bounded continuation targets.

The formulas hold at every dyadic depth. This does not construct the full
real log-periodic extension or justify its Fourier expansion.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Above its single innovation index, each actual boundary coordinate
interpolates exactly along arbitrary dyadic subdivisions. -/
theorem dyadicBoundaryCoordinate_step_interpolation
    (i q h r : ℕ) (hq : i+2 ≤ q) (hr : r ≤ 2^h) :
    (2 : ℝ)^h *
        dyadicBoundaryCoordinate
          (dyadicProjectedStep (2^h*q+r)
            (by
              have hqp : 0 < q := by omega
              positivity)) i =
      ((2 : ℝ)^h - (r : ℝ)) *
          dyadicBoundaryCoordinate (dyadicProjectedStep q (by omega)) i +
        (r : ℝ) *
          dyadicBoundaryCoordinate (dyadicProjectedStep (q+1) (by positivity)) i := by
  let f : ℕ → ℝ := fun m =>
    if hm : 0 < m then dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i else 0
  have hf (m : ℕ) (hm : 0 < m) :
      f m = dyadicBoundaryCoordinate (dyadicProjectedStep m hm) i := by
    simp only [f, dif_pos hm]
  have hd (n : ℕ) (hn : q ≤ n) : f (2*n) = f n := by
    rw [hf (2*n) (by omega), hf n (by omega)]
    exact dyadicBoundaryCoordinate_step_double n (by omega) i
  have ho (n : ℕ) (hn : q ≤ n) :
      f (2*n+1) = (1/2 : ℝ) * (f n + f (n+1)) := by
    rw [hf (2*n+1) (by omega), hf n (by omega), hf (n+1) (by omega),
      dyadicBoundaryCoordinate_step_odd n (by omega) i,
      if_neg (show i+1 ≠ n by omega), zero_add]
  have hqp : 0 < q := by omega
  have hp : 0 < 2^h*q+r := by positivity
  simpa only [hf _ hp, hf _ hqp, hf _ (show 0 < q+1 by omega)] using
    dyadicSequence_exact_interpolation f q hd ho h r hr

/-- The unique new coefficient has unit height. -/
theorem dyadicBoundaryCoordinate_step_peak (i : ℕ) :
    dyadicBoundaryCoordinate
      (dyadicProjectedStep (2*(i+1)+1) (by positivity)) i = 1 := by
  rw [dyadicBoundaryCoordinate_step_odd (i+1) (by positivity) i,
    if_pos rfl,
    dyadicBoundaryCoordinate_step_zero (i+1) (by positivity) i (by omega),
    dyadicBoundaryCoordinate_step_zero (i+1+1) (by positivity) i (by omega)]
  norm_num

/-- Exact ascending affine piece of every actual dyadic boundary tent. -/
theorem dyadicBoundaryCoordinate_step_tent_rising
    (i h r : ℕ) (hr : r ≤ 2^h) :
    dyadicBoundaryCoordinate
      (dyadicProjectedStep (2^h*(2*(i+1))+r) (by positivity)) i =
        (r : ℝ) / (2 : ℝ)^h := by
  have hi := dyadicBoundaryCoordinate_step_interpolation i (2*(i+1)) h r
    (by omega) hr
  rw [dyadicBoundaryCoordinate_step_zero (2*(i+1)) (by positivity) i (by omega),
    dyadicBoundaryCoordinate_step_peak, mul_zero, zero_add, mul_one] at hi
  apply (eq_div_iff (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) h))).mpr
  nlinarith only [hi]

/-- Exact descending affine piece, retaining its sign as an affine identity. -/
theorem dyadicBoundaryCoordinate_step_tent_falling
    (i h r : ℕ) (hr : r ≤ 2^h) :
    dyadicBoundaryCoordinate
      (dyadicProjectedStep (2^h*(2*(i+1)+1)+r) (by positivity)) i =
        1 - (r : ℝ) / (2 : ℝ)^h := by
  have hi := dyadicBoundaryCoordinate_step_interpolation i (2*(i+1)+1) h r
    (by omega) hr
  rw [dyadicBoundaryCoordinate_step_peak] at hi
  have he : 2*(i+1)+1+1 = 2*(i+1+1) := by omega
  simp only [he, dyadicBoundaryCoordinate_step_double (i+1+1) (by positivity) i,
    dyadicBoundaryCoordinate_step_zero (i+1+1) (by positivity) i (by omega),
    mul_one, mul_zero, add_zero] at hi
  have hp : (2 : ℝ)^h ≠ 0 := ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) h)
  apply (mul_right_cancel₀ hp)
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hp]
  nlinarith only [hi]

end
end RiemannResearch.RH.Pareto
