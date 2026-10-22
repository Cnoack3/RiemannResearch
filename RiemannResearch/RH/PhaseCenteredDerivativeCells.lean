import RiemannResearch.RH.PhaseCenteredActualOperator
import RiemannResearch.RH.ParetoCompressedMellinUniformBound
import RiemannResearch.Analysis.LogarithmicMellinHead
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CompressedMellin

def derivativeUnitCell (n : ℕ) : Set ℝ := Ico ((n : ℝ) + 1) ((n : ℝ) + 2)
def mellinLogCell (t : ℝ) (n : ℕ) : ℂ :=
  ∫ x in derivativeUnitCell n, ((Real.log x - Real.log t : ℝ) : ℂ) *
    (x : ℂ) ^ (-phaseMellinPoint t - 1)
def mellinLogBoundary (t : ℝ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-phaseMellinPoint t) *
    ((Real.log ((n : ℝ) + 1) - Real.log t : ℝ) : ℂ) -
  (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-phaseMellinPoint t) *
    ((Real.log ((n : ℝ) + 2) - Real.log t : ℝ) : ℂ)

private theorem phasePoint_ne_zero (t : ℝ) : phaseMellinPoint t ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  rw [phaseMellinPoint_re] at hh
  norm_num at hh

private theorem phasePoint_norm_sq (t : ℝ) : ‖phaseMellinPoint t‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [phaseMellinPoint] <;> ring

private def logCellPrimitive (t x : ℝ) : ℂ :=
  -(x : ℂ) ^ (-phaseMellinPoint t) *
    (((Real.log x - Real.log t : ℝ) : ℂ) / phaseMellinPoint t +
      1 / (phaseMellinPoint t) ^ 2)

private theorem logCellPrimitive_deriv (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (logCellPrimitive t)
      (((Real.log x - Real.log t : ℝ) : ℂ) * (x : ℂ) ^ (-phaseMellinPoint t - 1)) x := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hp := hasDerivAt_ofReal_cpow_const (ne_of_gt hx)
    (neg_ne_zero.mpr (phasePoint_ne_zero t))
  have hl := ((Real.hasDerivAt_log (ne_of_gt hx)).sub_const (Real.log t)).ofReal_comp
  have hd := hp.neg.mul ((hl.div_const (phaseMellinPoint t)).add_const
    (1 / (phaseMellinPoint t) ^ 2))
  convert! hd using 1
  simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.sub_apply,
    Pi.div_apply, Function.comp_apply, id_eq]
  rw [Complex.cpow_sub _ _ hxC, Complex.cpow_one]
  push_cast
  field_simp [phasePoint_ne_zero t, hxC] <;> ring

/-- Exact integral formula, retaining the original Mellin cell and logarithmic boundary. -/
theorem mellinLogCell_eq (t : ℝ) (n : ℕ) :
    mellinLogCell t n = mellinLogBoundary t n / phaseMellinPoint t +
      ((paretoWeight n : ℂ) * star (compressedMellinCell t n)) / phaseMellinPoint t := by
  let a : ℝ := (n : ℝ) + 1
  let b : ℝ := (n : ℝ) + 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hi : IntervalIntegrable
      (fun x : ℝ => ((Real.log x - Real.log t : ℝ) : ℂ) *
        (x : ℂ) ^ (-phaseMellinPoint t - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    exact (((Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (ne_of_gt hx0)).sub continuousAt_const))).mul
      (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (ne_of_gt hx0)))).continuousWithinAt
  have hJ := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := logCellPrimitive t)
    (fun x hx => logCellPrimitive_deriv t x (by
      rw [uIcc_of_le hab] at hx
      exact ha.trans_le hx.1)) hi
  have hC : (∫ x in derivativeUnitCell n, (x : ℂ) ^ (-phaseMellinPoint t - 1)) =
      (((a : ℂ) ^ (-phaseMellinPoint t) - (b : ℂ) ^ (-phaseMellinPoint t)) /
        phaseMellinPoint t) := by
    have hz : (0 : ℝ) ∉ uIcc a b := by
      rw [uIcc_of_le hab]
      intro h
      linarith [h.1]
    have hs : -phaseMellinPoint t - 1 ≠ (-1 : ℂ) := by
      intro h
      have hh := congrArg Complex.re h
      simp [phaseMellinPoint] at hh
    change (∫ x in Ico a b, (x : ℂ) ^ (-phaseMellinPoint t - 1)) = _
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_cpow (Or.inr ⟨hs, hz⟩)]
    rw [show -phaseMellinPoint t - 1 + 1 = -phaseMellinPoint t by ring]
    ring
  have hC' : (paretoWeight n : ℂ) * star (compressedMellinCell t n) =
      (((a : ℂ) ^ (-phaseMellinPoint t) - (b : ℂ) ^ (-phaseMellinPoint t)) /
        phaseMellinPoint t) := by
    rw [← compressedMellinCell_integral]
    exact hC
  rw [hC']
  unfold mellinLogCell
  change (∫ x in Ico a b, _) = _
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hJ]
  unfold logCellPrimitive mellinLogBoundary
  change -(b : ℂ) ^ (-phaseMellinPoint t) * _ -
    (-(a : ℂ) ^ (-phaseMellinPoint t) * _) = _
  field_simp [phasePoint_ne_zero t]
  ring

/-- Uniform boundary bound on every complete cell below t. -/
theorem mellinLogBoundary_head_bound (t : ℝ) (n : ℕ)
    (ht : (n : ℝ) + 2 ≤ t) :
    ‖mellinLogBoundary t n‖ ^ 2 / paretoWeight n ≤
      6 * Real.log (t / ((n : ℝ) + 1)) ^ 2 := by
  let a : ℝ := (n : ℝ) + 1
  let b : ℝ := (n : ℝ) + 2
  let L : ℝ := Real.log (t / a)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbt : b ≤ t := ht
  have ht0 : 0 < t := hb.trans_le hbt
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div ha).mpr (hab.trans hbt))
  have hla : Real.log a - Real.log t = -L := by
    dsimp [L]
    rw [Real.log_div (ne_of_gt ht0) (ne_of_gt ha)]
    ring
  have hlb0 : Real.log b - Real.log t ≤ 0 :=
    sub_nonpos.mpr (Real.log_le_log hb hbt)
  have hlba : -L ≤ Real.log b - Real.log t := by
    have h := Real.log_le_log ha hab
    linarith
  have hlb : |Real.log b - Real.log t| ≤ L :=
    abs_le.mpr ⟨hlba, hlb0.trans hL⟩
  have hn (x : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (-phaseMellinPoint t)‖ = 1 / x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [phaseMellinPoint, one_div, Real.rpow_neg_one]
  have hnorm : ‖mellinLogBoundary t n‖ ≤ (1 / a + 1 / b) * L := by
    calc
      _ ≤ ‖(a : ℂ) ^ (-phaseMellinPoint t) * ((Real.log a - Real.log t : ℝ) : ℂ)‖ +
          ‖(b : ℂ) ^ (-phaseMellinPoint t) * ((Real.log b - Real.log t : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
      _ = (1 / a) * L + (1 / b) * |Real.log b - Real.log t| := by
        rw [norm_mul, norm_mul, hn a ha, hn b hb]
        simp only [Complex.norm_real, Real.norm_eq_abs, hla, abs_neg, abs_of_nonneg hL]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlb (one_div_nonneg.mpr hb.le)]
  have hweight : (1 / a + 1 / b) ^ 2 / paretoWeight n ≤ 6 := by
    change (1 / a + 1 / b) ^ 2 / (1 / (a * b)) ≤ 6
    rw [div_le_iff₀ (by positivity : 0 < 1 / (a * b))]
    dsimp [a, b]
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (1 / a + 1 / b) * L)).mpr hnorm
  calc
    _ ≤ ((1 / a + 1 / b) * L) ^ 2 / paretoWeight n :=
      div_le_div_of_nonneg_right hsq (paretoWeight_pos n).le
    _ = ((1 / a + 1 / b) ^ 2 / paretoWeight n) * L ^ 2 := by ring
    _ ≤ 6 * L ^ 2 := mul_le_mul_of_nonneg_right hweight (sq_nonneg L)

private theorem norm_add_sq_le_twice (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := norm_add_le z w
  nlinarith [norm_nonneg (z + w), norm_nonneg z, norm_nonneg w, sq_nonneg (‖z‖ - ‖w‖)]

/-- Coordinate derivative energy with its complete cell energy retained. -/
theorem mellinLogCell_head_bound (t : ℝ) (n : ℕ) (ht : (n : ℝ) + 2 ≤ t) :
    ‖mellinLogCell t n‖ ^ 2 / paretoWeight n ≤
      (2 / (1 + t ^ 2)) *
        (6 * Real.log (t / ((n : ℝ) + 1)) ^ 2 +
          paretoWeight n * ‖compressedMellinCell t n‖ ^ 2) := by
  have hc : ‖(paretoWeight n : ℂ) * star (compressedMellinCell t n)‖ ^ 2 /
      paretoWeight n = paretoWeight n * ‖compressedMellinCell t n‖ ^ 2 := by
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (paretoWeight_pos n)]
    field_simp [(paretoWeight_pos n).ne']
  have h := norm_add_sq_le_twice
    (mellinLogBoundary t n / phaseMellinPoint t)
    (((paretoWeight n : ℂ) * star (compressedMellinCell t n)) / phaseMellinPoint t)
  rw [← mellinLogCell_eq, norm_div, norm_div, div_pow, div_pow, phasePoint_norm_sq] at h
  have hh := div_le_div_of_nonneg_right h (paretoWeight_pos n).le
  have hb := mellinLogBoundary_head_bound t n ht
  calc
    _ ≤ (2 / (1 + t ^ 2)) *
        (‖mellinLogBoundary t n‖ ^ 2 / paretoWeight n +
          ‖(paretoWeight n : ℂ) * star (compressedMellinCell t n)‖ ^ 2 / paretoWeight n) := by
      convert! hh using 1 <;> ring
    _ ≤ _ := by
      rw [hc]
      exact mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) (by positivity)

/-- Complete finite-head derivative energy. -/
theorem mellinLogCell_head_energy (t : ℝ) (ht : 1 ≤ t) (N : ℕ)
    (hN : (N : ℝ) + 1 ≤ t) :
    (∑ n ∈ Finset.range N, ‖mellinLogCell t n‖ ^ 2 / paretoWeight n) ≤ 28 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n hn =>
    mellinLogCell_head_bound t n (by
      have hn' : n + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
      have hh : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn'
      linarith))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hlogs := RiemannResearch.Analysis.logSquare_head_sum_le t ht N (by linarith)
  have hcell : (∑ n ∈ Finset.range N,
      paretoWeight n * ‖compressedMellinCell t n‖ ^ 2) ≤ 2 := by
    have h := Summable.sum_le_tsum (s := Finset.range N)
      (f := fun n => paretoWeight n * ‖compressedMellinCell t n‖ ^ 2)
      (fun n _ => mul_nonneg (paretoWeight_pos n).le (sq_nonneg _))
      (compressedMellinCell_square_summable t)
    exact h.trans (compressedMellinEnergy_le_two t)
  have hcalc : (2 / (1 + t ^ 2)) * (12 * t + 2) ≤ 28 / t := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) ht0]
    nlinarith [sq_nonneg (t - 1)]
  calc
    _ ≤ (2 / (1 + t ^ 2)) * (12 * t + 2) := hsum.trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ ≤ _ := hcalc

end RiemannResearch.RH.Pareto.CompressedMellin
