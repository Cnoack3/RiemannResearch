import RiemannResearch.RH.MellinProjectionDPP
import RiemannResearch.RH.ResidueGramDigamma
import RiemannResearch.RH.MellinFrequencyKernel
/-!
# Uniform Mellin intensity and its exact critical-line zero set

Source: the user's DPP/Mellin research request, 28 September 2026.
The proof uses the established Gram--Schmidt expansion and the exact first
mode. The lower constant is independent of rank and frequency. No RH,
zero-existence, or inverse-Gram growth premise occurs.

The companion note MellinDPPArithmeticBounds20260928.md develops the
higher-point dyadic comparison on paper; those further results are not
claimed to be kernel-verified by this module.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MellinFrequency
open CoefficientStabilization
theorem diagonal_eq_sum_norm_sq (n : ℕ) (t : ℝ) :
    (kernel n t t).re = ∑ i : Fin n, ‖modeFeature i.val t‖ ^ 2 := by
  rw [kernel_eq_mode_sum]
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_re]
theorem first_mode_le_diagonal (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖modeFeature 0 t‖ ^ 2 ≤ (kernel n t t).re := by
  rw [diagonal_eq_sum_norm_sq]
  cases n with
  | zero => omega
  | succ m =>
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi => sq_nonneg _))
theorem modeFeature_zero_formula (t : ℝ) :
    modeFeature 0 t =
      ((2 / Real.sqrt (Real.log 2) : ℝ) : ℂ) *
        (zetaEnvelope t * residueSymbol 0 t) := by
  rw [modeFeature, residueMode_zero, paretoMellin_smul,
    residueAtom_transform]
  rfl
theorem residueSymbol_zero_ne_zero (t : ℝ) : residueSymbol 0 t ≠ 0 := by
  have hp : ‖(2 : ℂ) ^ (-criticalPoint t)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [← norm_pow, pow_two, ← Complex.cpow_add _ _ (by norm_num)]
    change ‖((2 : ℝ) : ℂ) ^ (-criticalPoint t + -criticalPoint t)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num [Real.rpow_neg_one]
  intro h
  have he : (2 : ℂ) ^ (-criticalPoint t) = 1 / 2 := by
    simpa [residueSymbol] using (sub_eq_zero.mp h).symm
  rw [he] at hp
  norm_num at hp
theorem mellin_diagonal_zero_iff (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (kernel n t t).re = 0 ↔ riemannZeta (criticalPoint t) = 0 := by
  constructor
  · intro hz
    have hm := first_mode_le_diagonal n hn t
    rw [hz] at hm
    have hmode : modeFeature 0 t = 0 := norm_eq_zero.mp
      (by nlinarith [norm_nonneg (modeFeature 0 t)])
    rw [modeFeature_zero_formula] at hmode
    have hc : ((2 / Real.sqrt (Real.log 2) : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (div_ne_zero (by norm_num)
          (ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))))
    have he : zetaEnvelope t = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hmode).resolve_left hc)).resolve_right
        (residueSymbol_zero_ne_zero t)
    exact (div_eq_zero_iff.mp he).resolve_right (criticalPoint_ne_zero t)
  · intro hz
    rw [kernel_row_zero_of_zeta_zero n hz t]
    rfl
theorem first_atom_intensity_bound (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (4 / Real.log 2) * ‖zetaEnvelope t‖ ^ 2 *
      ‖residueSymbol 0 t‖ ^ 2 ≤ (kernel n t t).re := by
  have h := first_mode_le_diagonal n hn t
  rw [modeFeature_zero_formula, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, div_pow,
    Real.sq_sqrt (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le] at h
  norm_num only [show (2 : ℝ)^2 = 4 by norm_num] at h
  nlinarith only [h]
theorem residueSymbol_zero_norm_sq_lower (t : ℝ) :
    (3 - 2 * Real.sqrt 2) / 4 ≤ ‖residueSymbol 0 t‖ ^ 2 := by
  have hp : ‖(2 : ℂ) ^ (-criticalPoint t)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [← norm_pow, pow_two, ← Complex.cpow_add _ _ (by norm_num)]
    change ‖((2 : ℝ) : ℂ) ^ (-criticalPoint t + -criticalPoint t)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num [Real.rpow_neg_one]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : ‖(2 : ℂ) ^ (-criticalPoint t)‖ = Real.sqrt 2 / 2 := by
    nlinarith [norm_nonneg ((2 : ℂ) ^ (-criticalPoint t)), Real.sqrt_nonneg 2]
  have hd := norm_sub_norm_le ((2 : ℂ) ^ (-criticalPoint t)) (1 / 2 : ℂ)
  rw [hn, norm_sub_rev] at hd
  have hsym : residueSymbol 0 t = 1 / 2 - (2 : ℂ) ^ (-criticalPoint t) := by
    simp [residueSymbol]
  rw [← hsym] at hd
  norm_num at hd
  have hr : 0 ≤ Real.sqrt 2 / 2 - 1 / 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hsq := mul_self_le_mul_self hr
    (show Real.sqrt 2 / 2 - 1 / 2 ≤ ‖residueSymbol 0 t‖ by linarith)
  nlinarith only [hsq, hs]
theorem first_atom_intensity_uniform_bound (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ((3 - 2 * Real.sqrt 2) / Real.log 2) * ‖zetaEnvelope t‖ ^ 2 ≤
      (kernel n t t).re := by
  have h := first_atom_intensity_bound n hn t
  have hlow := residueSymbol_zero_norm_sq_lower t
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hlow
    (show 0 ≤ (4 / Real.log 2) * ‖zetaEnvelope t‖ ^ 2 by positivity)
  have he : (4 / Real.log 2) * ‖zetaEnvelope t‖ ^ 2 *
      ((3 - 2 * Real.sqrt 2) / 4) =
      ((3 - 2 * Real.sqrt 2) / Real.log 2) * ‖zetaEnvelope t‖ ^ 2 := by ring
  rw [he] at hm
  exact hm.trans h

end RiemannResearch.RH.Pareto.MellinFrequency
