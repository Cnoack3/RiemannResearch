import RiemannResearch.Analysis.LogarithmicTentIntegral

/-!
# Complex Mellin integral of the actual root tent

Source: user-provided FourierBridgeUniformSignedEnergy20260910.md, Section 2.
The integral formula and its proof are formalized here for the existing rootTent.

The complex exponent is `s - 1`, so the denominator is `s * (s + 1)`.
The exceptional parameters are `s = 0` and `s = -1`.  In particular,
`s = -I * ω`, `ω ≠ 0`, supplies the nonzero Fourier coefficients.
-/

noncomputable section

open MeasureTheory

namespace RiemannResearch.Analysis

private theorem integral_complex_power_of_pos {a b : ℝ} {s : ℂ}
    (ha : 0 < a) (hb : 0 < b) (hs : s ≠ -1) :
    (∫ x in a..b, (x : ℂ) ^ s) =
      ((b : ℂ) ^ (s + 1) - (a : ℂ) ^ (s + 1)) / (s + 1) := by
  exact integral_cpow (Or.inr ⟨hs, Set.notMem_uIcc_of_lt ha hb⟩)

private theorem complex_power_intervalIntegrable_of_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ s) volume a b := by
  exact intervalIntegral.intervalIntegrable_cpow
    (Or.inr (Set.notMem_uIcc_of_lt ha hb))

theorem rootTent_mul_cpow_intervalIntegrable {a b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    IntervalIntegrable (fun x => (rootTent a x : ℂ) * (x : ℂ) ^ s)
      volume b c := by
  exact (complex_power_intervalIntegrable_of_pos hb hc s).continuousOn_mul
    (Complex.continuous_ofReal.comp (continuous_rootTent a)).continuousOn

private theorem complex_mul_cpow_sub_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (s - 1) = (x : ℂ) ^ s := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have h := Complex.cpow_add (s - 1) 1 hx0
  simpa only [sub_add_cancel, Complex.cpow_one, mul_comm] using h.symm

theorem integral_rootTent_mul_cpow_left {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    (∫ x in a..a + 1, (rootTent a x : ℂ) * (x : ℂ) ^ (s - 1)) =
      (((a + 1 : ℝ) : ℂ) ^ (s + 1) - (a : ℂ) ^ (s + 1)) / (s + 1) -
        (a : ℂ) * ((((a + 1 : ℝ) : ℂ) ^ s - (a : ℂ) ^ s) / s) := by
  have ha1 : 0 < a + 1 := by linarith
  have hs' : s - 1 ≠ -1 := by
    intro h
    apply hs0
    have h' := congrArg (fun z : ℂ => z + 1) h
    simpa using h'
  have hi := complex_power_intervalIntegrable_of_pos ha ha1 s
  have hj := complex_power_intervalIntegrable_of_pos ha ha1 (s - 1)
  calc
    (∫ x in a..a + 1, (rootTent a x : ℂ) * (x : ℂ) ^ (s - 1)) =
        ∫ x in a..a + 1, (x : ℂ) ^ s - (a : ℂ) * (x : ℂ) ^ (s - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (show a ≤ a + 1 by linarith)] at hx
      dsimp only
      rw [rootTent_eq_left hx.1 hx.2, Complex.ofReal_sub, sub_mul,
        complex_mul_cpow_sub_one (lt_of_lt_of_le ha hx.1)]
    _ = _ := by
      rw [intervalIntegral.integral_sub hi (hj.const_mul (a : ℂ)),
        intervalIntegral.integral_const_mul,
        integral_complex_power_of_pos ha ha1 hs1,
        integral_complex_power_of_pos ha ha1 hs']
      simp only [sub_add_cancel]

theorem integral_rootTent_mul_cpow_right {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    (∫ x in a + 1..a + 2, (rootTent a x : ℂ) * (x : ℂ) ^ (s - 1)) =
      ((a + 2 : ℝ) : ℂ) *
        ((((a + 2 : ℝ) : ℂ) ^ s - ((a + 1 : ℝ) : ℂ) ^ s) / s) -
      ((((a + 2 : ℝ) : ℂ) ^ (s + 1) -
        ((a + 1 : ℝ) : ℂ) ^ (s + 1)) / (s + 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have hs' : s - 1 ≠ -1 := by
    intro h
    apply hs0
    have h' := congrArg (fun z : ℂ => z + 1) h
    simpa using h'
  have hi := complex_power_intervalIntegrable_of_pos ha1 ha2 s
  have hj := complex_power_intervalIntegrable_of_pos ha1 ha2 (s - 1)
  calc
    (∫ x in a + 1..a + 2, (rootTent a x : ℂ) * (x : ℂ) ^ (s - 1)) =
        ∫ x in a + 1..a + 2,
          ((a + 2 : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) - (x : ℂ) ^ s := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (show a + 1 ≤ a + 2 by linarith)] at hx
      dsimp only
      rw [rootTent_eq_right hx.1 hx.2, Complex.ofReal_sub, sub_mul,
        complex_mul_cpow_sub_one (lt_of_lt_of_le ha1 hx.1)]
    _ = _ := by
      rw [intervalIntegral.integral_sub (hj.const_mul ((a + 2 : ℝ) : ℂ)) hi,
        intervalIntegral.integral_const_mul,
        integral_complex_power_of_pos ha1 ha2 hs',
        integral_complex_power_of_pos ha1 ha2 hs1]
      simp only [sub_add_cancel]

/-- The exact Mellin integral giving all nonzero logarithmic Fourier modes. -/
theorem integral_rootTent_mul_cpow {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    (∫ x in a..a + 2, (rootTent a x : ℂ) * (x : ℂ) ^ (s - 1)) =
      ((a : ℂ) ^ (s + 1) - 2 * ((a + 1 : ℝ) : ℂ) ^ (s + 1) +
        ((a + 2 : ℝ) : ℂ) ^ (s + 1)) / (s * (s + 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have ha10 : ((a + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha1
  have ha20 : ((a + 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha2
  have hs10 : s + 1 ≠ 0 := by
    intro h
    apply hs1
    calc
      s = (s + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  have hiL := rootTent_mul_cpow_intervalIntegrable (a := a) ha ha1 (s - 1)
  have hiR := rootTent_mul_cpow_intervalIntegrable (a := a) ha1 ha2 (s - 1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR,
    integral_rootTent_mul_cpow_left ha hs0 hs1,
    integral_rootTent_mul_cpow_right ha hs0 hs1]
  rw [Complex.cpow_add s 1 ha0, Complex.cpow_add s 1 ha10,
    Complex.cpow_add s 1 ha20]
  simp only [Complex.cpow_one, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  field_simp [hs0, hs10]
  ring


/-- The nonzero imaginary Mellin parameter occurring in logarithmic Fourier analysis. -/
theorem integral_rootTent_fourier_kernel {a ω : ℝ} (ha : 0 < a) (hω : ω ≠ 0) :
    (∫ x in a..a + 2,
      (rootTent a x : ℂ) * (x : ℂ) ^ (-Complex.I * (ω : ℂ) - 1)) =
      ((a : ℂ) ^ (-Complex.I * (ω : ℂ) + 1) -
          2 * ((a + 1 : ℝ) : ℂ) ^ (-Complex.I * (ω : ℂ) + 1) +
          ((a + 2 : ℝ) : ℂ) ^ (-Complex.I * (ω : ℂ) + 1)) /
        ((-Complex.I * (ω : ℂ)) * (-Complex.I * (ω : ℂ) + 1)) := by
  have hs0 : -Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (by exact_mod_cast hω)
  have hs1 : -Complex.I * (ω : ℂ) ≠ -1 := by
    intro h
    have h' := congrArg Complex.re h
    simp [Complex.mul_re] at h'
  exact integral_rootTent_mul_cpow ha hs0 hs1

/-- At frequency zero the complex integral agrees with the real log second difference. -/
theorem integral_rootTent_cpow_neg_one {a : ℝ} (ha : 0 < a) :
    (∫ x in a..a + 2, (rootTent a x : ℂ) * (x : ℂ) ^ (-1 : ℂ)) =
      ((a * Real.log a - 2 * (a + 1) * Real.log (a + 1) +
        (a + 2) * Real.log (a + 2) : ℝ) : ℂ) := by
  calc
    (∫ x in a..a + 2, (rootTent a x : ℂ) * (x : ℂ) ^ (-1 : ℂ)) =
        ∫ x in a..a + 2, ((rootTent a x / x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Complex.cpow_neg_one, div_eq_mul_inv,
        Complex.ofReal_mul, Complex.ofReal_inv]
    _ = _ := by
      rw [intervalIntegral.integral_ofReal, integral_rootTent_div ha]

end RiemannResearch.Analysis


/-! Explicit inverse-square frequency decay of the actual tent Mellin integral. -/

noncomputable section

open MeasureTheory

namespace RiemannResearch.Analysis

private theorem norm_cpow_imaginary_add_one {x ω : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-Complex.I * (ω : ℂ) + 1)‖ = x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.mul_re]

theorem sq_le_norm_imaginary_mellin_denominator (ω : ℝ) :
    ω ^ 2 ≤ ‖(-Complex.I * (ω : ℂ)) * (-Complex.I * (ω : ℂ) + 1)‖ := by
  have hfirst : ‖-Complex.I * (ω : ℂ)‖ = |ω| := by
    simp [Real.norm_eq_abs]
  have hsecond : |ω| ≤ ‖-Complex.I * (ω : ℂ) + 1‖ := by
    simpa [Complex.mul_im] using
      Complex.abs_im_le_norm (-Complex.I * (ω : ℂ) + 1)
  calc
    ω ^ 2 = |ω| * |ω| := by rw [← sq_abs ω]; ring
    _ ≤ |ω| * ‖-Complex.I * (ω : ℂ) + 1‖ :=
      mul_le_mul_of_nonneg_left hsecond (abs_nonneg ω)
    _ = _ := by rw [norm_mul, hfirst]

/-- A concrete `O(a / ω²)` estimate, proved from the exact actual Mellin integral. -/
theorem norm_integral_rootTent_fourier_kernel_le {a ω : ℝ}
    (ha : 0 < a) (hω : ω ≠ 0) :
    ‖∫ x in a..a + 2,
      (rootTent a x : ℂ) * (x : ℂ) ^ (-Complex.I * (ω : ℂ) - 1)‖ ≤
        4 * (a + 1) / ω ^ 2 := by
  let u : ℂ := (a : ℂ) ^ (-Complex.I * (ω : ℂ) + 1)
  let v : ℂ := ((a + 1 : ℝ) : ℂ) ^ (-Complex.I * (ω : ℂ) + 1)
  let w : ℂ := ((a + 2 : ℝ) : ℂ) ^ (-Complex.I * (ω : ℂ) + 1)
  have hu : ‖u‖ = a := norm_cpow_imaginary_add_one ha
  have hv : ‖v‖ = a + 1 := norm_cpow_imaginary_add_one (by linarith)
  have hw : ‖w‖ = a + 2 := norm_cpow_imaginary_add_one (by linarith)
  have hnum : ‖u - 2 * v + w‖ ≤ 4 * (a + 1) := by
    calc
      ‖u - 2 * v + w‖ ≤ ‖u - 2 * v‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖(2 : ℂ) * v‖ + ‖w‖ := by
        linarith [norm_sub_le u ((2 : ℂ) * v)]
      _ = 4 * (a + 1) := by rw [norm_mul, hu, hv, hw]; norm_num; ring
  rw [integral_rootTent_fourier_kernel ha hω, norm_div]
  change ‖u - 2 * v + w‖ /
      ‖(-Complex.I * (ω : ℂ)) * (-Complex.I * (ω : ℂ) + 1)‖ ≤ _
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hω)
      (sq_le_norm_imaginary_mellin_denominator ω))

end RiemannResearch.Analysis
