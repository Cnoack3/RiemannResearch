import RiemannResearch.RH.ArithmeticMellinPositiveHalfPlane
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
The exact continuous zero-mode projection, including the complete residual
integral. The Mellin-identity provider is unconditional; a zero is an input
to the projection statement, never an assumption introduced as an axiom.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
open scoped BigOperators
noncomputable section

 theorem arithmeticCombination_bounded (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) :
    ∃ C : ℝ, ∀ k, |arithmeticCombination c k| ≤ C := by
  refine ⟨∑ p ∈ c.support, |c p| * ((p.2 : ℝ) * (p.1 : ℝ)), ?_⟩
  intro k
  unfold arithmeticCombination
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro p hp
  obtain ⟨ha, hm⟩ := hc p hp
  have ha0 : 0 < p.1 := by rcases ha with ha | ha <;> omega
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (dilation_abs_le (fun j => residue_abs_le p.1 j ha0) p.2 k) (abs_nonneg _)

 theorem arithmeticCombination_error_summable (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) :
    Summable (fun k => positiveWeight k * (1 - arithmeticCombination c k)^2) := by
  obtain ⟨C, hC⟩ := arithmeticCombination_bounded c hc
  exact weighted_summable_of_bounded (error_square_bounded hC)

 theorem arithmeticErrorMellin_at_zero (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hρpos : 0 < ρ.re) (hρupper : ρ.re < 1) :
    IntegrableOn (fun x : ℝ => (1 - arithmeticStep c x) * (x : ℂ)^(-ρ - 1))
      (Ioi 1) ∧
    (∫ x in Ioi (1 : ℝ), (1 - arithmeticStep c x) * (x : ℂ)^(-ρ - 1)) = 1 / ρ := by
  obtain ⟨hstep, hstepIntegral⟩ := arithmeticMellinIdentityTarget_proved c hc ρ hρpos hρupper
  have hp : (-ρ - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hpow := integrableOn_Ioi_cpow_of_lt hp (by norm_num : (0 : ℝ) < 1)
  have he : (fun x : ℝ => (1 - arithmeticStep c x) * (x : ℂ)^(-ρ - 1)) =
      fun x : ℝ => (x : ℂ)^(-ρ - 1) - arithmeticStep c x * (x : ℂ)^(-ρ - 1) := by
    funext x
    ring
  rw [he]
  refine ⟨hpow.sub hstep, ?_⟩
  rw [integral_sub hpow hstep, hstepIntegral, hρ,
    integral_Ioi_cpow_of_lt hp (by norm_num : (0 : ℝ) < 1)]
  simp

private theorem zeroProjection_cross_identity (a A ρ : ℂ) (x : ℝ) (hx : 0 < x) :
    (a / (x : ℂ)) * star (A * (x : ℂ)^(-star ρ)) =
      star A * (a * (x : ℂ)^(-ρ - 1)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos.ne
  have hconj : star ((x : ℂ)^(-star ρ)) = (x : ℂ)^(-ρ) := by
    simpa using (Complex.conj_cpow (x : ℂ) (-ρ) harg).symm
  rw [star_mul, hconj, Complex.cpow_sub (-ρ) 1 hxC, Complex.cpow_one]
  ring

private theorem zeroProjection_expansion (a : ℝ) (A ρ : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖(a : ℂ) - A * hypotheticalZeroMode ρ x‖^2 / x^2 =
      a^2 / x^2 + ‖A‖^2 * x^(-(2 * ρ.re)) -
        2 * (star A * ((a : ℂ) * (x : ℂ)^(-ρ - 1))).re := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpower : (x : ℂ)^(1 - star ρ) = (x : ℂ) * (x : ℂ)^(-star ρ) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hxC, Complex.cpow_one]
  have hquot : ((a : ℂ) - A * hypotheticalZeroMode ρ x) / (x : ℂ) =
      (a : ℂ) / (x : ℂ) - A * (x : ℂ)^(-star ρ) := by
    unfold hypotheticalZeroMode
    rw [hpower]
    field_simp
    <;> ring
  have hnorma : ‖(a : ℂ) / (x : ℂ)‖^2 = a^2 / x^2 := by
    simp only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnormv : ‖A * (x : ℂ)^(-star ρ)‖^2 = ‖A‖^2 * x^(-(2 * ρ.re)) := by
    rw [norm_mul, mul_pow]
    congr 1
    simpa [paretoMellinKernel] using paretoMellinKernel_norm_sq (star ρ) hx
  calc
    _ = ‖(a : ℂ) / (x : ℂ) - A * (x : ℂ)^(-star ρ)‖^2 := by
      rw [← hquot]
      simp only [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ‖(a : ℂ) / (x : ℂ)‖^2 + ‖A * (x : ℂ)^(-star ρ)‖^2 -
        2 * (((a : ℂ) / (x : ℂ)) * star (A * (x : ℂ)^(-star ρ))).re := by
      simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using
        Complex.normSq_sub ((a : ℂ) / (x : ℂ)) (A * (x : ℂ)^(-star ρ))
    _ = _ := by rw [hnorma, hnormv, zeroProjection_cross_identity _ _ _ _ hx]

private theorem zeroProjection_constants (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re) :
    let α := 2 * ρ.re - 1
    let A : ℂ := (α : ℂ) / ρ
    ‖A‖^2 * (1 / α) - 2 * (star A * (1 / ρ)).re = -α / ‖ρ‖^2 := by
  dsimp only
  have hα : 0 < 2 * ρ.re - 1 := by linarith
  have hρ0 : ρ ≠ 0 := by
    intro hz
    simp [hz] at hρ
    linarith
  have hn : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hρ0
  have hprod : ρ * star ρ = ((‖ρ‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow, Complex.star_def] using Complex.mul_conj' ρ
  have hcross : (star (((2 * ρ.re - 1 : ℝ) : ℂ) / ρ) * (1 / ρ)).re =
      (2 * ρ.re - 1) / ‖ρ‖^2 := by
    calc
      _ = (((2 * ρ.re - 1 : ℝ) : ℂ) / (ρ * star ρ)).re := by
        congr 1
        have hreal : star (((2 * ρ.re - 1 : ℝ) : ℂ)) =
            (((2 * ρ.re - 1 : ℝ) : ℂ)) := by
          rw [Complex.star_def, Complex.conj_ofReal]
        rw [star_div₀, hreal]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hprod, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hcross, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  field_simp [hρ0, hn, hα.ne']
  <;> ring

/-- Exact Pythagorean decomposition against the continuous off-line zero mode. -/
theorem arithmeticZeroProjectionTarget : ArithmeticZeroProjectionTarget := by
  intro ρ hzero hρ hupper c hc
  let α : ℝ := 2 * ρ.re - 1
  let A : ℂ := (α : ℂ) / ρ
  let f : ℕ → ℝ := fun k => 1 - arithmeticCombination c k
  let E : ℝ → ℝ := fun x => f ⌊x⌋₊ ^ 2 / x^2
  let M : ℝ → ℂ := fun x => (1 - arithmeticStep c x) * (x : ℂ)^(-ρ - 1)
  let P : ℝ → ℝ := fun x => x^(-(2 * ρ.re))
  have hα : 0 < α := by dsimp [α]; linarith
  have hf : Summable (fun k => positiveWeight k * f k^2) :=
    arithmeticCombination_error_summable c hc
  have hE : IntegrableOn E (Ioi 1) := paretoStepEnergy_integrable f hf
  have hEI : (∫ x in Ioi (1 : ℝ), E x) = arithmeticFullError c :=
    paretoStep_energy_identity f hf
  obtain ⟨hM, hMI⟩ := arithmeticErrorMellin_at_zero c hc ρ hzero (by linarith) hupper
  change IntegrableOn M (Ioi 1) at hM
  change (∫ x in Ioi (1 : ℝ), M x) = 1 / ρ at hMI
  have hP : IntegrableOn P (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -(2 * ρ.re) < -1)
      (by norm_num : (0 : ℝ) < 1)
  have hPI : (∫ x in Ioi (1 : ℝ), P x) = 1 / α := by
    rw [show P = (fun x : ℝ => x^(-(2 * ρ.re))) from rfl,
      integral_Ioi_rpow_of_lt (by linarith : -(2 * ρ.re) < -1)
        (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.one_rpow]
    rw [show -(2 * ρ.re) + 1 = -α by dsimp [α]; ring, div_neg]
    ring
  have hcross : IntegrableOn (fun x => (star A * M x).re) (Ioi 1) :=
    (hM.const_mul (star A)).re
  have hcrossI : (∫ x in Ioi (1 : ℝ), (star A * M x).re) =
      (star A * (1 / ρ)).re := by
    have hr : (∫ x in Ioi (1 : ℝ), (star A * M x).re) =
        (∫ x in Ioi (1 : ℝ), star A * M x).re := by
      simpa only using! integral_re (hM.const_mul (star A))
    rw [hr, integral_const_mul, hMI]
  have he : (∫ x in Ioi (1 : ℝ),
      ‖1 - arithmeticStep c x - A * hypotheticalZeroMode ρ x‖^2 / x^2) =
      arithmeticFullError c + ‖A‖^2 * (1 / α) -
        2 * (star A * (1 / ρ)).re := by
    calc
      _ = ∫ x in Ioi (1 : ℝ), E x + ‖A‖^2 * P x - 2 * (star A * M x).re := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hfx : ((f ⌊x⌋₊ : ℝ) : ℂ) = 1 - arithmeticStep c x := by
          simp [f, arithmeticStep, Complex.ofReal_sub]
        simpa only [E, P, M, hfx] using
          zeroProjection_expansion (f ⌊x⌋₊) A ρ x (lt_trans zero_lt_one hx)
      _ = _ := by
        have hEP : IntegrableOn (fun x : ℝ => E x + ‖A‖^2 * P x) (Ioi 1) := by
          simpa only [Pi.add_apply] using! hE.add (hP.const_mul (‖A‖^2))
        rw [integral_sub hEP (hcross.const_mul 2),
          integral_add hE (hP.const_mul (‖A‖^2)), integral_const_mul,
          integral_const_mul, hEI, hPI, hcrossI]
  have hconstant : ‖A‖^2 * (1 / α) - 2 * (star A * (1 / ρ)).re =
      -α / ‖ρ‖^2 := zeroProjection_constants ρ hρ
  rw [neg_div] at hconstant
  change arithmeticFullError c = α / ‖ρ‖^2 + _
  change arithmeticFullError c = α / ‖ρ‖^2 +
    (∫ x in Ioi (1 : ℝ),
      ‖1 - arithmeticStep c x - A * hypotheticalZeroMode ρ x‖^2 / x^2)
  rw [he]
  linarith

end
end RiemannResearch.RH.Pareto
