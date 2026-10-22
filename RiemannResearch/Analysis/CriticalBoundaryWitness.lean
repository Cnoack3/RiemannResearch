import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Explicit unit-energy witnesses for unbounded critical-line Mellin evaluation

These witnesses live in the ambient Pareto L2 space. They are not asserted to
be legal Nyman--Beurling corrections. Thus no approximation theorem or RH is
inferred from the failure of bounded boundary evaluation.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.CriticalBoundaryWitness

def criticalPoint (γ : ℝ) : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I

@[simp] lemma criticalPoint_re (γ : ℝ) : (criticalPoint γ).re = 1 / 2 := by
  simp [criticalPoint]

def witness (R γ : ℝ) : ℝ → ℂ :=
  (Ioc 1 (Real.exp R)).indicator
    (fun x => (x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ))

def energy (f : ℝ → ℂ) : ℝ := ∫ x : ℝ in Ioi 1, ‖f x‖ ^ 2 / x ^ 2

def mellinValue (f : ℝ → ℂ) (γ : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 1, f x * (x : ℂ) ^ (-criticalPoint γ - 1)

lemma inverse_integral (R : ℝ) (hR : 0 < R) :
    (∫ x : ℝ in Ioc 1 (Real.exp R), x⁻¹) = R := by
  rw [← intervalIntegral.integral_of_le (Real.one_le_exp_iff.mpr hR.le),
    integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (Real.exp_pos R)]
  simp

lemma sqrt_ne_zero (R : ℝ) (hR : 0 < R) : (Real.sqrt R : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hR)

lemma witness_norm_integrand (R γ x : ℝ) (hR : 0 < R) (hx : 0 < x) :
    ‖(x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ)‖ ^ 2 / x ^ 2 = x⁻¹ / R := by
  rw [norm_div, div_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, criticalPoint_re,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg R), Real.sq_sqrt hR.le]
  field_simp

lemma witness_mellin_integrand (R γ x : ℝ) (hx : 0 < x) :
    ((x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ)) *
      (x : ℂ) ^ (-criticalPoint γ - 1) = ((x⁻¹ : ℝ) : ℂ) / (Real.sqrt R : ℂ) := by
  rw [div_mul_eq_mul_div, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  have he : criticalPoint γ + (-criticalPoint γ - 1) = (-1 : ℂ) := by ring
  rw [he]
  simp [Complex.cpow_neg_one]

lemma restrict_indicator (R : ℝ) (f : ℝ → ℂ) :
    (∫ x : ℝ in Ioi 1, (Ioc 1 (Real.exp R)).indicator f x) =
      ∫ x : ℝ in Ioc 1 (Real.exp R), f x := by
  rw [setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (show Ioc 1 (Real.exp R) ⊆ Ioi 1 from fun x hx => hx.1)]

lemma restrict_indicator_real (R : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ in Ioi 1, (Ioc 1 (Real.exp R)).indicator f x) =
      ∫ x : ℝ in Ioc 1 (Real.exp R), f x := by
  rw [setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (show Ioc 1 (Real.exp R) ⊆ Ioi 1 from fun x hx => hx.1)]

/-- The explicit witnesses have exactly unit Pareto L2 energy. -/
theorem witness_energy_one (R γ : ℝ) (hR : 0 < R) : energy (witness R γ) = 1 := by
  unfold energy witness
  have hi (x : ℝ) :
      ‖(Ioc 1 (Real.exp R)).indicator
        (fun x => (x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ)) x‖ ^ 2 / x ^ 2 =
      (Ioc 1 (Real.exp R)).indicator
        (fun x => ‖(x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ)‖ ^ 2 / x ^ 2) x := by
    by_cases hx : x ∈ Ioc 1 (Real.exp R) <;> simp [hx]
  simp_rw [hi]
  rw [restrict_indicator_real]
  calc
    _ = ∫ x : ℝ in Ioc 1 (Real.exp R), x⁻¹ / R := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact witness_norm_integrand R γ x hR (lt_trans zero_lt_one hx.1)
    _ = 1 := by rw [integral_div, inverse_integral R hR, div_self hR.ne']

/-- Their critical-line Mellin values grow as sqrt(R). -/
theorem witness_mellin_value (R γ : ℝ) (hR : 0 < R) :
    mellinValue (witness R γ) γ = (Real.sqrt R : ℂ) := by
  unfold mellinValue witness
  have hi (x : ℝ) :
      (Ioc 1 (Real.exp R)).indicator
        (fun x => (x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ)) x *
          (x : ℂ) ^ (-criticalPoint γ - 1) =
      (Ioc 1 (Real.exp R)).indicator
        (fun x => ((x : ℂ) ^ criticalPoint γ / (Real.sqrt R : ℂ)) *
          (x : ℂ) ^ (-criticalPoint γ - 1)) x := by
    by_cases hx : x ∈ Ioc 1 (Real.exp R) <;> simp [hx]
  simp_rw [hi]
  rw [restrict_indicator]
  calc
    _ = ∫ x : ℝ in Ioc 1 (Real.exp R), ((x⁻¹ : ℝ) : ℂ) / (Real.sqrt R : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact witness_mellin_integrand R γ x (lt_trans zero_lt_one hx.1)
    _ = (R : ℂ) / (Real.sqrt R : ℂ) := by
      rw [integral_div, integral_complex_ofReal, inverse_integral R hR]
    _ = _ := by
      apply (div_eq_iff (sqrt_ne_zero R hR)).mpr
      norm_cast
      nlinarith [Real.sq_sqrt hR.le]

/-- The boundary evaluation is unbounded on the unit-energy sphere. -/
theorem boundary_evaluation_unbounded (γ C : ℝ) :
    ∃ f : ℝ → ℂ, energy f = 1 ∧ C < ‖mellinValue f γ‖ := by
  let R : ℝ := (|C| + 1) ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨witness R γ, witness_energy_one R γ hR, ?_⟩
  rw [witness_mellin_value R γ hR, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg R)]
  have he : Real.sqrt R = |C| + 1 := by
    dsimp [R]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < |C| + 1)]
  rw [he]
  linarith [le_abs_self C]

/-- In particular no global energy-to-boundary-evaluation constant exists. -/
theorem no_uniform_boundary_bound (γ : ℝ) :
    ¬ ∃ C : ℝ, ∀ f : ℝ → ℂ, energy f = 1 → ‖mellinValue f γ‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨f, hf, hlarge⟩ := boundary_evaluation_unbounded γ C
  exact (not_le_of_gt hlarge) (hC f hf)

/-- The unit-energy claim is supported by a genuine integrable energy density. -/
theorem witness_energy_integrable (R γ : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => ‖witness R γ x‖ ^ 2 / x ^ 2) (Ioi 1) := by
  by_contra h
  have hz := integral_undef h
  have he := witness_energy_one R γ hR
  change (∫ x : ℝ in Ioi 1, ‖witness R γ x‖ ^ 2 / x ^ 2) = 1 at he
  rw [hz] at he
  norm_num at he

/-- Boundary values here are convergent integrals, not default values assigned
to nonintegrable functions. -/
theorem witness_mellin_integrable (R γ : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => witness R γ x * (x : ℂ) ^ (-criticalPoint γ - 1)) (Ioi 1) := by
  by_contra h
  have hz := integral_undef h
  have he := witness_mellin_value R γ hR
  change (∫ x : ℝ in Ioi 1, witness R γ x * (x : ℂ) ^ (-criticalPoint γ - 1)) = (Real.sqrt R : ℂ) at he
  rw [hz] at he
  exact (sqrt_ne_zero R hR) he.symm

end RiemannResearch.Analysis.CriticalBoundaryWitness
