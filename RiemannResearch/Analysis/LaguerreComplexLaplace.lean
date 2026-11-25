import RiemannResearch.Analysis.LaguerreMomentTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Laplace transforms of the ordinary Laguerre polynomials at complex arguments -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

private def laplaceMonomial (s : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)^j * Complex.exp (-s * (x : ℂ))

private theorem laplaceMonomial_integrable {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    IntegrableOn (laplaceMonomial s j) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x^j * Real.exp (-s.re * x)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (j : ℝ))
        (b := s.re) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg j)) zero_lt_one hs)
  refine h.mono' (by unfold laplaceMonomial; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
  simp [laplaceMonomial, norm_mul, norm_pow, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
    Complex.mul_re, Complex.neg_re]

private theorem laplaceMonomial_integral {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    ∫ x in Ioi 0, laplaceMonomial s j x = (j.factorial : ℂ) / s^(j+1) := by
  have hs0 : s ≠ 0 := fun h => by simpa [h] using hs
  induction j with
  | zero =>
    simpa [laplaceMonomial] using
      (integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) (0 : ℝ))
  | succ j ih =>
    let g := fun x : ℝ =>
      ((j+1 : ℕ) : ℂ) * laplaceMonomial s j x +
        (-s) * laplaceMonomial s (j+1) x
    have hg : ∀ x, HasDerivAt (laplaceMonomial s (j+1)) (g x) x := by
      intro x
      have hpow := (hasDerivAt_id (x : ℂ)).pow (j+1)
      have hexp := ((hasDerivAt_id (x : ℂ)).const_mul (-s)).cexp
      convert (hpow.mul hexp).comp_ofReal using 1 <;>
        first
        | (apply funext; intro y; simp [laplaceMonomial, g, Function.comp_def, Pi.pow_apply,
            Pi.mul_apply, pow_add, neg_mul, mul_comm, mul_left_comm, mul_assoc] <;> ring)
        | (simp [laplaceMonomial, g, Function.comp_def, Pi.pow_apply, Pi.mul_apply] <;> ring)
    have hA := (laplaceMonomial_integrable hs j).const_mul ((j+1 : ℕ) : ℂ)
    have hB := (laplaceMonomial_integrable hs (j+1)).const_mul (-s)
    have hgint : IntegrableOn g (Ioi 0) := hA.add hB
    have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (a := (0 : ℝ)) (fun x _ => hg x) hgint (laplaceMonomial_integrable hs (j+1))
    have he := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0 : ℝ)) (fun x _ => hg x) hgint ht
    dsimp only [g] at he
    rw [integral_add hA hB, integral_const_mul, integral_const_mul] at he
    have h0 : laplaceMonomial s (j+1) 0 = 0 := by simp [laplaceMonomial]
    rw [h0, sub_self] at he
    calc
      ∫ x in Ioi 0, laplaceMonomial s (j+1) x =
          ((j+1 : ℕ) : ℂ) * (∫ x in Ioi 0, laplaceMonomial s j x) / s := by
        apply (eq_div_iff hs0).mpr
        linear_combination -he
      _ = _ := by
        rw [ih, Nat.factorial_succ, Nat.cast_mul, pow_succ s (j+1)]
        field_simp [hs0] <;> ring

/-- The complex Laplace transform of the ordinary real Laguerre polynomial. -/
theorem laguerreValue_complex_laplace (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ici 0, (laguerreValue k x : ℂ) * Complex.exp (-s * (x : ℂ))) =
      (s - 1)^k / s^(k+1) := by
  have hs0 : s ≠ 0 := fun h => by simpa [h] using hs
  rw [integral_Ici_eq_integral_Ioi]
  calc
    _ = ∫ x : ℝ in Ioi 0, ∑ j ∈ Finset.range (k+1),
          (laguerreCoefficient k j : ℂ) * laplaceMonomial s j x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp [laguerreValue, laplaceMonomial, Finset.sum_mul, mul_assoc]
    _ = ∑ j ∈ Finset.range (k+1), (laguerreCoefficient k j : ℂ) *
          ((j.factorial : ℂ) / s^(j+1)) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul, laplaceMonomial_integral hs]
      · intro j hj
        exact (laplaceMonomial_integrable hs j).const_mul _
    _ = s⁻¹ * ∑ j ∈ Finset.range (k+1),
          (-s⁻¹)^j * (1 : ℂ)^(k-j) * (k.choose j : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hfac : (j.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      rw [laguerreCoefficient, neg_eq_neg_one_mul (s⁻¹), mul_pow, inv_pow, pow_succ]
      push_cast
      field_simp [hs0, hfac]
      <;> ring
    _ = s⁻¹ * (-s⁻¹ + 1)^k := by rw [add_pow]
    _ = _ := by
      have he : -s⁻¹ + 1 = (s-1) / s := by field_simp [hs0]; ring
      rw [he, div_pow, pow_succ]
      field_simp [hs0] <;> ring

end RiemannResearch.Analysis
