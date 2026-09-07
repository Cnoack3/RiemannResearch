import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The exact quarter-point Complex.digamma constant

This is obtained by differentiating Mathlib's actual gamma reflection and
duplication identities at 1/4. No gamma value or logarithmic-derivative
identity is assumed. The final real identity supplies the diagonal constant
in the spatial Weil archimedean normalization.
-/

open Complex

namespace RiemannResearch.RH

noncomputable section

private theorem gamma_differentiable_at_positive {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma z
  intro n hn
  rw [hn] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz

private theorem quarter_logDeriv_reflect :
    Complex.digamma (1 / 4) - Complex.digamma (3 / 4) = -(Real.pi : ℂ) := by
  have hq : DifferentiableAt ℂ Complex.Gamma (1 / 4) :=
    gamma_differentiable_at_positive (by norm_num)
  have ht : DifferentiableAt ℂ Complex.Gamma (3 / 4) :=
    gamma_differentiable_at_positive (by norm_num)
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) (1 / 4) := by
    convert (hasDerivAt_id (1 / 4 : ℂ)).const_sub 1 using 1 <;> first | rfl | norm_num
  have hrefld : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (1 - z)) (1 / 4) := by
    apply DifferentiableAt.comp (g := Complex.Gamma) _ _ hlin.differentiableAt
    convert ht using 1 <;> first | rfl | norm_num
  have hrefllog : logDeriv (fun z : ℂ => Complex.Gamma (1 - z)) (1 / 4) =
      -Complex.digamma (3 / 4) := by
    have h := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => 1 - z)
      (x := 1 / 4) (by convert ht using 1 <;> first | rfl | norm_num) hlin.differentiableAt
    rw [hlin.deriv] at h
    simpa only [Function.comp_def, show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num,
      mul_neg, mul_one, ← Complex.digamma_def] using h
  have hleft : logDeriv (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) (1 / 4) =
      Complex.digamma (1 / 4) - Complex.digamma (3 / 4) := by
    rw [logDeriv_mul (f := Complex.Gamma) (g := fun z : ℂ => Complex.Gamma (1 - z)) (1 / 4)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num : 0 < (1 / 4 : ℂ).re))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num : 0 < ((1 : ℂ) - 1 / 4).re))
      hq hrefld, hrefllog]
    rfl
  have harg : (Real.pi : ℂ) * (1 / 4) = ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 / 4)) ≠ 0 := by
    rw [harg, ← Complex.ofReal_sin, Real.sin_pi_div_four]
    exact_mod_cast (show Real.sqrt 2 / 2 ≠ 0 by positivity)
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 / 4)) =
      Complex.sin ((Real.pi : ℂ) * (1 / 4)) := by
    rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsd : HasDerivAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z))
      (Complex.cos ((Real.pi : ℂ) * (1 / 4)) * (Real.pi : ℂ)) (1 / 4) := by
    convert ((hasDerivAt_id (1 / 4 : ℂ)).const_mul (Real.pi : ℂ)).csin using 1
    <;> first | rfl | simp only [id_eq, mul_one]
  have hslog : logDeriv (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) (1 / 4) =
      (Real.pi : ℂ) := by
    rw [logDeriv_apply, hsd.deriv, hcos]
    rw [mul_comm (Complex.sin ((Real.pi : ℂ) * (1 / 4))) (Real.pi : ℂ),
      mul_div_assoc, div_self hsin, mul_one]
  have hright : logDeriv (fun z : ℂ => (Real.pi : ℂ) /
      Complex.sin ((Real.pi : ℂ) * z)) (1 / 4) = -(Real.pi : ℂ) := by
    rw [logDeriv_div (f := fun _ : ℂ => (Real.pi : ℂ))
      (g := fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) (1 / 4)
      (by exact_mod_cast Real.pi_ne_zero) hsin
      (differentiableAt_const (Real.pi : ℂ)) hsd.differentiableAt, hslog, logDeriv_const]
    simp
  have heq : (fun z : ℂ => Complex.Gamma z * Complex.Gamma (1 - z)) =
      (fun z : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z)) :=
    funext Complex.Gamma_mul_Gamma_one_sub
  rw [← hleft, heq, hright]

private theorem quarter_logDeriv_duplicate :
    Complex.digamma (1 / 4) + Complex.digamma (3 / 4) =
      2 * Complex.digamma (1 / 2) - 2 * Complex.log 2 := by
  have hq : DifferentiableAt ℂ Complex.Gamma (1 / 4) :=
    gamma_differentiable_at_positive (by norm_num)
  have ht : DifferentiableAt ℂ Complex.Gamma (3 / 4) :=
    gamma_differentiable_at_positive (by norm_num)
  have hh : DifferentiableAt ℂ Complex.Gamma (1 / 2) :=
    gamma_differentiable_at_positive (by norm_num)
  have hadd : HasDerivAt (fun z : ℂ => z + 1 / 2) 1 (1 / 4) := by
    convert (hasDerivAt_id (1 / 4 : ℂ)).add_const (1 / 2) using 1 <;> first | rfl | norm_num
  have hmul : HasDerivAt (fun z : ℂ => 2 * z) 2 (1 / 4) := by
    convert (hasDerivAt_id (1 / 4 : ℂ)).const_mul 2 using 1 <;> first | rfl | norm_num
  have htransd : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1 / 2)) (1 / 4) := by
    apply DifferentiableAt.comp (g := Complex.Gamma) _ _ hadd.differentiableAt
    convert ht using 1 <;> first | rfl | norm_num
  have hdouble : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (2 * z)) (1 / 4) := by
    apply DifferentiableAt.comp (g := Complex.Gamma) _ _ hmul.differentiableAt
    convert hh using 1 <;> first | rfl | norm_num
  have htranslog : logDeriv (fun z : ℂ => Complex.Gamma (z + 1 / 2)) (1 / 4) =
      Complex.digamma (3 / 4) := by
    have h := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z + 1 / 2)
      (x := 1 / 4) (by convert ht using 1 <;> first | rfl | norm_num) hadd.differentiableAt
    rw [hadd.deriv] at h
    simpa only [Function.comp_def, show (1 / 4 : ℂ) + 1 / 2 = 3 / 4 by norm_num,
      mul_one, ← Complex.digamma_def] using h
  have hdoublelog : logDeriv (fun z : ℂ => Complex.Gamma (2 * z)) (1 / 4) =
      2 * Complex.digamma (1 / 2) := by
    have h := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => 2 * z)
      (x := 1 / 4) (by convert hh using 1 <;> first | rfl | norm_num) hmul.differentiableAt
    rw [hmul.deriv] at h
    simpa only [Function.comp_def, show (2 : ℂ) * (1 / 4) = 1 / 2 by norm_num,
      ← Complex.digamma_def, mul_comm _ (2 : ℂ)] using h
  have hexpd := ((hmul.const_sub 1).const_mul (Complex.log 2)).cexp
  have hexplog : logDeriv (fun z : ℂ =>
      Complex.exp (Complex.log 2 * (1 - 2 * z))) (1 / 4) = -2 * Complex.log 2 := by
    rw [logDeriv_apply, hexpd.deriv]
    field_simp [Complex.exp_ne_zero]
    <;> ring
  have hleft : logDeriv (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) (1 / 4) =
      Complex.digamma (1 / 4) + Complex.digamma (3 / 4) := by
    rw [logDeriv_mul (f := Complex.Gamma) (g := fun z : ℂ => Complex.Gamma (z + 1 / 2)) (1 / 4)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num : 0 < (1 / 4 : ℂ).re))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num : 0 < ((1 / 4 : ℂ) + 1 / 2).re))
      hq htransd, htranslog]
    rfl
  have hright : logDeriv (fun z : ℂ => Complex.Gamma (2 * z) *
      Complex.exp (Complex.log 2 * (1 - 2 * z)) * (Real.sqrt Real.pi : ℂ)) (1 / 4) =
      2 * Complex.digamma (1 / 2) - 2 * Complex.log 2 := by
    rw [logDeriv_mul_const
      (f := fun z : ℂ => Complex.Gamma (2 * z) * Complex.exp (Complex.log 2 * (1 - 2 * z)))
      (1 / 4) _ (by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'),
      logDeriv_mul (f := fun z : ℂ => Complex.Gamma (2 * z))
        (g := fun z : ℂ => Complex.exp (Complex.log 2 * (1 - 2 * z))) (1 / 4)
        (Complex.Gamma_ne_zero_of_re_pos (by norm_num : 0 < ((2 : ℂ) * (1 / 4)).re))
        (Complex.exp_ne_zero _) hdouble hexpd.differentiableAt,
      hdoublelog, hexplog]
    ring
  have heq : (fun z : ℂ => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) =
      (fun z : ℂ => Complex.Gamma (2 * z) *
        Complex.exp (Complex.log 2 * (1 - 2 * z)) * (Real.sqrt Real.pi : ℂ)) := by
    funext z
    rw [Complex.Gamma_mul_Gamma_add_half,
      Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  rw [← hleft, heq, hright]

/-- The exact complex value at 1/4. -/
theorem digamma_one_quarter :
    Complex.digamma (1 / 4) = -(Real.eulerMascheroniConstant : ℂ) -
      3 * (Real.log 2 : ℂ) - (Real.pi : ℂ) / 2 := by
  have hs := quarter_logDeriv_duplicate
  have hd := quarter_logDeriv_reflect
  rw [Complex.digamma_one_half] at hs
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ 2 by norm_num)).symm
  rw [hlog] at hs
  linear_combination hs / 2 + hd / 2

theorem re_digamma_one_quarter :
    (Complex.digamma (1 / 4)).re = -Real.eulerMascheroniConstant -
      3 * Real.log 2 - Real.pi / 2 := by
  have hc : Complex.digamma (1 / 4) =
      ((-Real.eulerMascheroniConstant - 3 * Real.log 2 - Real.pi / 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_ofNat] using digamma_one_quarter
  simpa only [Complex.ofReal_re] using congrArg Complex.re hc

end
end RiemannResearch.RH
