/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The finite shifted Möbius test at its boundary

The finite divisor rearrangement is the shifted-test construction in the
Mertens displacement manuscript. The completion at one uses Mathlib's
entire function `riemannZeta₁`. The parameter may approach zero in ℂ.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
open ArithmeticFunction

namespace RiemannResearch.NumberTheory.MertensShiftedTest

/-- The Dirichlet coefficient of ζ(z)/ζ(z+s). -/
def shiftedCoeff (m : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ m.divisors, (ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ (-s)

/-- The pole-subtracted partial sum at a physical site. -/
def shiftedTest (n : ℕ) (s : ℂ) : ℂ :=
  (∑ m ∈ Finset.Icc 1 n, shiftedCoeff m s) -
    (n : ℂ) * (s / riemannZeta₁ (1 + s))

/-- Away from zero the scalar correction is the reciprocal zeta value. -/
theorem correction_eq_inv_zeta {s : ℂ} (hs : s ≠ 0) :
    s / riemannZeta₁ (1+s) = (riemannZeta (1+s))⁻¹ := by
  have h : 1 + s ≠ 1 := by simpa using hs
  rw [riemannZeta_eq_inv_sub_mul h, mul_inv_rev, inv_inv]
  rw [show (1+s)-1 = s by ring, div_eq_mul_inv, mul_comm]

@[simp] theorem shiftedCoeff_zero (m : ℕ) :
    shiftedCoeff m 0 = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f m)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [shiftedCoeff, neg_zero, Complex.cpow_zero, mul_one,
    ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

@[simp] theorem shiftedTest_zero (n : ℕ) (hn : 1 ≤ n) : shiftedTest n 0 = 1 := by
  simp [shiftedTest, hn]

/-- Each individual coefficient is entire. A divisor in the finite sum
is positive, so the positive base of the complex power never vanishes. -/
theorem differentiable_shiftedCoeff (m : ℕ) : Differentiable ℂ (shiftedCoeff m) := by
  unfold shiftedCoeff
  apply Differentiable.fun_sum
  intro k hk
  have hk0 : (k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
  apply Differentiable.mul (differentiable_const _)
  exact (differentiable_id.neg.const_cpow (.inl hk0))

/-- The tests are holomorphic at every parameter where the completed
zeta denominator is nonzero. In particular this includes the origin. -/
theorem differentiableAt_shiftedTest (n : ℕ) (s : ℂ)
    (hs : riemannZeta₁ (1+s) ≠ 0) : DifferentiableAt ℂ (shiftedTest n) s := by
  unfold shiftedTest
  apply DifferentiableAt.sub
  · exact DifferentiableAt.fun_sum fun m _ => (differentiable_shiftedCoeff m).differentiableAt
  · have harg : DifferentiableAt ℂ (fun w : ℂ => 1 + w) s := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ => riemannZeta₁ (1+w)) s :=
      differentiable_riemannZeta₁.differentiableAt.comp s harg
    exact (differentiableAt_const _).mul (differentiableAt_id.div hden hs)

/-- The sum is holomorphic in the entire open right half-plane. -/
theorem differentiableOn_shiftedTest (n : ℕ) :
    DifferentiableOn ℂ (shiftedTest n) {s : ℂ | 0 < s.re} := by
  intro s hs
  apply (differentiableAt_shiftedTest n s _).differentiableWithinAt
  have hRe : 1 < (1+s).re := by simpa using hs
  have hne : 1+s ≠ 1 := by
    intro he
    rw [he] at hRe
    simp at hRe
  intro hz
  apply (riemannZeta_ne_zero_of_one_lt_re hRe)
  rw [riemannZeta_eq_inv_sub_mul hne, hz, mul_zero]

/-- The undamped endpoint equals one along every complex approach to zero. -/
theorem tendsto_shiftedTest_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (shiftedTest n) (𝓝 0) (𝓝 1) := by
  have h := (differentiableAt_shiftedTest n 0 (by simp)).continuousAt.tendsto
  simpa only [shiftedTest_zero n hn] using h

end RiemannResearch.NumberTheory.MertensShiftedTest
