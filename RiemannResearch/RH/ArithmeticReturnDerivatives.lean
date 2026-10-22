import RiemannResearch.RH.ArithmeticReturnSupport
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Differentiation of the actual locally finite arithmetic return

Source: user-provided argument, Theorem 4.1 of the Nyman--Weil note.

Every observation point has a neighborhood on which the return is an exact
finite sum of fixed translates. Differentiation therefore commutes with the
arithmetic return, without invoking a derivative/interchange theorem for an
infinite series. The same argument applies to every iterated derivative.
-/

open scoped BigOperators Topology

namespace RiemannResearch.RH

/-- A derivative inherits a lower support bound by local equality with zero. -/
theorem deriv_zero_below_of_zero_below {u : ℝ → ℂ} {a : ℝ}
    (ha : ∀ x < a, u x = 0) : ∀ x < a, deriv u x = 0 := by
  intro x hx
  have heq : u =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [Iio_mem_nhds hx] with t ht
    exact ha t ht
  simpa using heq.deriv_eq

/-- The same lower support bound holds for every actual iterated derivative. -/
theorem iteratedDeriv_zero_below_of_zero_below {u : ℝ → ℂ} {a : ℝ}
    (ha : ∀ x < a, u x = 0) (j : ℕ) :
    ∀ x < a, iteratedDeriv j u x = 0 := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using ha
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact deriv_zero_below_of_zero_below ih

/-- Derivatives also preserve an upper support bound. -/
theorem deriv_zero_above_of_zero_above {u : ℝ → ℂ} {b : ℝ}
    (hb : ∀ x > b, u x = 0) : ∀ x > b, deriv u x = 0 := by
  intro x hx
  have heq : u =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact hb t ht
  simpa using heq.deriv_eq

theorem iteratedDeriv_zero_above_of_zero_above {u : ℝ → ℂ} {b : ℝ}
    (hb : ∀ x > b, u x = 0) (j : ℕ) :
    ∀ x > b, iteratedDeriv j u x = 0 := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hb
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact deriv_zero_above_of_zero_above ih

/-- The derivative of the actual return is the return of the derivative. -/
theorem hasDerivAt_arithmeticReturn (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} (hu : Differentiable ℝ u)
    (ha : ∀ x < a, u x = 0) (y : ℝ) :
    HasDerivAt (arithmeticReturn c u) (arithmeticReturn c (deriv u) y) y := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (y + 1 - a))
  have hN' : Real.exp (y + 1 - a) < (N + 1 : ℕ) :=
    lt_trans hN (by exact_mod_cast Nat.lt_succ_self N)
  let F : ℝ → ℂ := fun x => ∑ k ∈ Finset.range (N + 1),
    (c k / Real.sqrt k : ℝ) • u (x - Real.log k)
  have hF : HasDerivAt F
      (∑ k ∈ Finset.range (N + 1),
        (c k / Real.sqrt k : ℝ) • deriv u (y - Real.log k)) y := by
    apply HasDerivAt.fun_sum
    intro k hk
    have hshift : HasDerivAt (fun x : ℝ => u (x - Real.log k))
        (deriv u (y - Real.log k)) y := by
      have hc := (hu (y - Real.log k)).hasDerivAt.scomp y
        ((hasDerivAt_id y).sub_const (Real.log k))
      convert hc using 1 <;> first
        | rfl
        | simp only [Function.comp_apply, id_eq, one_smul]
    exact hshift.fun_const_smul (c k / Real.sqrt k : ℝ)
  rw [arithmeticReturn_eq_sum c (deriv_zero_below_of_zero_below ha)
    (by linarith : y ≤ y + 1) hN']
  apply hF.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (by linarith : y < y + 1)] with x hx
  exact arithmeticReturn_eq_sum c ha (le_of_lt hx) hN'

theorem arithmeticReturn_deriv (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} (hu : Differentiable ℝ u)
    (ha : ∀ x < a, u x = 0) :
    deriv (arithmeticReturn c u) = arithmeticReturn c (deriv u) := by
  funext y
  exact (hasDerivAt_arithmeticReturn c hu ha y).deriv

/-- The full all-orders commutation theorem for a smooth arithmetic return. -/
theorem arithmeticReturn_iteratedDeriv (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (j : ℕ) :
    iteratedDeriv j (arithmeticReturn c u) = arithmeticReturn c (iteratedDeriv j u) := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      exact arithmeticReturn_deriv c
        (ContDiff.differentiable_iteratedDeriv j hu
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j))
        (iteratedDeriv_zero_below_of_zero_below ha j)

/-- Specialization to the actual Nyman conductor coefficients. -/
theorem nymanFullReturn_iteratedDeriv (n : ℕ)
    {u : ℝ → ℂ} {a : ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (j : ℕ) :
    iteratedDeriv j (nymanFullReturn n u) = nymanFullReturn n (iteratedDeriv j u) :=
  arithmeticReturn_iteratedDeriv (nymanConductorBeta n) hu ha j

end RiemannResearch.RH
