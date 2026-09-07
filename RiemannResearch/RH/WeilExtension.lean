import RiemannResearch.RH.SignedWeilCorrelation
import RiemannResearch.Analysis.SuperexponentialDecay
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Removing the arithmetic cutoff in the signed Weil expression

Source: the user-provided Nyman--Weil note, section 2. The arithmetic
normalization is that of Suzuki, *Weil's quadratic form via the screw function*,
section 1.1, https://arxiv.org/html/2606.09096v1.

This module establishes absolute convergence of the actual von Mangoldt
series from concrete exponential decay, and convergence of the finite
arithmetic form to its full arithmetic expression. It does not assert the
unavailable compact-test explicit formula identifying this expression with
the sum over zeros of `riemannZeta`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

/-- A deliberately coarse majorant used only to justify absolute convergence.
The actual weight in all identities remains `vonMangoldt n / sqrt n`. -/
theorem primePowerWeight_le_nat (n : ℕ) : primePowerWeight n ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [primePowerWeight]
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnp.le
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hv : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := by
    have := @ArithmeticFunction.vonMangoldt_le_log n
    have := Real.log_le_sub_one_of_pos hnp
    linarith
  unfold primePowerWeight
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnp)).2
  nlinarith

theorem exp_neg_three_log {x : ℝ} (hx : 0 < x) :
    Real.exp (-3 * Real.log x) = 1 / x ^ 3 := by
  rw [show -3 * Real.log x = -(Real.log x + Real.log x + Real.log x) by ring,
    Real.exp_neg]
  simp [Real.exp_add, Real.exp_log hx, pow_succ]

/-- Quantitative convergence majorant for the actual complex arithmetic terms. -/
theorem norm_primePowerTerm_le_inv_sq (C : ℝ → ℂ) (A : ℝ)
    (hC : ∀ t, 0 ≤ t → ‖C t‖ ≤ A * Real.exp (-3 * t)) (n : ℕ) :
    ‖(primePowerWeight n : ℂ) * C (Real.log n)‖ ≤ A / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [primePowerWeight]
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    ‖(primePowerWeight n : ℂ) * C (Real.log n)‖ =
        primePowerWeight n * ‖C (Real.log n)‖ := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (primePowerWeight_nonneg n)]
    _ ≤ (n : ℝ) * (A * Real.exp (-3 * Real.log n)) :=
      mul_le_mul (primePowerWeight_le_nat n)
        (hC _ (Real.log_natCast_nonneg n)) (norm_nonneg _) hnp.le
    _ = A / (n : ℝ) ^ 2 := by
      rw [exp_neg_three_log hnp]
      field_simp [ne_of_gt hnp]
      <;> ring

/-- Absolute convergence includes every prime power and needs no RH input. -/
theorem summable_norm_primePowerTerm_of_exp_decay (C : ℝ → ℂ) (A : ℝ)
    (hC : ∀ t, 0 ≤ t → ‖C t‖ ≤ A * Real.exp (-3 * t)) :
    Summable (fun n : ℕ => ‖(primePowerWeight n : ℂ) * C (Real.log n)‖) := by
  have hs : Summable (fun n : ℕ => A / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left A
  exact hs.of_norm_bounded (fun n => by
    simpa only [norm_norm] using norm_primePowerTerm_le_inv_sq C A hC n)

theorem summable_primePowerTerm_of_exp_decay (C : ℝ → ℂ) (A : ℝ)
    (hC : ∀ t, 0 ≤ t → ‖C t‖ ≤ A * Real.exp (-3 * t)) :
    Summable (fun n : ℕ => (primePowerWeight n : ℂ) * C (Real.log n)) :=
  (summable_norm_primePowerTerm_of_exp_decay C A hC).of_norm

/-- Real specialization for the existing signed arithmetic correlation form. -/
theorem summable_real_primePowerTerm_of_exp_decay (C : ℝ → ℝ) (A : ℝ)
    (hC : ∀ t, 0 ≤ t → |C t| ≤ A * Real.exp (-3 * t)) :
    Summable (fun n : ℕ => primePowerWeight n * C (Real.log n)) := by
  have hs := summable_primePowerTerm_of_exp_decay (fun t => (C t : ℂ)) A
    (fun t ht => by simpa using hC t ht)
  obtain ⟨a, ha⟩ := hs
  refine ⟨a.re, ?_⟩
  have hm := ha.map Complex.reAddGroupHom Complex.continuous_re
  change HasSum (fun n => ((primePowerWeight n : ℂ) * (C (Real.log n) : ℂ)).re) a.re at hm
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hm

/-- The actual cross-correlation series is absolutely convergent on continuous
superexponential test functions. Its correlation bound is supplied above by
ordinary Lebesgue integration, rather than retained as a hypothesis. -/
theorem summable_norm_crossCorrelation_primePowerTerm {f g : ℝ → ℂ}
    (hf : RiemannResearch.Analysis.SuperexponentialDecay f)
    (hg : RiemannResearch.Analysis.SuperexponentialDecay g)
    (hfc : Continuous f) (hgc : Continuous g) :
    Summable (fun n : ℕ => ‖(primePowerWeight n : ℂ) *
      RiemannResearch.Analysis.crossCorrelation f g (Real.log n)‖) := by
  obtain ⟨A, _, hA⟩ := hf.crossCorrelation hg hfc hgc 3 (by norm_num)
  apply summable_norm_primePowerTerm_of_exp_decay _ A
  intro t ht
  simpa only [abs_of_nonneg ht] using hA t

/-- Absolute convergence for the actual real autocorrelation in the existing
signed arithmetic form, with its decay deduced from the test function. -/
theorem summable_realAutocorrelation_primePowerTerm {f : ℝ → ℂ}
    (hf : RiemannResearch.Analysis.SuperexponentialDecay f) (hfc : Continuous f) :
    Summable (fun n : ℕ => primePowerWeight n * realAutocorrelation f (Real.log n)) := by
  have hs := (summable_norm_crossCorrelation_primePowerTerm hf hf hfc hfc).of_norm
  obtain ⟨a, ha⟩ := hs
  refine ⟨a.re, ?_⟩
  have hm := ha.map Complex.reAddGroupHom Complex.continuous_re
  change HasSum (fun n => ((primePowerWeight n : ℂ) *
    RiemannResearch.Analysis.crossCorrelation f f (Real.log n)).re) a.re at hm
  have hc (t : ℝ) : RiemannResearch.Analysis.crossCorrelation f f t =
      RiemannResearch.Analysis.SquarePartitionLocalization.autocorrelation f t := by rfl
  simpa only [hc, realAutocorrelation,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hm

/-- The infinite arithmetic expression: the polar, gamma, and diagonal terms
are unchanged and the complete signed von Mangoldt series replaces the cutoff. -/
def infinitePrimePowerCorrelationValue (c : ℝ) (C : ℝ → ℝ) : ℝ :=
  2 * (∫ t, weilPoleKernel t * C t ∂positiveMeasure) -
    2 * (∑' n : ℕ, primePowerWeight n * C (Real.log n)) - c * C 0 -
    2 * (∫ t, weilGammaKernel t * (C t - weilRegulator t * C 0)
      ∂positiveMeasure)

/-- The finite arithmetic expressions converge to the actual full arithmetic
expression. Absolute convergence is discharged by the concrete decay estimate. -/
theorem primePowerCorrelationValue_tendsto (c : ℝ) (C : ℝ → ℝ) (A : ℝ)
    (hC : ∀ t, 0 ≤ t → |C t| ≤ A * Real.exp (-3 * t)) :
    Tendsto (fun N => primePowerCorrelationValue N c C) atTop
      (𝓝 (infinitePrimePowerCorrelationValue c C)) := by
  have hs := (summable_real_primePowerTerm_of_exp_decay C A hC).hasSum.tendsto_sum_nat
  unfold primePowerCorrelationValue correlationValue infinitePrimePowerCorrelationValue
  exact (((tendsto_const_nhds.sub (tendsto_const_nhds.mul hs)).sub
    tendsto_const_nhds).sub tendsto_const_nhds)

end
end RiemannResearch.RH.SignedWeilCorrelation
