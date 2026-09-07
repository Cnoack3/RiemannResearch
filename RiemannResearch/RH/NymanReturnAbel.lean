import RiemannResearch.RH.NymanReturnKernel
import RiemannResearch.RH.ArithmeticReturnDerivatives
import RiemannResearch.Analysis.BilateralLaplaceDifferential
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual Abel representation of the arithmetic return

This proves the convolution with the concrete cumulative-beta kernel by
integrating its actual logarithmic jumps. Compact support makes the jump sum
finite on every relevant integration interval; half-line FTC evaluates each
jump. Neither an assumed convolution identity nor a transform uniqueness
hypothesis is used.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH

open MeasureTheory.BilateralLaplace

private noncomputable def abelDerivative (u : ℝ → ℂ) (y t : ℝ) : ℂ :=
  kernel (1 / 2) t * (deriv u (y - t) + (1 / 2 : ℂ) * u (y - t))

private theorem continuous_halfKernel : Continuous (kernel (1 / 2)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_kernel_spatial (1 / 2) t).continuousAt

private theorem halfKernel_eq (t : ℝ) :
    kernel (1 / 2) t = (Real.exp (-t / 2) : ℂ) := by
  rw [kernel, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem abelDerivative_zero_above {u : ℝ → ℂ} {a : ℝ}
    (ha : ∀ x < a, u x = 0) (y : ℝ) {t : ℝ} (ht : y - a < t) :
    abelDerivative u y t = 0 := by
  have hyt : y - t < a := by linarith
  simp [abelDerivative, ha _ hyt, deriv_zero_below_of_zero_below ha _ hyt]

private theorem integrable_abelDerivative {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ∀ x < a, u x = 0)
    (hb : ∀ x > b, u x = 0) (y : ℝ) : Integrable (abelDerivative u y) := by
  have hc : Continuous (abelDerivative u y) :=
    continuous_halfKernel.mul
      ((hu.continuous_deriv_one.comp (continuous_const.sub continuous_id)).add
        (continuous_const.mul (hu.continuous.comp (continuous_const.sub continuous_id))))
  apply hc.integrable_of_hasCompactSupport
  have hs : tsupport (abelDerivative u y) ⊆ Icc (y - b) (y - a) := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    constructor
    · by_contra h
      have hyt : b < y - t := by linarith
      exact ht (by simp [abelDerivative, hb _ hyt,
        deriv_zero_above_of_zero_above hb _ hyt])
    · by_contra h
      exact ht (abelDerivative_zero_above ha y (by linarith))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hs

/-- The integral attached to one arithmetic jump is evaluated by ordinary
half-line FTC, with both convergence hypotheses proved from compact support. -/
private theorem integral_abelDerivative_Ici {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ∀ x < a, u x = 0)
    (hb : ∀ x > b, u x = 0) (y q : ℝ) :
    (∫ t in Ici q, abelDerivative u y t) = kernel (1 / 2) q * u (y - q) := by
  have hd : ∀ t : ℝ,
      HasDerivAt (fun z : ℝ => -(kernel (1 / 2) z * u (y - z)))
        (abelDerivative u y t) t := by
    intro t
    have hs : HasDerivAt (fun z : ℝ => u (y - z)) (-deriv u (y - t)) t := by
      have h := ((hu.differentiable (by norm_num)) (y - t)).hasDerivAt.scomp t
        ((hasDerivAt_id t).const_sub y)
      simpa only [Function.comp_def, neg_smul, one_smul] using h
    have h := ((hasDerivAt_kernel_spatial (1 / 2) t).mul hs).neg
    convert h using 1 <;> first
      | rfl
      | dsimp [abelDerivative]; ring
  have ht : Tendsto (fun z : ℝ => -(kernel (1 / 2) z * u (y - z))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (y - a)] with t ht
    have hyt : y - t < a := by linarith
    simp [ha _ hyt]
  rw [integral_Ici_eq_integral_Ioi]
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hd t) (integrable_abelDerivative hu ha hb y).integrableOn ht

private theorem cumulativeBeta_eq_log_jumps (n N : ℕ) {T t : ℝ}
    (ht : t ≤ T) (hN : Real.exp T < (N + 1 : ℕ)) :
    nymanCumulativeBeta n (Real.exp t) =
      ∑ k ∈ Finset.range (N + 1), if Real.log k ≤ t then nymanConductorBeta n k else 0 := by
  have hf : ⌊Real.exp t⌋₊ ≤ N := by
    have hlt := (Nat.floor_lt (Real.exp_pos t).le).mpr
      ((Real.exp_le_exp.mpr ht).trans_lt hN)
    omega
  have hset : (Finset.range (N + 1)).filter (fun k => k ≤ ⌊Real.exp t⌋₊) =
      Finset.Icc 0 ⌊Real.exp t⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [nymanCumulativeBeta, ← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    simp only [Nat.le_floor_iff (Real.exp_pos t).le, ← Real.log_le_iff_le_exp hkpos]

private theorem kernel_mul_derivative_eq_finite_jumps (n N : ℕ)
    {u : ℝ → ℂ} {a : ℝ} (ha : ∀ x < a, u x = 0) (y : ℝ)
    (hN : Real.exp (y - a) < (N + 1 : ℕ)) (t : ℝ) :
    (nymanReturnKernel n t : ℂ) *
        (deriv u (y - t) + (1 / 2 : ℂ) * u (y - t)) =
      ∑ k ∈ Finset.range (N + 1),
        (nymanConductorBeta n k : ℂ) * (Ici (Real.log k)).indicator (abelDerivative u y) t := by
  by_cases ht : t ≤ y - a
  · rw [nymanReturnKernel, cumulativeBeta_eq_log_jumps n N ht hN]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkt : Real.log k ≤ t
    · simp only [if_pos hkt, Set.indicator_of_mem (show t ∈ Ici (Real.log k) from hkt),
        abelDerivative]
      rw [halfKernel_eq]
      push_cast
      ring
    · simp [hkt, mem_Ici]
  · have hzero : u (y - t) = 0 := ha _ (by linarith)
    have hd : deriv u (y - t) = 0 := deriv_zero_below_of_zero_below ha _ (by linarith)
    have hD := abelDerivative_zero_above ha y (by linarith : y - a < t)
    simp [hzero, hd, Set.indicator_apply, hD]

/-- Actual Abel convolution formula for the full Nyman arithmetic return.
The test is only required to be C¹ with explicit compact support bounds. -/
theorem nymanFullReturn_eq_kernel_convolution (n : ℕ)
    {u : ℝ → ℂ} {a b : ℝ} (hu : ContDiff ℝ 1 u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (y : ℝ) :
    nymanFullReturn n u y = ∫ t : ℝ, (nymanReturnKernel n t : ℂ) *
      (deriv u (y - t) + (1 / 2 : ℂ) * u (y - t)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (y - a))
  have hN' : Real.exp (y - a) < (N + 1 : ℕ) :=
    hN.trans (by exact_mod_cast Nat.lt_succ_self N)
  have heq :
      (fun t : ℝ => (nymanReturnKernel n t : ℂ) *
        (deriv u (y - t) + (1 / 2 : ℂ) * u (y - t))) =
      fun t : ℝ => ∑ k ∈ Finset.range (N + 1),
        (nymanConductorBeta n k : ℂ) * (Ici (Real.log k)).indicator (abelDerivative u y) t := by
    funext t
    exact kernel_mul_derivative_eq_finite_jumps n N ha y hN' t
  have hi := integrable_abelDerivative hu ha hb y
  rw [heq, integral_finsetSum _ (fun k _ =>
    (hi.indicator measurableSet_Ici).const_mul (nymanConductorBeta n k : ℂ))]
  simp_rw [integral_const_mul, integral_indicator measurableSet_Ici,
    integral_abelDerivative_Ici hu ha hb y]
  rw [nymanFullReturn, arithmeticReturn_eq_sum (nymanConductorBeta n) ha le_rfl hN']
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have he : Real.exp (-Real.log (k : ℝ) / 2) = (Real.sqrt k)⁻¹ := by
      rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hkpos]
    rw [halfKernel_eq, he]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv,
      Complex.ofReal_mul, div_eq_mul_inv]
    ring

/-- Exact real-profile specialization for scaled broad-window estimates. -/
theorem nymanFullReturn_ofReal_eq_kernel_convolution (n : ℕ)
    {u : ℝ → ℝ} {a b : ℝ} (hu : ContDiff ℝ 1 u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (y : ℝ) :
    nymanFullReturn n (fun x => (u x : ℂ)) y =
      ((∫ t : ℝ, nymanReturnKernel n t *
        (deriv u (y - t) + (1 / 2 : ℝ) * u (y - t))) : ℂ) := by
  have huc : ContDiff ℝ 1 (fun x => (u x : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have hd : ∀ x : ℝ, deriv (fun z => (u z : ℂ)) x =
      ((deriv (F := ℝ) u x : ℝ) : ℂ) := by
    intro x
    exact ((hu.differentiable (by norm_num) x).hasDerivAt.ofReal_comp).deriv
  rw [nymanFullReturn_eq_kernel_convolution n (a := a) (b := b) huc
    (fun x hx => by simp [ha x hx]) (fun x hx => by simp [hb x hx]) y]
  push_cast
  apply integral_congr_ae
  filter_upwards [] with t
  norm_num [hd]

end RiemannResearch.RH
