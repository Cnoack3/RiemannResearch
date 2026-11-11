/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialResolvent

/-!
# Unconditional approximation of the canonical Schur upper endpoints

Source: the squarefree CRT displacement agenda, 9 November 2026, and
the 10 November request for cofinal upper-endpoint smallness.
The iterates are specified using finite Q projections and the reciprocal
multiplier. No assumed solve-residual estimate occurs in the interval
theorem. Its shrinking width is unconditional; smallness of the actual
Schur energies is explicitly separate.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialSchurEndpoints
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoClosedProjectionComparison
open QSquarefreePrimorialCofinality QPrimorialMatchedDisplacement
open QPrimorialPrimeCarry QPrimorialResolvent QSquarefreeDisplacementRigidity

def trial (n k : ℕ) : QHilbert := (primeStage n).starProjection (approx n k)

theorem trial_mem (n k : ℕ) : trial n k ∈ primeStage n :=
  (primeStage n).starProjection_apply_mem _

theorem trial_error_sq (n k : ℕ) :
    ‖primeComponent n - trial n k‖ ^ 2 ≤
      (966289 / 8136000 : ℝ) * primorialError n * (1 / 289 : ℝ)^k := by
  have hn : ‖primeComponent n - trial n k‖ ≤ ‖stageDisplacement n - approx n k‖ := by
    rw [primeComponent, trial, ← map_sub]
    exact projection_norm_le _ _
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn).trans (approx_error_sq n k)

/-- Complete Q arithmetic budget, not a truncated physical tail. -/
def budget (n k : ℕ) : ℝ :=
  (966289 / 8136000 : ℝ) * zetaTwo * primorialError n * (1 / 289 : ℝ)^k

def lower (n k : ℕ) : ℝ := trialEnergy n (trial n k)

def upper (n k : ℕ) : ℝ := lower n k + budget n k

theorem budget_nonneg (n k : ℕ) : 0 ≤ budget n k := by
  have hz := zetaTwo_pos
  unfold budget primorialError
  positivity

/-- Certified endpoints with no hypothetical solve accuracy. -/
theorem certified_interval (n k : ℕ) :
    lower n k ≤ selfForcing n ∧ selfForcing n ≤ upper n k := by
  have hv := schurVariational_exact n (trial_mem n k)
  have h0 : 0 ≤ schurForm n (primeComponent n - trial n k) (primeComponent n - trial n k) := by
    rw [schurForm, real_inner_self_eq_norm_sq]
    positivity
  have hb := (schurForm_upper n (primeComponent n - trial n k)).trans
    (mul_le_mul_of_nonneg_left (trial_error_sq n k) zetaTwo_pos.le)
  change selfForcing n = lower n k + _ at hv
  unfold upper budget
  constructor <;> nlinarith only [hv, h0, hb]

theorem upper_nonneg (n k : ℕ) : 0 ≤ upper n k := by
  have hf : 0 ≤ selfForcing n := by rw [selfForcing_exact]; positivity
  exact hf.trans (certified_interval n k).2

theorem upper_excess (n k : ℕ) :
    0 ≤ upper n k - selfForcing n ∧
      upper n k - selfForcing n ≤ budget n k := by
  have h := certified_interval n k
  unfold upper at *
  constructor <;> linarith [h.1, h.2]

theorem budget_uniform (n k : ℕ) :
    budget n k ≤ (966289 / 8136000 : ℝ) * zetaTwo * (1 / 289 : ℝ)^k := by
  have hz := zetaTwo_pos
  have h := mul_le_mul_of_nonneg_left (primorialError_le_one n)
    (show 0 ≤ (966289 / 8136000 : ℝ) * zetaTwo * (1 / 289 : ℝ)^k by positivity)
  unfold budget
  nlinarith only [h]

/-- The endpoint error vanishes uniformly over every choice of primorial stages,
including bounded or oscillating stage sequences. -/
theorem upper_excess_tendsto (N k : ℕ → ℕ) (hk : Tendsto k atTop atTop) :
    Tendsto (fun j => upper (N j) (k j) - selfForcing (N j)) atTop (𝓝 0) := by
  have hp : Tendsto (fun j : ℕ => (1 / 289 : ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht := (hp.comp hk).const_mul ((966289 / 8136000 : ℝ) * zetaTwo)
  simp only [mul_zero] at ht
  exact squeeze_zero (fun j => (upper_excess (N j) (k j)).1)
    (fun j => ((upper_excess (N j) (k j)).2).trans (budget_uniform (N j) (k j))) ht

/-- A common solve depth makes every endpoint excess small, over all stages. -/
theorem upper_excess_uniform_smallness (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n k : ℕ, K ≤ k →
      0 ≤ upper n k - selfForcing n ∧ upper n k - selfForcing n < ε := by
  have hp : Tendsto (fun k : ℕ => (1 / 289 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht := hp.const_mul ((966289 / 8136000 : ℝ) * zetaTwo)
  simp only [mul_zero] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hε))
  refine ⟨K, fun n k hk => ⟨(upper_excess n k).1, ?_⟩⟩
  exact (((upper_excess n k).2).trans (budget_uniform n k)).trans_lt (hK k hk)

/-- A specified diagonal replaces the arbitrary trial/accuracy providers.
Its convergence to zero still requires the actual displacement to vanish. -/
theorem diagonal_upper_tendsto_zero_iff :
    Tendsto (fun n => upper n n) atTop (𝓝 0) ↔ displacement = 0 := by
  have hg := upper_excess_tendsto id id tendsto_id
  constructor
  · intro hu
    apply selfForcing_tendsto_zero_iff.mp
    have h := hu.sub hg
    simpa only [Function.id_def, sub_sub_cancel, sub_zero] using h
  · intro hd
    have h := (selfForcing_tendsto_zero_iff.mpr hd).add hg
    simpa only [Function.id_def, ← add_sub_assoc, add_sub_cancel_left, add_zero] using h

theorem displacement_zero_of_cofinal_upper (k : ℕ → ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, upper n (k n) ≤ ε) :
    displacement = 0 := by
  apply displacement_zero_of_cofinal_selfForcing
  intro ε hε
  exact (h ε hε).mono fun n hn => (certified_interval n (k n)).2.trans hn

/-- No growth assumption on the solve depth is needed for the sufficient direction. -/
theorem riemannHypothesis_of_cofinal_upper (k : ℕ → ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, upper n (k n) ≤ ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_selfForcing
  intro ε hε
  exact (h ε hε).mono fun n hn => (certified_interval n (k n)).2.trans hn

/-- A second certificate uses only the observed change between two iterates. -/
def posteriorUpper (n k : ℕ) : ℝ :=
  lower n (k + 1) + (zetaTwo / 256) * ‖approx n (k + 1) - approx n k‖ ^ 2

theorem posteriorUpper_certified (n k : ℕ) : selfForcing n ≤ posteriorUpper n k := by
  have hn : ‖primeComponent n - trial n (k + 1)‖ ≤
      ‖stageDisplacement n - approx n (k + 1)‖ := by
    rw [primeComponent, trial, ← map_sub]
    exact projection_norm_le _ _
  have hs := ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn).trans
    (approx_successor_error_sq n k)
  have hb := (schurForm_upper n (primeComponent n - trial n (k + 1))).trans
    (mul_le_mul_of_nonneg_left hs zetaTwo_pos.le)
  have hv := schurVariational_exact n (trial_mem n (k + 1))
  unfold posteriorUpper lower
  nlinarith only [hv, hb]

/-- Both independent complete-error certificates can be used together. -/
theorem min_upper_certified (n k : ℕ) :
    selfForcing n ≤ min (upper n (k + 1)) (posteriorUpper n k) :=
  le_min (certified_interval n (k + 1)).2 (posteriorUpper_certified n k)

/-- Explicit dual solve accuracy for the original residual-based certificate. -/
def solveError (n k : ℕ) : ℝ :=
  Real.sqrt ((966289 / 8136000 : ℝ) * primorialError n * (1 / 289 : ℝ)^k)

theorem schurForm_abs_le (n : ℕ) (x y : QHilbert) :
    |schurForm n x y| ≤ zetaTwo * ‖x‖ * ‖y‖ := by
  have hb (f : QHilbert) :
      ‖ZetaTwoParetoTransfer.toPareto (schurLift n f)‖ ≤ Real.sqrt zetaTwo * ‖f‖ := by
    have hh := schurForm_upper n f
    rw [schurForm, real_inner_self_eq_norm_sq] at hh
    calc
      _ ≤ Real.sqrt (zetaTwo * ‖f‖^2) := Real.le_sqrt_of_sq_le hh
      _ = _ := by rw [Real.sqrt_mul zetaTwo_pos.le, Real.sqrt_sq (norm_nonneg _)]
  have hc := (abs_real_inner_le_norm
    (ZetaTwoParetoTransfer.toPareto (schurLift n x))
    (ZetaTwoParetoTransfer.toPareto (schurLift n y))).trans
      (mul_le_mul (hb x) (hb y) (norm_nonneg _) (by positivity))
  change |schurForm n x y| ≤ _ at hc
  have he : (Real.sqrt zetaTwo * ‖x‖) * (Real.sqrt zetaTwo * ‖y‖) =
      zetaTwo * ‖x‖ * ‖y‖ := by
    calc
      _ = (Real.sqrt zetaTwo)^2 * ‖x‖ * ‖y‖ := by ring
      _ = _ := by rw [Real.sq_sqrt zetaTwo_pos.le]
  exact hc.trans_eq he

/-- The complete dual residual hypothesis is supplied, for every test vector. -/
theorem automatic_schur_residual (n k : ℕ) {y : QHilbert} (hy : y ∈ primeStage n) :
    |forcingResidual n (trial n k) y| ≤ zetaTwo * solveError n k * ‖y‖ := by
  have he : forcingResidual n (trial n k) y =
      schurForm n (primeComponent n - trial n k) y := by
    rw [forcingResidual, ← schur_equation n hy]
    simp only [schurForm, toPareto_schurLift, toPareto_sub,
      map_sub, inner_sub_left]
  have hn : ‖primeComponent n - trial n k‖ ≤ solveError n k :=
    Real.le_sqrt_of_sq_le (trial_error_sq n k)
  rw [he]
  exact (schurForm_abs_le n _ y).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hn zetaTwo_pos.le) (norm_nonneg y))

theorem original_interval_automatic (n k : ℕ) :
    lower n k ≤ selfForcing n ∧
      selfForcing n ≤ lower n k + (59 / 30 : ℝ) * zetaTwo * (solveError n k)^2 := by
  apply selfForcing_interval n (trial_mem n k) (solveError n k) (Real.sqrt_nonneg _)
  intro y hy
  exact (le_abs_self _).trans (automatic_schur_residual n k hy)

/-- The new endpoint is no larger than the original dual-residual endpoint. -/
theorem upper_le_original_endpoint (n k : ℕ) :
    upper n k ≤ lower n k + (59 / 30 : ℝ) * zetaTwo * (solveError n k)^2 := by
  have hs : (solveError n k)^2 =
      (966289 / 8136000 : ℝ) * primorialError n * (1 / 289 : ℝ)^k :=
    Real.sq_sqrt (by unfold primorialError; positivity)
  have hb := budget_nonneg n k
  unfold upper budget at *
  rw [hs]
  nlinarith only [hb]

end RiemannResearch.RH.QPrimorialSchurEndpoints
