/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoLCMZeroCertificate
import RiemannResearch.RH.ParetoFiniteMellinHalfPlane
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannResearch.RH.MobiusQuantitativeRate
import RiemannResearch.NumberTheory.PrimeNumberTheorem.LogarithmicMobiusMean
import RiemannResearch.Analysis.AffineObservationProjection
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic upper-rate inputs for the Pareto LCM optimizer

Balazard and de Roton, *Sur un critère de Báez-Duarte pour l'hypothèse de
Riemann*, Propositions 1--3, split the classical error into a shifted
quotient and a truncation term. The checked inequality below implements
the split for the actual centered legal numerator.
https://arxiv.org/abs/0812.1689

Bettin, Conrey, and Farmer, *An optimal choice of Dirichlet polynomials
for the Nyman-Beurling criterion*, Theorem 1, supplies the published
conditional classical budget. The transfer here uses the already proved
Möbius means to remove the leading-constant loss from centering.
https://arxiv.org/abs/1211.5191

The analytic trial budgets remain explicit hypotheses. The optimizer
comparison, charge estimate, and horizontal factors are unconditional.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace RiemannResearch.RH.Pareto.BaezDuarte

private theorem square_add_le_weighted (u v η : ℝ) (hη : 0 < η) :
    (u + v) ^ 2 ≤ (1 + η) * u ^ 2 + (1 + η⁻¹) * v ^ 2 := by
  by_contra! hlt
  have hmul := mul_lt_mul_of_pos_left hlt hη
  have h : η * ((1 + η) * u ^ 2 + (1 + η⁻¹) * v ^ 2) -
      η * (u + v) ^ 2 = (η * u - v) ^ 2 := by
    field_simp
    ring
  linarith [sq_nonneg (η * u - v)]

/-- Variable-parameter centering allows leading constants to transfer
when the coefficient charge is negligible at the target scale. -/
theorem centeredError_le_weighted_naturalError (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (η : ℝ) (hη : 0 < η) :
    centeredError s a ≤ ENNReal.ofReal (1 + η) * naturalError s a +
      ENNReal.ofReal ((1 + η⁻¹) * (naturalCharge s a) ^ 2) := by
  have hp (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      ENNReal.ofReal ((1 - ∑ d ∈ s, a d *
        (Int.fract (1 / ((d : ℝ) * x)) - (1 / (d : ℝ)) * Int.fract (1 / x))) ^ 2) ≤
        ENNReal.ofReal (1 + η) * ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) +
          ENNReal.ofReal ((1 + η⁻¹) * (naturalCharge s a) ^ 2) := by
    rw [centered_sum_eq, chi_eq_one hx]
    let u := 1 - naturalSum s a x
    let v := naturalCharge s a * Int.fract (1 / x)
    have hv : v ^ 2 ≤ (naturalCharge s a) ^ 2 := by
      dsimp only [v]
      rw [mul_pow]
      calc
        _ ≤ (naturalCharge s a) ^ 2 * (1 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Int.fract_nonneg _) (Int.fract_lt_one _).le 2) (sq_nonneg _)
        _ = _ := by simp
    have h : (1 - (naturalSum s a x - v)) ^ 2 ≤
        (1 + η) * u ^ 2 + (1 + η⁻¹) * (naturalCharge s a) ^ 2 := by
      rw [show 1 - (naturalSum s a x - v) = u + v by dsimp only [u]; ring]
      exact (square_add_le_weighted u v η hη).trans
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hv
          (show 0 ≤ 1 + η⁻¹ by positivity)))
    exact (ENNReal.ofReal_le_ofReal h).trans_eq (by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)])
  calc
    _ ≤ ∫⁻ x : ℝ in Ioc 0 1,
        (ENNReal.ofReal (1 + η) * ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) +
          ENNReal.ofReal ((1 + η⁻¹) * (naturalCharge s a) ^ 2)) := by
      unfold centeredError
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hp x hx
    _ = ENNReal.ofReal (1 + η) * naturalHeadError s a +
        ENNReal.ofReal ((1 + η⁻¹) * (naturalCharge s a) ^ 2) := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp [naturalHeadError]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (naturalHeadError_le_naturalError s a hs)
      zero_le) (le_refl _)

/-- Real signed coefficients of the logarithmically smoothed Möbius trial.
The sign matches the natural fractional-part synthesis. -/
def bcfCoefficient (M d : ℕ) : ℝ :=
  -(ArithmeticFunction.moebius d : ℝ) * (1 - Real.log d / Real.log M)

open RiemannResearch.NumberTheory.PrimeNumberTheorem (logarithmicMobiusMean
  logarithmicMobiusMean_tendsto_neg_one)

theorem bcf_charge_eq (M : ℕ) :
    naturalCharge (Finset.Icc 1 M) (bcfCoefficient M) =
      -mobiusReciprocalSum M + logarithmicMobiusMean M / Real.log M := by
  unfold naturalCharge mobiusReciprocalSum logarithmicMobiusMean
  rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold bcfCoefficient
  ring

/-- The centering charge has negligible squared energy on the inverse-log scale,
using the already proved quantitative PNT and logarithmic Möbius mean. -/
theorem bcf_charge_sq_mul_log_tendsto_zero :
    Tendsto (fun M : ℕ =>
      (naturalCharge (Finset.Icc 1 M) (bcfCoefficient M)) ^ 2 * Real.log M) atTop (𝓝 0) := by
  have hinv : Tendsto (fun M : ℕ => (Real.log M)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun M : ℕ => (logarithmicMobiusMean M) ^ 2 / Real.log M) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (logarithmicMobiusMean_tendsto_neg_one.pow 2).mul hinv
  have hu := (mobiusReciprocalSum_sq_mul_log_tendsto_zero.const_mul 2).add (hb.const_mul 2)
  simp only [mul_zero, add_zero] at hu
  apply squeeze_zero' (Eventually.of_forall (fun M =>
    mul_nonneg (sq_nonneg _) (Real.log_natCast_nonneg M))) ?_ hu
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with M hM
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  let A := mobiusReciprocalSum M
  let B := logarithmicMobiusMean M
  let ℓ := Real.log (M : ℝ)
  rw [bcf_charge_eq]
  change (-A + B / ℓ) ^ 2 * ℓ ≤ 2 * (A ^ 2 * ℓ) + 2 * (B ^ 2 / ℓ)
  have h : (-A + B / ℓ) ^ 2 ≤ 2 * A ^ 2 + 2 * (B / ℓ) ^ 2 := by
    nlinarith [sq_nonneg (A + B / ℓ)]
  calc
    _ ≤ (2 * A ^ 2 + 2 * (B / ℓ) ^ 2) * ℓ := mul_le_mul_of_nonneg_right h hlog.le
    _ = _ := by field_simp [show ℓ ≠ 0 from hlog.ne']

end RiemannResearch.RH.Pareto.BaezDuarte

namespace RiemannResearch.RH.Pareto.ResidueMellin

open BaezDuarte (finiteResidueSum residueVector centeredError_eq_hilbert_norm_sq
  centeredError_le_weighted_naturalError naturalError naturalCharge bcfCoefficient
  bcf_charge_sq_mul_log_tendsto_zero)
open RiemannResearch.Analysis.SingleObservationProjection (affine_target_error_split)

/-- Exact positive-scale transfer of a classical upper budget with its centering cost. -/
theorem lcm_error_mul_log_le_of_natural_budget (M : ℕ) (hM : 1 < M)
    (s : Finset ℕ) (a : ℕ → ℝ) (hs : ∀ d ∈ s, d ∈ Finset.Icc 1 M)
    (η b : ℝ) (hη : 0 < η) (hb : 0 ≤ b)
    (hbudget : naturalError s a ≤ ENNReal.ofReal (b / Real.log M)) :
    Real.log M * ‖hilbertOne - lcmBest M‖ ^ 2 ≤
      (1 + η) * b + (1 + η⁻¹) * ((naturalCharge s a) ^ 2 * Real.log M) := by
  have hspos : ∀ d ∈ s, 0 < d := fun d hd => (Finset.mem_Icc.mp (hs d hd)).1
  have hf : finiteResidueSum s a ∈ trialSpace (Nat.lcmUpto M) := by
    apply Submodule.sum_mem
    intro d hd
    rw [residueVector, dif_pos (hspos d hd)]
    exact Submodule.smul_mem _ _ (atom_mem_trial _ d (Nat.lcmUpto_pos M) (hspos d hd)
      (Finset.dvd_lcm (f := id) (hs d hd)))
  have he := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne
    (finiteResidueSum s a) hf
  change ‖hilbertOne - finiteResidueSum s a‖ ^ 2 =
    ‖hilbertOne - lcmBest M‖ ^ 2 + ‖finiteResidueSum s a - lcmBest M‖ ^ 2 at he
  have hopt : ‖hilbertOne - lcmBest M‖ ^ 2 ≤ ‖hilbertOne - finiteResidueSum s a‖ ^ 2 := by
    linarith [sq_nonneg ‖finiteResidueSum s a - lcmBest M‖]
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hh : ENNReal.ofReal (‖hilbertOne - lcmBest M‖ ^ 2) ≤
      ENNReal.ofReal ((1 + η) * (b / Real.log M) + (1 + η⁻¹) * (naturalCharge s a) ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (‖hilbertOne - finiteResidueSum s a‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hopt
      _ = BaezDuarte.centeredError s a := (centeredError_eq_hilbert_norm_sq s a hspos).symm
      _ ≤ ENNReal.ofReal (1 + η) * naturalError s a +
          ENNReal.ofReal ((1 + η⁻¹) * (naturalCharge s a) ^ 2) :=
        centeredError_le_weighted_naturalError s a hspos η hη
      _ ≤ ENNReal.ofReal (1 + η) * ENNReal.ofReal (b / Real.log M) +
          ENNReal.ofReal ((1 + η⁻¹) * (naturalCharge s a) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hbudget zero_le) (le_refl _)
      _ = _ := by
        rw [ENNReal.ofReal_add (show 0 ≤ (1 + η) * (b / Real.log M) by positivity)
          (show 0 ≤ (1 + η⁻¹) * (naturalCharge s a) ^ 2 by positivity),
          ENNReal.ofReal_mul (show 0 ≤ 1 + η by positivity)]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (by positivity)] at hr
  calc
    _ ≤ Real.log M *
        ((1 + η) * (b / Real.log M) + (1 + η⁻¹) * (naturalCharge s a) ^ 2) :=
      mul_le_mul_of_nonneg_left hr hlog.le
    _ = _ := by field_simp [hlog.ne']

/-- Conditional transfer of the BCF leading constant to the LCM optimum.
The analytic budget is the complete classical trial error, with the
charge correction provided unconditionally above. -/
theorem bcf_lcm_log_upper_of_natural_budget (K : ℝ) (hK : 0 ≤ K)
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 K)) (hB0 : ∀ᶠ M in atTop, 0 ≤ B M)
    (hbudget : ∀ᶠ M in atTop, naturalError (Finset.Icc 1 M) (bcfCoefficient M) ≤
      ENNReal.ofReal (B M / Real.log M)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, Real.log M * ‖hilbertOne - lcmBest M‖ ^ 2 ≤ K + ε := by
  let η := ε / (K + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hk : (1 + η) * K < K + ε := by
    have he : η * (K + 1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hlim := (hB.const_mul (1 + η)).add
    (bcf_charge_sq_mul_log_tendsto_zero.const_mul (1 + η⁻¹))
  rw [mul_zero, add_zero] at hlim
  filter_upwards [hbudget, hB0, eventually_gt_atTop (1 : ℕ),
    hlim.eventually (gt_mem_nhds hk)] with M hM hM0 hM1 hlimM
  exact (lcm_error_mul_log_le_of_natural_budget M hM1 _ _ (fun _ h => h)
    η (B M) hη hM0 hM).trans hlimM.le

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

open MeasureTheory
open MellinFrequency (criticalPoint)
open ParetoHorizontalZeroBridge (LegalConductor finiteResidueCandidate)
open ParetoFiniteMellinHalfPlane (finiteResidueError_boundary_zeta_energy)
open RiemannResearch.Analysis.SingleObservationProjection (affine_target_error_split)

/-- The image of a centered legal trial in the normalized zeta numerator. -/
def centeredZetaImage (D : Finset LegalConductor) (c : LegalConductor → ℝ) (t : ℝ) : ℂ :=
  riemannZeta (criticalPoint t) * ∑ d ∈ D,
    (c d : ℂ) * (1 / (d.val : ℂ) - (d.val : ℂ) ^ (-criticalPoint t))

def boundarySquare (f : ℝ → ℂ) (t : ℝ) : ℝ := ‖f t‖ ^ 2 / (1 / 4 + t ^ 2)

def shiftedZetaQuotient (ε t : ℝ) : ℂ :=
  riemannZeta (criticalPoint t) / riemannZeta (criticalPoint t + (ε : ℂ))

/-- Balazard--de Roton's two-budget splitting, directly for the actual
centered legal atoms. The second integral includes the index-one charge.
The two weighted integrals are the analytic inputs. -/
theorem lcmError_le_shifted_zeta_budgets (M : ℕ) (D : Finset LegalConductor)
    (c : LegalConductor → ℝ) (hd : ∀ d ∈ D, d.val ∣ Nat.lcmUpto M) (ε : ℝ)
    (hJ : Integrable (boundarySquare (fun t => 1 - shiftedZetaQuotient ε t)))
    (hI : Integrable
      (boundarySquare (fun t => shiftedZetaQuotient ε t - centeredZetaImage D c t))) :
    lcmError M ≤ (1 / (2 * Real.pi)) *
      (2 * ((∫ t, boundarySquare (fun u => 1 - shiftedZetaQuotient ε u) t) +
        ∫ t, boundarySquare (fun u => shiftedZetaQuotient ε u - centeredZetaImage D c u) t)) := by
  let q := shiftedZetaQuotient ε
  let b := centeredZetaImage D c
  let J := boundarySquare (fun t => 1 - q t)
  let I := boundarySquare (fun t => q t - b t)
  let F := finiteResidueCandidate D c
  have hf : F ∈ trialSpace (Nat.lcmUpto M) := by
    apply Submodule.sum_mem
    intro d hD
    apply Submodule.smul_mem
    exact atom_mem_trial _ _ (Nat.lcmUpto_pos M) (by have := d.property; omega) (hd d hD)
  have he := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne F hf
  change ‖hilbertOne - F‖ ^ 2 = lcmError M + ‖F - lcmBest M‖ ^ 2 at he
  have hopt : lcmError M ≤ ‖hilbertOne - F‖ ^ 2 := by
    linarith [sq_nonneg ‖F - lcmBest M‖]
  have hbd : (∫ t, boundarySquare (fun u => 1 - b u) t) ≤
      2 * ((∫ t, J t) + ∫ t, I t) := by
    have hg : Integrable (fun t => 2 * (J t + I t)) := (hJ.add hI).const_mul 2
    have hb : ∀ t : ℝ, boundarySquare (fun u => 1 - b u) t ≤ 2 * (J t + I t) := by
      intro t
      let x := 1 - q t
      let y := q t - b t
      have hxy : 1 - b t = x + y := by dsimp [x, y]; ring
      have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
      have h := hnorm.trans (show (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) by
        nlinarith [sq_nonneg (‖x‖ - ‖y‖)])
      change ‖1 - b t‖ ^ 2 / (1 / 4 + t ^ 2) ≤
        2 * (‖x‖ ^ 2 / (1 / 4 + t ^ 2) + ‖y‖ ^ 2 / (1 / 4 + t ^ 2))
      rw [hxy, ← add_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right h (by positivity)
    have hi := integral_mono_of_nonneg
      (Eventually.of_forall (fun t : ℝ => by unfold boundarySquare; positivity))
      hg (Eventually.of_forall hb)
    rw [integral_const_mul, integral_add hJ hI] at hi
    exact hi
  have hp := finiteResidueError_boundary_zeta_energy D c
  change (1 / (2 * Real.pi)) * (∫ t, boundarySquare (fun u => 1 - b u) t) =
    ‖hilbertOne - F‖ ^ 2 at hp
  rw [← hp] at hopt
  exact hopt.trans (mul_le_mul_of_nonneg_left hbd (by positivity))

/-- The exact horizontal condition for contraction of one zero factor
in the shifted quotient. -/
theorem shifted_zero_factor_sq_le_iff (s ρ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ‖s - ρ‖ ^ 2 ≤ ‖s + (ε : ℂ) - ρ‖ ^ 2 ↔ ρ.re ≤ s.re + ε / 2 := by
  have he : ‖s + (ε : ℂ) - ρ‖ ^ 2 - ‖s - ρ‖ ^ 2 = ε * (2 * (s.re - ρ.re) + ε) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero]
    ring
  constructor
  · intro h
    by_contra! hbad
    have hneg : ε * (2 * (s.re - ρ.re) + ε) < 0 :=
      mul_neg_of_pos_of_neg hε (by linarith)
    linarith
  · intro h
    have hnon : 0 ≤ ε * (2 * (s.re - ρ.re) + ε) :=
      mul_nonneg hε.le (by linarith)
    linarith

/-- Horizontal displacement controls the modulus of each BCF zero factor. -/
theorem bcf_zero_power_norm (M : ℕ) (hM : 0 < M) (s ρ : ℂ) :
    ‖(M : ℂ) ^ (ρ - s)‖ = (M : ℝ) ^ (ρ.re - s.re) := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hM), Complex.sub_re]

variable {ι : Type*} [Fintype ι]

/-- Inverse log of reciprocal error is an automatic inequality on the error's
own scale. Its right side shrinks only when the original error does. -/
theorem lcm_remainder_mul_log_inv_error_le (M : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    lcmRemainder z M * Real.log ((lcmError M)⁻¹) ≤ 1 - lcmError M := by
  have he := lcm_best_error_eq M z hs hs1 hz
  change lcmError M = _ at he
  have hp : 0 < lcmError M := by
    have hw := classWeight_pos (lcmResidueIndex M) (Fin.last (lcmResidueIndex M))
    have hc := certificateEnergy_nonneg (lcmResidueIndex M) z
    have hr : 0 ≤ lcmRemainder z M := sq_nonneg _
    linarith
  have hlog : 0 ≤ Real.log ((lcmError M)⁻¹) := by
    apply Real.log_nonneg
    rw [← one_div, le_div_iff₀ hp, one_mul]
    exact lcmError_le_one M
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  calc
    _ ≤ lcmError M * Real.log ((lcmError M)⁻¹) :=
      mul_le_mul_of_nonneg_right (lcmRemainder_le_error M z hs hs1 hz) hlog
    _ ≤ lcmError M * ((lcmError M)⁻¹ - 1) := mul_le_mul_of_nonneg_left hl hp.le
    _ = _ := by rw [mul_sub, mul_inv_cancel₀ hp.ne', mul_one]

end RiemannResearch.RH.Pareto.ResidueMellin
