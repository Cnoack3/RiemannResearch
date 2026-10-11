/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact lag control for sampled ordinate phases

Source: user-provided
RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11.md,
Section 7 (adjacent-phase coalescence). The telescoping proof is extended
to arbitrary fixed or moving lags. Endpoint height control and any marginal
correlation limit are explicit hypotheses. These declarations do not supply
the classical actual-zero counting or scalar equidistribution providers.
No RH-dependent input is used.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.OrdinateLagPhase

def phase (u t : ℝ) : ℂ := Complex.exp (Complex.I * (u * t : ℝ))

@[simp] theorem norm_phase (u t : ℝ) : ‖phase u t‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem phase_norm_sub_le (u a b : ℝ) :
    ‖phase u a - phase u b‖ ≤ |u| * |a - b| := by
  have hid : phase u a - phase u b =
      phase u b * (Complex.exp (Complex.I * (u * (a - b) : ℝ)) - 1) := by
    unfold phase
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul, norm_phase, one_mul]
  calc
    _ ≤ ‖u * (a - b)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |u| * |a - b| := by rw [Real.norm_eq_abs, abs_mul]

/-- Exact exchange of the two boundary strips; no gap estimate is used. -/
theorem lag_gap_sum_identity (γ : ℕ → ℝ) (J ℓ : ℕ) :
    (∑ j ∈ Finset.range J, (γ (j + ℓ) - γ j)) =
      ∑ i ∈ Finset.range ℓ, (γ (J + i) - γ i) := by
  have hJ := Finset.sum_range_add γ J ℓ
  have hℓ : (∑ i ∈ Finset.range (J + ℓ), γ i) =
      (∑ i ∈ Finset.range ℓ, γ i) +
        ∑ j ∈ Finset.range J, γ (j + ℓ) := by
    simpa only [Nat.add_comm] using Finset.sum_range_add γ ℓ J
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith

/-- A lag `ℓ` costs at most `ℓ` copies of the endpoint height span. -/
theorem lag_gap_sum_le (γ : ℕ → ℝ) (hγ : Monotone γ) (J ℓ : ℕ) :
    (∑ j ∈ Finset.range J, (γ (j + ℓ) - γ j)) ≤
      (ℓ : ℝ) * (γ (J + ℓ) - γ 0) := by
  rw [lag_gap_sum_identity]
  calc
    _ ≤ ∑ i ∈ Finset.range ℓ, (γ (J + ℓ) - γ 0) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiℓ : i ≤ ℓ := (Finset.mem_range.mp hi).le
      have hu := hγ (Nat.add_le_add_left hiℓ J)
      have hl := hγ (Nat.zero_le i)
      linarith
    _ = _ := by simp; ring

def driftMean (z : ℕ → ℂ) (J ℓ : ℕ) : ℝ :=
  (∑ j ∈ Finset.range J, ‖z (j + ℓ) - z j‖) / (J : ℝ)

theorem driftMean_nonneg (z : ℕ → ℂ) (J ℓ : ℕ) :
    0 ≤ driftMean z J ℓ := by
  unfold driftMean
  positivity

theorem phase_driftMean_le (γ : ℕ → ℝ) (hγ : Monotone γ)
    (u : ℝ) (J ℓ : ℕ) :
    driftMean (fun j => phase u (γ j)) J ℓ ≤
      |u| * ((ℓ : ℝ) * (γ (J + ℓ) - γ 0) / (J : ℝ)) := by
  unfold driftMean
  have hs : (∑ j ∈ Finset.range J,
      ‖phase u (γ (j + ℓ)) - phase u (γ j)‖) ≤
      |u| * ((ℓ : ℝ) * (γ (J + ℓ) - γ 0)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, |u| * (γ (j + ℓ) - γ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hgap : 0 ≤ γ (j + ℓ) - γ j :=
          sub_nonneg.mpr (hγ (Nat.le_add_right j ℓ))
        simpa only [abs_of_nonneg hgap] using
          phase_norm_sub_le u (γ (j + ℓ)) (γ j)
      _ = |u| * (∑ j ∈ Finset.range J, (γ (j + ℓ) - γ j)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (lag_gap_sum_le γ hγ J ℓ) (abs_nonneg u)
  calc
    _ ≤ (|u| * ((ℓ : ℝ) * (γ (J + ℓ) - γ 0))) / (J : ℝ) :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg J)
    _ = _ := by ring

theorem phase_driftMean_tendsto_zero (γ : ℕ → ℝ) (hγ : Monotone γ)
    (u : ℝ) (lag : ℕ → ℕ)
    (hendpoint : Tendsto
      (fun J => (lag J : ℝ) * (γ (J + lag J) - γ 0) / (J : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun J => driftMean (fun j => phase u (γ j)) J (lag J))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun J => |u| * ((lag J : ℝ) * (γ (J + lag J) - γ 0) / (J : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hendpoint
  exact squeeze_zero (fun J => driftMean_nonneg _ J (lag J))
    (fun J => phase_driftMean_le γ hγ u J (lag J)) hupper

def correlationMean (z w : ℕ → ℂ) (J ℓ : ℕ) : ℂ :=
  (J : ℝ)⁻¹ • (∑ j ∈ Finset.range J, z j * star (w (j + ℓ)))

theorem selfCorrelationMean_eq_one (z : ℕ → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) (J : ℕ) (hJ : J ≠ 0) :
    correlationMean z z J 0 = 1 := by
  have hpoint (j : ℕ) : z j * star (z j) = 1 := by
    change z j * starRingEnd ℂ (z j) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz j]
    norm_num
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
  have hsum : (∑ j ∈ Finset.range J, z j * star (z (j + 0))) =
      (J : ℂ) := by
    calc
      _ = ∑ j ∈ Finset.range J, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Nat.add_zero] using hpoint j
      _ = _ := by simp
  calc
    correlationMean z z J 0 = (J : ℝ)⁻¹ • (J : ℂ) := by
      unfold correlationMean
      rw [hsum]
    _ = 1 := by
      rw [Complex.real_smul]
      exact_mod_cast inv_mul_cancel₀ hJr

theorem selfCorrelationMean_tendsto_one (z : ℕ → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    Tendsto (fun J => correlationMean z z J 0) atTop (𝓝 (1 : ℂ)) := by
  have heq : (fun J => correlationMean z z J 0) =ᶠ[atTop]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [eventually_ge_atTop 1] with J hJ
    exact selfCorrelationMean_eq_one z hz J (by omega)
  exact tendsto_const_nhds.congr' heq.symm

/-- Only the lagged second factor moves, so a unit first factor has cost one. -/
theorem correlationMean_sub_norm_le (z w : ℕ → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ 1) (J ℓ : ℕ) :
    ‖correlationMean z w J ℓ - correlationMean z w J 0‖ ≤
      driftMean w J ℓ := by
  have hs : (∑ j ∈ Finset.range J,
      ‖z j * star (w (j + ℓ)) - z j * star (w j)‖) ≤
      ∑ j ∈ Finset.range J, ‖w (j + ℓ) - w j‖ := by
    apply Finset.sum_le_sum
    intro j hj
    rw [← mul_sub, ← star_sub, norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hz j)
  have hinv : 0 ≤ (J : ℝ)⁻¹ := by positivity
  calc
    _ = (J : ℝ)⁻¹ * ‖∑ j ∈ Finset.range J,
        (z j * star (w (j + ℓ)) - z j * star (w j))‖ := by
      simp only [correlationMean, Nat.add_zero, ← smul_sub,
        ← Finset.sum_sub_distrib, norm_smul, Real.norm_of_nonneg hinv]
    _ ≤ (J : ℝ)⁻¹ * (∑ j ∈ Finset.range J,
        ‖z j * star (w (j + ℓ)) - z j * star (w j)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hinv
    _ ≤ (J : ℝ)⁻¹ * (∑ j ∈ Finset.range J, ‖w (j + ℓ) - w j‖) :=
      mul_le_mul_of_nonneg_left hs hinv
    _ = _ := by simp only [driftMean, div_eq_mul_inv, mul_comm]

/-- Vanishing average phase displacement transfers every diagonal correlation
limit to a fixed or moving lag. The marginal limit remains an explicit premise. -/
theorem correlationMean_tendsto_of_drift (z w : ℕ → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ 1) (lag : ℕ → ℕ) (L : ℂ)
    (hdiag : Tendsto (fun J => correlationMean z w J 0) atTop (𝓝 L))
    (hdrift : Tendsto (fun J => driftMean w J (lag J)) atTop (𝓝 0)) :
    Tendsto (fun J => correlationMean z w J (lag J)) atTop (𝓝 L) := by
  have hnorm : Tendsto
      (fun J => ‖correlationMean z w J (lag J) - correlationMean z w J 0‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun J => correlationMean_sub_norm_le z w hz J (lag J)) hdrift
  have hdiff : Tendsto
      (fun J => correlationMean z w J (lag J) - correlationMean z w J 0)
      atTop (𝓝 (0 : ℂ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [sub_add_cancel, zero_add] using hdiff.add hdiag

/-- Character-correlation transfer at a controlled moving ordinate lag. -/
theorem phase_correlationMean_tendsto (γ : ℕ → ℝ) (hγ : Monotone γ)
    (u v : ℝ) (lag : ℕ → ℕ) (L : ℂ)
    (hdiag : Tendsto
      (fun J => correlationMean (fun j => phase u (γ j))
        (fun j => phase v (γ j)) J 0) atTop (𝓝 L))
    (hendpoint : Tendsto
      (fun J => (lag J : ℝ) * (γ (J + lag J) - γ 0) / (J : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun J => correlationMean (fun j => phase u (γ j))
        (fun j => phase v (γ j)) J (lag J)) atTop (𝓝 L) := by
  apply correlationMean_tendsto_of_drift
  · intro j
    exact (norm_phase u (γ j)).le
  · exact hdiag
  · exact phase_driftMean_tendsto_zero γ hγ v lag hendpoint

/-- Same-frequency unscaled correlations converge to one solely from
counting-scale control; no equidistribution premise is required. -/
theorem phase_selfCorrelationMean_tendsto_one
    (γ : ℕ → ℝ) (hγ : Monotone γ) (u : ℝ) (lag : ℕ → ℕ)
    (hendpoint : Tendsto
      (fun J => (lag J : ℝ) * (γ (J + lag J) - γ 0) / (J : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun J => correlationMean (fun j => phase u (γ j))
        (fun j => phase u (γ j)) J (lag J)) atTop (𝓝 (1 : ℂ)) := by
  exact phase_correlationMean_tendsto γ hγ u u lag 1
    (selfCorrelationMean_tendsto_one _ (fun j => norm_phase u (γ j))) hendpoint

end RiemannResearch.Analysis.OrdinateLagPhase
