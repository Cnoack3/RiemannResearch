/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroFMZComparison
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit literature density hypotheses and actual-zero consequences

Source for the classical density statement: Ford--Zaharescu,
"On the distribution of imaginary parts of zeros of the Riemann zeta function",
Lemma 2, p. 7, https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
Source for the ordinate comparison application: Ford--Meng--Zaharescu,
"Simultaneous distribution of the fractional parts of Riemann zeta zeros",
Lemma 2 and Corollary 1.1, https://arxiv.org/abs/1511.06814 .

Source for the stronger density statement (not a formalized proof):
S. A. C. Baluyot, "On the Zeros of Riemann's Zeta-function" (2017),
Theorem 1.2.1 and Chapter 3, proving the theorem announced by Conrey:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
See also the author's statement on slide 6 of
https://maine-quebec.mat.ulaval.ca/CNTA_XV_website/docs/baluyot.pdf .
The source parameter is theta = a/2, so every fixed 0 < a < 8/7 is allowed.
There is no endpoint assertion at a = 8/7 and no uniformity in a.

Baluyot's count uses positive ordinates and the strict real-part cutoff.
The repository's count retains actual analytic multiplicities and includes
threshold copies. The left-limit transfer, including the total-count
endpoint at 1/2, is proved in ActualSelbergDensityConventions.
Classical Selberg gives a = 1/4 uniformly on 1/2 <= sigma <= 1.

As of 2026-11-15, the count conventions, dyadic assembly, truncated
near-line assembly and reduction to the Ingham estimate are proved.
The actual upper mollified moment, full Kloosterman estimates, horizontal
boundary estimate and Ingham density estimate still need Lean providers.
ConreyBaluyotDensityHypothesis is the explicit target proposition.
Constants may depend on a.

`ActualConreyBaluyotConsequences` uses the full open published range:
every fixed frequency-band width b < 8/7 is allowed, and any positive
density exponent suffices for fixed-mode convergence. Existing one-quarter
entry points remain compatible. None of these deductions discharges the
analytic density premise or proves RH.

The proved deductions include equivalence of the power and exponential
forms, exact strict/inclusive count transfer, the general FMZ rational majorant
and all fractional frequency bands, and loglog/log shrinking-strip rates.
The imported reflection and layer-cake identities preserve multiplicities,
signed summands, threshold copies and the complete finite endpoint terms.
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Pointwise uniform-in-sigma classical density input, with explicit constant and exponent. -/
def SelbergDensityBound (T C a : ℝ) : Prop :=
  ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
    rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T

/-- One constant and height threshold for every height and inclusive strip threshold. -/
def UniformSelbergDensity (a : ℝ) : Prop :=
  ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 < T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → SelbergDensityBound T C a

/-- The published Conrey--Baluyot range, whose analytic proof remains an open
formalization task. This named proposition is passed as an explicit theorem
hypothesis; it is not a provider or an axiom. Each exponent has its own
constants and height threshold. The endpoint `8 / 7` is excluded. -/
def ConreyBaluyotDensityHypothesis : Prop :=
  ∀ a : ℝ, 0 < a → a < 8 / 7 → UniformSelbergDensity a

/-- Extract precisely the classical input needed by existing ordinate
results. Those results do not require the full Conrey--Baluyot range. -/
theorem ConreyBaluyotDensityHypothesis.classical
    (hD : ConreyBaluyotDensityHypothesis) :
    UniformSelbergDensity (1 / 4) :=
  hD (1 / 4) (by norm_num) (by norm_num)

/-- An admissible stronger exponent for quantitative applications,
still conditional on the unformalized analytic density input. -/
theorem ConreyBaluyotDensityHypothesis.one
    (hD : ConreyBaluyotDensityHypothesis) :
    UniformSelbergDensity 1 :=
  hD 1 (by norm_num) (by norm_num)

/-- Exact power/exponential identity on the positive-height domain. -/
theorem selberg_power_kernel_eq_exp (T a σ : ℝ) (hT : 0 < T) :
    T ^ (1 - a * (σ - 1 / 2)) * Real.log T =
      T * Real.log T * Real.exp (-(a * Real.log T) * (σ - 1 / 2)) := by
  rw [Real.rpow_def_of_pos hT]
  rw [show Real.log T * (1 - a * (σ - 1 / 2)) =
    Real.log T + (-(a * Real.log T) * (σ - 1 / 2)) by ring,
    Real.exp_add, Real.exp_log hT]
  ring

/-- The conventional power estimate is exactly its exponential-tail formulation. -/
theorem selbergDensityBound_iff_exp (T C a : ℝ) (hT : 0 < T) :
    SelbergDensityBound T C a ↔
      ∀ σ ∈ Icc (1 / 2 : ℝ) 1, rightInclusiveCount T σ ≤
        C * T * Real.log T * Real.exp (-(a * Real.log T) * (σ - 1 / 2)) := by
  unfold SelbergDensityBound
  simp_rw [show ∀ σ : ℝ,
    C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T =
      C * T * Real.log T * Real.exp (-(a * Real.log T) * (σ - 1 / 2)) from
    fun σ => by
      calc
        _ = C * (T ^ (1 - a * (σ - 1 / 2)) * Real.log T) := by ring
        _ = _ := by rw [selberg_power_kernel_eq_exp T a σ hT]; ring]

/-- Inclusive density bounds the strict right tail without discarding threshold copies. -/
theorem rightStrictTail_of_selbergDensity (T C a : ℝ) (hT : 0 < T)
    (hD : SelbergDensityBound T C a) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ C * T * Real.log T * Real.exp (-(a * Real.log T) * t) := by
  intro t ht
  have hσ : 1 / 2 + t ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have h := (selbergDensityBound_iff_exp T C a hT).mp hD (1 / 2 + t) hσ
  have heq : 1 / 2 + t - 1 / 2 = t := by ring
  rw [heq] at h
  exact (rightStrictTail_le_inclusive T t).trans h

/-- Actual multiplicity-preserving reflection supplies precisely the factor two. -/
theorem strictTail_of_selbergDensity (T C a δ : ℝ) (hT : 0 < T)
    (hδ : δ ∈ Icc (0 : ℝ) (1 / 2)) (hD : SelbergDensityBound T C a) :
    strictTail T δ ≤ 2 * C * T * Real.log T * Real.exp (-(a * Real.log T) * δ) := by
  rw [strictTail_eq_twice_right T δ hδ.1]
  have h := mul_le_mul_of_nonneg_left
    (rightStrictTail_of_selbergDensity T C a hT hD δ hδ) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using h

/-- Density concentration with any explicit positive count normalization. -/
theorem normalized_strictTail_of_selbergDensity
    (T C a δ c : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (hc : 0 < c)
    (hδ : δ ∈ Icc (0 : ℝ) (1 / 2)) (hD : SelbergDensityBound T C a)
    (hN : c * T * Real.log T ≤ (Ncount 0 T : ℝ)) :
    strictTail T δ / (Ncount 0 T : ℝ) ≤
      (2 * C / c) * Real.exp (-(a * Real.log T) * δ) := by
  have hT₀ : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hN₀ : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  apply (div_le_iff₀ hN₀).mpr
  calc
    _ ≤ 2 * C * T * Real.log T * Real.exp (-(a * Real.log T) * δ) :=
      strictTail_of_selbergDensity T C a δ hT₀ hδ hD
    _ = ((2 * C / c) * Real.exp (-(a * Real.log T) * δ)) *
        (c * T * Real.log T) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

/-- Exact rate for a loglog/log window, allowing every real logarithmic exponent. -/
theorem selberg_movingWindow_exp (T a b : ℝ)
    (hL : 0 < Real.log T) (ha : a ≠ 0) :
    Real.exp (-(a * Real.log T) *
      ((b / a) * Real.log (Real.log T) / Real.log T)) =
        (Real.log T) ^ (-b) := by
  have heq : -(a * Real.log T) *
      ((b / a) * Real.log (Real.log T) / Real.log T) =
      Real.log (Real.log T) * (-b) := by
    field_simp [ha, ne_of_gt hL]
  rw [heq, Real.rpow_def_of_pos hL]

/-- Shrinking-strip concentration, with the entire normalizer and admissibility retained. -/
theorem normalized_strictTail_loglogWindow
    (T C a b c : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : a ≠ 0)
    (hc : 0 < c)
    (hδ : (b / a) * Real.log (Real.log T) / Real.log T ∈
      Icc (0 : ℝ) (1 / 2))
    (hD : SelbergDensityBound T C a)
    (hN : c * T * Real.log T ≤ (Ncount 0 T : ℝ)) :
    strictTail T ((b / a) * Real.log (Real.log T) / Real.log T) /
        (Ncount 0 T : ℝ) ≤ (2 * C / c) * (Real.log T) ^ (-b) := by
  have h := normalized_strictTail_of_selbergDensity T C a
    ((b / a) * Real.log (Real.log T) / Real.log T) c hT hC hc hδ hD hN
  rwa [selberg_movingWindow_exp T a b (Real.log_pos hT) ha] at h

/-- General-exponent actual FMZ comparison throughout the open density frequency band. -/
theorem normalized_ordinate_landau_error_of_selbergDensity
    (T u C a : ℝ) (hT : 1 < T) (hC : 0 ≤ C)
    (hu : |u| < a * Real.log T) (hD : SelbergDensityBound T C a) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      2 * C * Real.log T * u ^ 2 / ((a * Real.log T) ^ 2 - u ^ 2) := by
  have hT₀ : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have h := ordinate_landau_error_of_right_expTail T u
    (C * T * Real.log T) (a * Real.log T) (by positivity) hu
    (rightStrictTail_of_selbergDensity T C a hT₀ hD)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT₀]
  apply (div_le_iff₀ hT₀).mpr
  calc
    _ ≤ 2 * (C * T * Real.log T) * u ^ 2 / ((a * Real.log T) ^ 2 - u ^ 2) := h
    _ = _ := by ring

/-- Every fractional band below the density exponent has an explicit quadratic budget. -/
theorem normalized_ordinate_landau_error_of_selbergDensity_band
    (T u C a θ : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hu : |u| ≤ θ * (a * Real.log T)) (hD : SelbergDensityBound T C a) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      (2 * C / (a ^ 2 * (1 - θ ^ 2))) * u ^ 2 / Real.log T := by
  have hL : 0 < Real.log T := Real.log_pos hT
  have hq : 0 < a * Real.log T := mul_pos ha hL
  have hu' : |u| < a * Real.log T := lt_of_le_of_lt hu
    (by nlinarith [mul_pos (sub_pos.mpr hθ₁) hq])
  have hθsq : 0 < 1 - θ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hθ₁) (by linarith : 0 < 1 + θ)]
  have hs : 0 < (a * Real.log T) ^ 2 * (1 - θ ^ 2) := by positivity
  have hprod : 0 ≤ (θ * (a * Real.log T) - |u|) *
      (θ * (a * Real.log T) + |u|) := mul_nonneg (by linarith) (by positivity)
  have hden : (a * Real.log T) ^ 2 * (1 - θ ^ 2) ≤
      (a * Real.log T) ^ 2 - u ^ 2 := by nlinarith [hprod, sq_abs u]
  have hd : 0 < (a * Real.log T) ^ 2 - u ^ 2 := lt_of_lt_of_le hs hden
  apply (normalized_ordinate_landau_error_of_selbergDensity T u C a hT hC hu' hD).trans
  calc
    _ ≤ (2 * C * Real.log T * u ^ 2) /
        ((a * Real.log T) ^ 2 * (1 - θ ^ 2)) := by
      apply (div_le_div_iff₀ hd hs).mpr
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by
      field_simp [ne_of_gt hL, ne_of_gt ha, ne_of_gt hθsq]

/-- The existing unconditional Riemann--von Mangoldt theorem supplies the normalizer. -/
theorem eventually_normalized_strictTail_of_uniformSelberg
    (a : ℝ) (hD : UniformSelbergDensity a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ δ ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T δ / (Ncount 0 T : ℝ) ≤
        C * Real.exp (-(a * Real.log T) * δ) := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine ⟨2 * C / (1 / (16 * Real.pi)), by positivity, ?_⟩
  filter_upwards [eventually_count_ge_log, eventually_ge_atTop T₀] with T hN hT
  intro δ hδ
  exact normalized_strictTail_of_selbergDensity T C a δ (1 / (16 * Real.pi))
    (lt_of_lt_of_le hT₀ hT) hC (by positivity) hδ (hD T hT) hN


/-- The classical one-quarter Selberg input feeds the exact existing FMZ band. -/
theorem normalized_ordinate_landau_error_of_classical_selberg
    (T u C : ℝ) (hT : 1 < T) (hC : 0 ≤ C)
    (hu : |u| ≤ Real.log T / 8) (hD : SelbergDensityBound T C (1 / 4)) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      (128 * C / 3) * u ^ 2 / Real.log T := by
  have hu' : |u| ≤ (1 / 2 : ℝ) * ((1 / 4 : ℝ) * Real.log T) := by
    nlinarith
  have h := normalized_ordinate_landau_error_of_selbergDensity_band
    T u C (1 / 4) (1 / 2) hT hC (by norm_num) (by norm_num) (by norm_num) hu' hD
  convert h using 1; ring

/-- Uniform classical density supplies the existing actual fixed-mode limit.
The analytic density input remains explicit; the general positive-exponent
version is in ActualConreyBaluyotConsequences. -/
theorem tendsto_ordinate_landau_error_of_uniformSelberg
    (u : ℝ) (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  apply tendsto_ordinate_landau_error_div_of_selberg u C hC
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT₁ : 1 < T := lt_of_lt_of_le hT₀ hT
  have h := rightStrictTail_of_selbergDensity T C (1 / 4)
    (by linarith) (hD T hT)
  have heq : (1 / 4 : ℝ) * Real.log T = Real.log T / 4 := by ring
  simpa only [heq] using h

#print axioms selbergDensityBound_iff_exp
#print axioms ConreyBaluyotDensityHypothesis.classical
#print axioms ConreyBaluyotDensityHypothesis.one
#print axioms normalized_strictTail_loglogWindow
#print axioms normalized_ordinate_landau_error_of_selbergDensity_band
#print axioms normalized_ordinate_landau_error_of_classical_selberg
#print axioms tendsto_ordinate_landau_error_of_uniformSelberg
end RiemannResearch.Analysis.ActualZeroOrdinate
