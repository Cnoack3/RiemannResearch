/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.RamanujanZeroSignal
import RiemannResearch.Analysis.ActualUniformRationalLandau
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ExplicitSamplingHeights

/-!
# Actual zero sampling at explicit exponential heights

Source: user-provided constructive approximants handoff, 24 October 2026,
Section 5. The true inverse-Gram budgets and larger conductor weight below
make its height schedule work with the existing unconditional contour theorem
`exists_uniform_rational_landau_rpow_bound`. No new Landau provider is assumed.
The theorem includes actual zeros and analytic multiplicities. Its constant
is proved to exist; a numerical value is not extracted in this module.

Primary sources for the classical analytic estimates and proof strategy:
* S. M. Gonek, A Formula of Landau and Mean Values of zeta(s), Theorem 1:
  https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf
* Aleksander Simonic, Explicit zero density estimate for the Riemann zeta-function
  near the critical line, Theorem 1 and corollary:
  https://arxiv.org/html/1910.08274v2

Formalization boundary: a cited paper is not a kernel provider. The strict-tail
and Selberg estimates below remain displayed hypotheses. The numerical strict-
tail specialization is only a conditional reduction. In particular no theorem
here proves the actual density estimate, RH, or the arithmetic full-energy bound.
-/

noncomputable section

open RiemannResearch.Analysis
open FiniteHilbertGram FiniteGramCapacity FiniteGramSignalStability
open ActualZeroOrdinate ActualZeroCoshMass ExplicitSamplingHeights

namespace RiemannResearch.RH.RamanujanZeroSignal


/-- A conductor weight supplied by the existing unconditional contour estimate. -/
def actualLandauWeight (q : ℕ) : ℝ :=
  (2 * Real.pi * Real.sqrt (q : ℝ)) *
    ((q : ℝ) ^ (5 / 2 : ℝ) + (q : ℝ) ^ (3 / 2 : ℝ) + q)

theorem actualLandauWeight_nonneg (q : ℕ) : 0 ≤ actualLandauWeight q := by
  unfold actualLandauWeight
  positivity

/-- Uniform actual integer-mode Landau error; its constant is proved to exist,
not introduced as an analytic provider hypothesis. -/
theorem exists_actual_landauSignal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (T : ℝ), 1 < q → 9 ≤ T →
      |landauSignal q T - ArithmeticFunction.vonMangoldt q| ≤
        actualLandauWeight q * (C * (1 + Real.log (T + 3) ^ 2) / T) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  intro q T hq hT
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hc : 0 ≤ 2 * Real.pi * Real.sqrt (q : ℝ) := by positivity
  have hmain := rationalLandauMain_eq_vonMangoldt_div_sqrt (n := q) (m := 1)
    (by norm_num) hq
  simp only [Nat.one_dvd, if_true, Nat.div_one, Nat.cast_one, div_one] at hmain
  have hr : (((T * rationalLandauMain q 1 : ℝ) : ℂ) / (T : ℂ)).re =
      rationalLandauMain q 1 := by
    rw [← Complex.ofReal_div]
    simp [hT0.ne']
  have hid : landauSignal q T - ArithmeticFunction.vonMangoldt q =
      -(2 * Real.pi * Real.sqrt (q : ℝ)) *
        ((landauSum T (Real.log (q : ℝ)) +
          ((T * rationalLandauMain q 1 : ℝ) : ℂ)) / (T : ℂ)).re := by
    rw [landauSignal, add_div, Complex.add_re, hr, hmain]
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr hq0).ne']
    <;> ring
  have hraw := hbound T (q : ℝ) q 1 hT (by norm_num) hq le_rfl
  simp only [Nat.cast_one, div_one] at hraw
  let L := Real.log (T + 3)
  have henv : (q : ℝ) ^ (5 / 2 : ℝ) + (q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 + q * L ≤
      ((q : ℝ) ^ (5 / 2 : ℝ) + (q : ℝ) ^ (3 / 2 : ℝ) + q) * (1 + L ^ 2) := by
    have ha := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + L ^ 2 by nlinarith [sq_nonneg L])
      (Real.rpow_nonneg (Nat.cast_nonneg q) (5 / 2 : ℝ))
    have hb := mul_le_mul_of_nonneg_left (show L ^ 2 ≤ 1 + L ^ 2 by linarith)
      (Real.rpow_nonneg (Nat.cast_nonneg q) (3 / 2 : ℝ))
    have hc' := mul_le_mul_of_nonneg_left
      (show L ≤ 1 + L ^ 2 by nlinarith [sq_nonneg (L - 1 / 2)])
      (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  rw [hid, abs_mul, abs_neg, abs_of_nonneg hc]
  calc
    _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
        ‖(landauSum T (Real.log (q : ℝ)) +
          ((T * rationalLandauMain q 1 : ℝ) : ℂ)) / (T : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc
    _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
        (C * ((q : ℝ) ^ (5 / 2 : ℝ) +
          (q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 + q * L) / T) := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
      exact div_le_div_of_nonneg_right hraw hT0.le
    _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
        (C * (((q : ℝ) ^ (5 / 2 : ℝ) + (q : ℝ) ^ (3 / 2 : ℝ) + q) *
          (1 + L ^ 2)) / T) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left henv hC.le) hT0.le) hc
    _ = _ := by unfold actualLandauWeight; dsimp [L]; ring

/-- Actual inverse-matrix cost for a nonnegative coordinate weight. -/
def inverseGramWeightNorm (s : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  Real.sqrt (inverseGramWeightBudget s weight)

theorem inverseGramWeightBudget_nonneg (s : Finset ℕ) (weight : ℕ → ℝ)
    (hw : ∀ q ∈ s, 0 ≤ weight q) : 0 ≤ inverseGramWeightBudget s weight := by
  classical
  unfold inverseGramWeightBudget
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (hw i.val i.property)) (hw j.val j.property)))

/-- The complete inverse Gram matrix is retained; no diagonal approximation. -/
theorem inverseNorm_le_weightNorm (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (e : s → ℝ) (E : ℝ) (weight : ℕ → ℝ) (hE : 0 ≤ E)
    (hw : ∀ q ∈ s, 0 ≤ weight q) (he : ∀ i : s, |e i| ≤ weight i.val * E) :
    inverseNorm (family_independent s hs) e ≤ E * inverseGramWeightNorm s weight := by
  classical
  have h := inverseNorm_sq_le_entrywise (family_independent s hs) e
    (fun i => weight i.val * E) (fun i => mul_nonneg (hw i.val i.property) hE) he
  have hsq : inverseNorm (family_independent s hs) e ^ 2 ≤
      E ^ 2 * inverseGramWeightBudget s weight := by
    apply h.trans_eq
    simp only [inverseGramWeightBudget, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr : (inverseGramWeightNorm s weight) ^ 2 = inverseGramWeightBudget s weight :=
    Real.sq_sqrt (inverseGramWeightBudget_nonneg s weight hw)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hE (Real.sqrt_nonneg _))).mp
  change inverseNorm (family_independent s hs) e ^ 2 ≤
    (E * inverseGramWeightNorm s weight) ^ 2
  simpa only [mul_pow, hr] using hsq

/-- The existing actual Landau theorem plus the literal horizontal energy
provides a quantitative bound for every finite dictionary. -/
theorem exists_actual_sampled_inverseNorm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (T : ℝ), 9 ≤ T →
      inverseNorm (family_independent s hs) (sampledVector s T - signal s) ≤
        (horizontalEnergy T / T) * inverseGramWeightNorm s horizontalSignalWeight +
        (C * (1 + Real.log (T + 3) ^ 2) / T) * inverseGramWeightNorm s actualLandauWeight := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_landauSignal_bound
  refine ⟨C, hC, ?_⟩
  intro s hs T hT
  have hT0 : 0 < T := by linarith
  have hL := inverseNorm_le_weightNorm s hs (landauVector s T - signal s)
    (C * (1 + Real.log (T + 3) ^ 2) / T) actualLandauWeight (by positivity)
    (fun q _ => actualLandauWeight_nonneg q) (fun i => hbound i.val T (hs _ i.property) hT)
  have hD := inverseNorm_le_weightNorm s hs (densityDefect s T)
    (horizontalEnergy T / T) horizontalSignalWeight
    (div_nonneg (horizontalEnergy_nonneg T) hT0.le)
    (fun q _ => horizontalSignalWeight_nonneg q)
    (fun i => sampledSignal_sub_landauSignal_abs_le i.val T hT0)
  rw [signal_error_decomposition]
  exact (inverseNorm_add_le (family_independent s hs) _ _).trans (by linarith)

end RiemannResearch.RH.RamanujanZeroSignal

namespace RiemannResearch.Analysis.ExplicitSamplingHeights


/-- Elementary cubic majorant at the schedule's initial height. -/
theorem cube_le_exp_of_sixteen_le (M : ℝ) (hM : 16 ≤ M) : M ^ 3 ≤ Real.exp M := by
  have hhalf := sq_le_exp_of_nonneg (M / 2) (by linarith)
  have hsq : ((M / 2) ^ 2) ^ 2 ≤ Real.exp (M / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf)
      (show 0 ≤ Real.exp (M / 2) + (M / 2) ^ 2 by positivity)]
  have hexp : Real.exp (M / 2) ^ 2 = Real.exp M := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsq
  have hlarge : 16 * M ^ 3 ≤ M ^ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ M - 16 by linarith)
      (show 0 ≤ M ^ 3 by positivity)]
  nlinarith

/-- The unconditional contour envelope decays at an explicit exponential
height; the factor five permits a simple conductor weight. -/
theorem actual_landau_height_envelope (M : ℝ) (hM : 16 ≤ M) :
    (1 + Real.log (Real.exp M + 3) ^ 2) / Real.exp M ≤ 5 / M := by
  have hM0 : 0 < M := by linarith
  have hexp := Real.add_one_le_exp M
  have hlog : Real.log (Real.exp M + 3) ≤ 2 * M := by
    calc
      _ ≤ Real.log (Real.exp (2 * M)) := by
        apply Real.log_le_log (by positivity)
        rw [show 2 * M = M + M by ring, Real.exp_add]
        nlinarith
      _ = _ := Real.log_exp _
  have hlog0 : 0 ≤ Real.log (Real.exp M + 3) := Real.log_nonneg (by linarith)
  have hs : Real.log (Real.exp M + 3) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * M - Real.log (Real.exp M + 3) by linarith)
      (show 0 ≤ 2 * M + Real.log (Real.exp M + 3) by positivity)]
  have h1 : 1 + Real.log (Real.exp M + 3) ^ 2 ≤ 5 * M ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right h1 hM0.le
  apply (div_le_div_iff₀ (Real.exp_pos M) hM0).mpr
  nlinarith [cube_le_exp_of_sixteen_le M hM]



/-- The published strict-count convention feeds this exact analytic interface.
No conversion to an inclusive count is required. -/
theorem horizontalEnergy_ratio_of_strictTail_at_exp
    (M C a : ℝ) (hM : 0 < M) (hC : 0 ≤ C) (ha : 0 < a)
    (hdecay : 2 ≤ a * M)
    (htail : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      rightStrictTail (Real.exp M) t ≤ C * Real.exp M * M * Real.exp (-(a * M) * t)) :
    horizontalEnergy (Real.exp M) / Real.exp M ≤ (8 * C / a ^ 2) / M := by
  have hraw := horizontalEnergy_le_of_right_expTail (Real.exp M)
    (C * Real.exp M * M) (a * M) (by positivity) (by linarith) htail
  have hden : 0 < (a * M) ^ 2 - 1 := by nlinarith
  have hsquare : 2 ≤ (a * M) ^ 2 := by nlinarith
  calc
    _ ≤ (4 * (C * Real.exp M * M) / ((a * M) ^ 2 - 1)) / Real.exp M :=
      div_le_div_of_nonneg_right hraw (Real.exp_pos M).le
    _ = 4 * C * M / ((a * M) ^ 2 - 1) := by field_simp
    _ ≤ 8 * C / (a ^ 2 * M) := by
      apply (div_le_div_iff₀ hden (by positivity : 0 < a ^ 2 * M)).mpr
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hsquare)]
    _ = _ := by ring

/-- Numerical consequence of a precisely stated strict-tail provider.
The provider is a hypothesis, not a formalization of the cited publication. -/
theorem horizontalEnergy_ratio_of_simonic_tail_at_exp
    (M : ℝ) (hM : 16 ≤ M)
    (htail : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      rightStrictTail (Real.exp M) t ≤
        24000 * Real.exp M * M * Real.exp (-((1 / 8 : ℝ) * M) * t)) :
    horizontalEnergy (Real.exp M) / Real.exp M ≤ 12288000 / M := by
  have h := horizontalEnergy_ratio_of_strictTail_at_exp M 24000 (1 / 8)
    (by linarith) (by norm_num) (by norm_num) (by linarith) htail
  norm_num at h ⊢
  exact h


/-- The inclusive Selberg interface yields the same explicit horizontal bound.
The Selberg estimate itself remains a hypothesis. -/
theorem horizontalEnergy_ratio_of_selberg_at_exp
    (M C a : ℝ) (hM : 0 < M) (hC : 0 ≤ C) (ha : 0 < a)
    (hdecay : 2 ≤ a * M) (hD : SelbergDensityBound (Real.exp M) C a) :
    horizontalEnergy (Real.exp M) / Real.exp M ≤ (8 * C / a ^ 2) / M := by
  apply horizontalEnergy_ratio_of_strictTail_at_exp M C a hM hC ha hdecay
  have htail := rightStrictTail_of_selbergDensity (Real.exp M) C a (Real.exp_pos M) hD
  simpa only [Real.log_exp] using htail

end RiemannResearch.Analysis.ExplicitSamplingHeights

namespace RiemannResearch.RH.RamanujanZeroSignal


/-- Explicit exponential heights using the already proved actual Landau input.
Only the displayed horizontal-energy inequality is an analytic hypothesis.
Integer weights majorize two finite quantities from the true inverse Gram. -/
theorem exists_actual_explicit_sampling_schedule_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (w : ℕ → ℕ) (j : ℕ), 0 < j →
      ∀ D : ℝ, 0 ≤ D →
      inverseGramWeightNorm s horizontalSignalWeight ≤ (w j : ℝ) →
      inverseGramWeightNorm s actualLandauWeight ≤ (w j : ℝ) →
      horizontalEnergy (Real.exp (logHeight w j : ℝ)) / Real.exp (logHeight w j : ℝ) ≤
        D / (logHeight w j : ℝ) →
      inverseNorm (family_independent s hs)
        (sampledVector s (Real.exp (logHeight w j : ℝ)) - signal s) ≤
          (D + 5 * C) / (j : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_sampled_inverseNorm_bound
  refine ⟨C, hC, ?_⟩
  intro s hs w j hj D hD hwH hwL henergy
  have hM : (16 : ℝ) ≤ logHeight w j := by exact_mod_cast logHeight_ge_sixteen w hj
  have hT : (9 : ℝ) ≤ Real.exp (logHeight w j : ℝ) := by
    have he := Real.add_one_le_exp (logHeight w j : ℝ)
    linarith
  have hb := hbound s hs (Real.exp (logHeight w j : ℝ)) hT
  have hh := mul_le_mul_of_nonneg_right henergy
    (Real.sqrt_nonneg (inverseGramWeightBudget s horizontalSignalWeight))
  have hl := mul_le_mul_of_nonneg_left (actual_landau_height_envelope (logHeight w j : ℝ) hM)
    (mul_nonneg hC.le (Real.sqrt_nonneg (inverseGramWeightBudget s actualLandauWeight)))
  have hrH := (logHeight_budget_ratio w hj
    (inverseGramWeightNorm s horizontalSignalWeight) 1 hwH (by simpa using hwH)).1
  have hrL := (logHeight_budget_ratio w hj
    (inverseGramWeightNorm s actualLandauWeight) 1 hwL (by simpa using hwL)).1
  have hd := mul_le_mul_of_nonneg_left hrH hD
  have hc := mul_le_mul_of_nonneg_left hrL (show 0 ≤ 5 * C by positivity)
  calc
    _ ≤ (horizontalEnergy (Real.exp (logHeight w j : ℝ)) /
          Real.exp (logHeight w j : ℝ)) * inverseGramWeightNorm s horizontalSignalWeight +
        (C * (1 + Real.log (Real.exp (logHeight w j : ℝ) + 3) ^ 2) /
          Real.exp (logHeight w j : ℝ)) * inverseGramWeightNorm s actualLandauWeight := hb
    _ ≤ D * inverseGramWeightNorm s horizontalSignalWeight / (logHeight w j : ℝ) +
        5 * C * inverseGramWeightNorm s actualLandauWeight / (logHeight w j : ℝ) := by
      simp only [div_eq_mul_inv, inverseGramWeightNorm] at hh hl ⊢
      nlinarith
    _ ≤ (D + 5 * C) / (j : ℝ) := by
      simp only [div_eq_mul_inv] at hd hc ⊢
      nlinarith

end RiemannResearch.RH.RamanujanZeroSignal
