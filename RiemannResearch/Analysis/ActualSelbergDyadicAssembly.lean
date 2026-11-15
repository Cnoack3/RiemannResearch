/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DyadicPowerLogBound
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform dyadic assembly beyond Selberg's one-quarter exponent

Source for the proof strategy: Baluyot, *On the Zeros of Riemann's
Zeta-function* (2017), section 3.6, equations (3.6.12)--(3.6.13) and
printed pp. 142--143:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The exact dyadic identity retains the finite initial zero count and every
window, with actual analytic multiplicities and inclusive real-part cutoffs.
The uniform assembly works for 0 <= a < 2, hence throughout 0 < a < 8/7,
without a loss of exponent. This range is for the assembly theorem only.
It does not assert a density provider beyond the published range.

The final theorem discharges the narrow logarithmic band by total counting
and combines a near-line weighted-excess input with an away-line window
input. Both analytic inputs remain explicit. The mollified moment and
Kloosterman estimates are not proved here; neither is RH.
-/

noncomputable section
open Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem rightInclusiveCount_monotone_height (σ : ℝ) :
    Monotone (fun T => rightInclusiveCount T σ) := by
  intro H T hHT
  change rightInclusiveCount H σ ≤ rightInclusiveCount T σ
  rw [rightInclusiveCount_split hHT]
  exact le_add_of_nonneg_right (rightInclusiveWindow_nonneg H T σ)

/-- Every dyadic shell and the complete finite head are retained. -/
theorem rightInclusiveCount_dyadic_exact (H σ : ℝ) (hH : 0 ≤ H) (n : ℕ) :
    rightInclusiveCount (H * 2 ^ n) σ = rightInclusiveCount H σ +
      ∑ k ∈ Finset.range n,
        rightInclusiveWindow (H * 2 ^ k) (H * 2 ^ (k + 1)) σ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : H * 2 ^ n ≤ H * 2 ^ (n + 1) := by
        rw [pow_succ]
        nlinarith [mul_nonneg hH (show (0 : ℝ) ≤ 2 ^ n by positivity)]
      rw [rightInclusiveCount_split hstep, ih, Finset.sum_range_succ]
      ring

/-- Dyadic window bounds with one constant for all sigma assemble without
losing the density exponent. The analytic window estimate is explicit. -/
theorem uniformSelbergDensity_of_dyadic_windows
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a < 2)
    (hwindow : ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧
      ∀ T : ℝ, 2 * H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
        rightInclusiveWindow (T / 2) T σ ≤
          D * T ^ (1 - a * (σ - 1 / 2)) * Real.log T) :
    UniformSelbergDensity a := by
  obtain ⟨D, H, hD, hH, hw⟩ := hwindow
  let r : ℝ := (2 : ℝ) ^ (-(1 - a / 2))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    calc
      _ < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero _
  let A : ℝ := (Zeta23.Ncount 0 (2 * H) : ℝ) / Real.log H
  have hA : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) (Real.log_pos hH).le
  let K : ℝ := (A + D) / (1 - r)
  have hden : 0 < 1 - r := by linarith
  have hK : 0 ≤ K := div_nonneg (add_nonneg hA hD) hden.le
  have heq : K * (1 - r) = A + D := div_mul_cancel₀ _ hden.ne'
  have hAK : A ≤ K := by nlinarith [mul_nonneg hK hr0]
  have hc : K * r + D ≤ K := by nlinarith
  refine ⟨K, H, hK, hH, ?_⟩
  intro T hT σ hσ
  have hp0 : 0 ≤ 1 - a * (σ - 1 / 2) := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hσ.2)]
  have hscale : (2 : ℝ) ^ (-(1 - a * (σ - 1 / 2))) ≤ r := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hσ.2)]
  apply bound_of_dyadic_power_log (fun t => rightInclusiveCount t σ)
    hH hK hp0 (rightInclusiveCount_monotone_height σ) ?_ hscale hc ?_ T hT
  · calc
      rightInclusiveCount (2 * H) σ ≤ (Zeta23.Ncount 0 (2 * H) : ℝ) :=
        rightInclusiveCount_le_count _ _
      _ = A * Real.log H := (div_mul_cancel₀ _ (Real.log_pos hH).ne').symm
      _ ≤ K * Real.log H := mul_le_mul_of_nonneg_right hAK (Real.log_pos hH).le
  · intro S hS
    rw [← rightInclusiveWindow_eq_sub (show S / 2 ≤ S by linarith [hH])]
    exact hw S hS σ hσ


/-- Exact equivalence of global and dyadic formulations in the positive
power range. It is an interface theorem, not a density provider. -/
theorem uniformSelbergDensity_iff_dyadic_windows
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a < 2) :
    UniformSelbergDensity a ↔
      ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧
        ∀ T : ℝ, 2 * H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
          rightInclusiveWindow (T / 2) T σ ≤
            D * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  constructor
  · rintro ⟨D, H, hD, hH, hglobal⟩
    refine ⟨D, H, hD, hH, ?_⟩
    intro T hT σ hσ
    have hsub : T / 2 ≤ T := by linarith [hH]
    rw [rightInclusiveWindow_eq_sub hsub]
    exact (sub_le_self _ (rightInclusiveCount_nonneg _ _)).trans
      (hglobal T (by linarith [hH]) σ hσ)
  · exact uniformSelbergDensity_of_dyadic_windows ha ha2

/-- The full open published range can be supplied by uniform dyadic bounds.
Constants may depend on a; the endpoint 8/7 is not included. -/
theorem conreyBaluyotDensity_iff_dyadic_windows :
    ConreyBaluyotDensityHypothesis ↔
      ∀ a : ℝ, 0 < a → a < 8 / 7 →
        ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧
          ∀ T : ℝ, 2 * H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
            rightInclusiveWindow (T / 2) T σ ≤
              D * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  constructor
  · intro h a ha ha'
    exact (uniformSelbergDensity_iff_dyadic_windows ha.le (by linarith)).mp
      (h a ha ha')
  · intro h a ha ha'
    exact (uniformSelbergDensity_iff_dyadic_windows ha.le (by linarith)).mpr
      (h a ha ha')


/-- Near-line weighted zero excess, together with an away-line window bound,
supplies the complete uniform density estimate. The narrow logarithmic band
is discharged by the unconditional total-count theorem. Both analytic inputs
remain explicit, and no exponent is lost. -/
theorem uniformSelbergDensity_of_near_excess_and_far_windows
    {a η : ℝ} (ha : 0 < a) (ha2 : a < 2)
    (hnear : ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) (1 / 2 + η),
        rightLogExcessWindow (T / 2) T α ≤
          D * T * Real.exp (-(a * Real.log T) * (α - 1 / 2)))
    (hfar : ∃ F H : ℝ, 0 ≤ F ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 + η) (1 : ℝ),
        rightInclusiveWindow (T / 2) T σ ≤
          F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T) :
    UniformSelbergDensity a := by
  obtain ⟨D, H₁, hD, hH₁, hnear⟩ := hnear
  obtain ⟨F, H₂, hF, hH₂, hfar⟩ := hfar
  obtain ⟨B, hB, hband⟩ := exists_selberg_form_on_logarithmic_strip a (1 / a) ha.le
  let H : ℝ := max (max H₁ H₂) 9
  let K : ℝ := max B (max (a * Real.exp 1 * D) F)
  have hBH : B ≤ K := le_max_left _ _
  have hDH : a * Real.exp 1 * D ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hFH : F ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hHone : 1 < H := hH₁.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  apply uniformSelbergDensity_of_dyadic_windows ha.le ha2
  refine ⟨K, H, hB.le.trans hBH, hHone, ?_⟩
  intro T hT σ hσ
  have hHT : H ≤ T := by linarith
  have hT₁ : H₁ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hHT
  have hT₂ : H₂ ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hHT
  have hT9 : 9 ≤ T := (le_max_right _ _).trans hHT
  have hT1 : 1 < T := hHone.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have enlarge {C : ℝ} (hCK : C ≤ K) :
      C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T ≤
        K * T ^ (1 - a * (σ - 1 / 2)) * Real.log T :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hT0.le _)) hL.le
  by_cases hs : 1 / 2 + η ≤ σ
  · exact (hfar T hT₂ σ ⟨hs, hσ.2⟩).trans (enlarge hFH)
  by_cases hb : (σ - 1 / 2) * Real.log T ≤ 1 / a
  · have hw : rightInclusiveWindow (T / 2) T σ ≤ rightInclusiveCount T σ := by
      rw [rightInclusiveWindow_eq_sub (show T / 2 ≤ T by linarith)]
      exact sub_le_self _ (rightInclusiveCount_nonneg _ _)
    exact hw.trans ((hband T hT9 σ hb).trans (enlarge hBH))
  · have hq : 0 < a * Real.log T := mul_pos ha hL
    have hbudget : 1 < ((σ - 1 / 2) * Real.log T) * a :=
      (div_lt_iff₀ ha).mp (lt_of_not_ge hb)
    have hshift : 1 / (a * Real.log T) ≤ σ - 1 / 2 := by
      apply (div_le_iff₀ hq).mpr
      nlinarith
    have hα : σ - 1 / (a * Real.log T) ∈ Icc (1 / 2 : ℝ) (1 / 2 + η) := by
      constructor
      · linarith
      · linarith [one_div_pos.mpr hq]
    have hexcess := hnear T hT₁ _ hα
    have hsource : rightLogExcessWindow (T / 2) T (σ - 1 / (a * Real.log T)) ≤
        D * T * Real.exp (-(a * Real.log T) * (σ - 1 / (a * Real.log T) - 1 / 2)) +
          0 * Real.log T := by simpa using hexcess
    have hw := densityWindow_le_of_shifted_logExcess hT1 ha hsource
    calc
      rightInclusiveWindow (T / 2) T σ ≤
          (a * Real.exp 1 * D) * T * Real.log T *
            Real.exp (-(a * Real.log T) * (σ - 1 / 2)) := by simpa using hw
      _ = (a * Real.exp 1 * D) * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
        nlinarith only [congrArg (fun x : ℝ => (a * Real.exp 1 * D) * x)
          (selberg_power_kernel_eq_exp T a σ hT0)]
      _ ≤ K * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := enlarge hDH

end RiemannResearch.Analysis.ActualZeroOrdinate
