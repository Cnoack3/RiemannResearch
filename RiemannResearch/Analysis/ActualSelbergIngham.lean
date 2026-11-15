/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergDyadicAssembly

/-!
# Ingham's estimate on the fixed strip away from the critical line

The input is Ingham's inclusive count bound as stated in Chourasiya and
Simonič, *An explicit form of Ingham's zero density estimate*,
https://arxiv.org/abs/2507.15184 . The application to Conrey--Baluyot is
the away-line step in Baluyot, *On the Zeros of Riemann's Zeta-function*
(2017), §3.6, p. 142. We retain the uniform exponent slack explicitly.
-/

noncomputable section
open Set

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Ingham's classical bound, stated for the project's actual inclusive count. -/
def InghamDensityBound : Prop :=
  ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧
    ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      rightInclusiveCount T σ ≤
        C * T ^ (3 * (1 - σ) / (2 - σ)) * (Real.log T) ^ 5

/-- On a fixed away-line strip, the Ingham exponent leaves uniform slack
to absorb the four extra logarithms. -/
theorem ingham_exponent_add_gap_le {a η σ : ℝ}
    (ha : a ≤ 4 / 3) (hη : 0 ≤ η) (hσ : σ ∈ Icc (1 / 2 + η) (1 : ℝ)) :
    3 * (1 - σ) / (2 - σ) + (4 / 3 - a) * η ≤ 1 - a * (σ - 1 / 2) := by
  have hhalf : (1 / 2 : ℝ) ≤ σ := by linarith [hσ.1]
  have hden : 0 < 2 - σ := by linarith [hσ.2]
  have hrate : (4 / 3 : ℝ) ≤ 2 / (2 - σ) := by
    apply (le_div_iff₀ hden).2
    linarith
  have hmul := mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hhalf)
  have hgap := mul_le_mul_of_nonneg_left (show η ≤ σ - 1 / 2 by linarith [hσ.1])
    (sub_nonneg.mpr ha)
  have heq : 3 * (1 - σ) / (2 - σ) =
      1 - (2 / (2 - σ)) * (σ - 1 / 2) := by
    field_simp
    <;> ring
  rw [heq]
  nlinarith only [hmul, hgap]

private theorem log_pow_four_le_rpow {T d : ℝ} (hT : 1 ≤ T) (hd : 0 < d) :
    (Real.log T) ^ 4 ≤ (4 / d) ^ 4 * T ^ d := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hx : d * Real.log T / 4 ≤ Real.exp (d * Real.log T / 4) := by
    linarith only [Real.add_one_le_exp (d * Real.log T / 4)]
  have hlog : Real.log T ≤ (4 / d) * Real.exp (d * Real.log T / 4) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).2
    nlinarith only [hx]
  have he : Real.exp (d * Real.log T / 4) ^ 4 = Real.exp (Real.log T * d) := by
    have hadd : Real.log T * d =
        (d * Real.log T / 4 + d * Real.log T / 4) +
          (d * Real.log T / 4 + d * Real.log T / 4) := by ring
    rw [hadd]
    simp only [Real.exp_add]
    ring
  calc
    _ ≤ ((4 / d) * Real.exp (d * Real.log T / 4)) ^ 4 :=
      pow_le_pow_left₀ (Real.log_nonneg hT) hlog 4
    _ = (4 / d) ^ 4 * T ^ d := by rw [mul_pow, he, Real.rpow_def_of_pos hT0]

/-- The exact strip-dependent slope preserves the nonlinear gain of Ingham's exponent. -/
theorem ingham_exponent_add_sharp_gap_le {a η σ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1/2)
    (ha : a ≤ 4/(3-2*η)) (hσ : σ ∈ Icc (1/2+η) (1 : ℝ)) :
    3*(1-σ)/(2-σ) + (4/(3-2*η)-a)*η ≤ 1-a*(σ-1/2) := by
  have hdη : 0 < 3-2*η := by linarith
  have hdσ : 0 < 2-σ := by linarith [hσ.2]
  have hrate : 4/(3-2*η) ≤ 2/(2-σ) := by
    apply (div_le_div_iff₀ hdη hdσ).mpr
    linarith [hσ.1]
  have hprod := mul_le_mul_of_nonneg_right hrate (show 0 ≤ σ-1/2 by linarith [hσ.1])
  have hgap := mul_le_mul_of_nonneg_left (show η ≤ σ-1/2 by linarith [hσ.1]) (sub_nonneg.mpr ha)
  have he : 3*(1-σ)/(2-σ) = 1-(2/(2-σ))*(σ-1/2) := by
    field_simp
    <;> ring
  rw [he]
  nlinarith only [hprod, hgap]

/-- The slope 4/(3-2eta) is optimal for the uniform exponent comparison
on this fixed strip: necessity already follows at its left endpoint. -/
theorem ingham_exponent_comparison_on_strip_iff {a η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    (∀ σ ∈ Icc (1 / 2+η) (1 : ℝ),
      3*(1-σ)/(2-σ) ≤ 1-a*(σ-1 / 2)) ↔ a ≤ 4/(3-2*η) := by
  have hd : 0 < 3-2*η := by linarith
  constructor
  · intro h
    have he := h (1 / 2+η) ⟨le_rfl, by linarith⟩
    have he' := (div_le_iff₀ (show 0 < 2-(1 / 2+η) by linarith)).mp he
    apply (le_div_iff₀ hd).mpr
    by_contra hn
    have hp := mul_pos hη (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  · intro ha σ hσ
    have h := ingham_exponent_add_sharp_gap_le hη.le hη' ha hσ
    have hg : 0 ≤ (4/(3-2*η)-a)*η := mul_nonneg (sub_nonneg.mpr ha) hη.le
    linarith

/-- The classical bound supplies away-line windows for a < 4/(3-2eta).
The explicit logarithm-absorption gap is (4/(3-2eta)-a)*eta. -/
theorem exists_selberg_far_windows_of_ingham_sharp
    {a η : ℝ} (ha : a < 4 / (3 - 2 * η)) (hη : 0 < η)
    (hη' : η ≤ 1 / 2) (hI : InghamDensityBound) :
    ∃ F H : ℝ, 0 ≤ F ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 + η) (1 : ℝ),
        rightInclusiveWindow (T / 2) T σ ≤
          F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  obtain ⟨C, H, hC, hH, hI⟩ := hI
  let d := (4 / (3 - 2 * η) - a) * η
  let F := C * (4 / d) ^ 4
  have hd : 0 < d := mul_pos (sub_pos.mpr ha) hη
  have hF : 0 ≤ F := mul_nonneg hC (pow_nonneg (by positivity) _)
  refine ⟨F, H, hF, hH, ?_⟩
  intro T hT σ hσ
  have hT1 : 1 ≤ T := hH.le.trans hT
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hL : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hσ' : σ ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  let k := 3 * (1 - σ) / (2 - σ)
  calc
    rightInclusiveWindow (T / 2) T σ ≤ rightInclusiveCount T σ := by
      rw [rightInclusiveWindow_eq_sub (show T / 2 ≤ T by linarith)]
      exact sub_le_self _ (rightInclusiveCount_nonneg _ _)
    _ ≤ C * T ^ k * (Real.log T) ^ 5 := hI T hT σ hσ'
    _ = C * T ^ k * ((Real.log T) ^ 4 * Real.log T) := by ring
    _ ≤ C * T ^ k * (((4 / d) ^ 4 * T ^ d) * Real.log T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (log_pow_four_le_rpow hT1 hd) hL)
        (mul_nonneg hC (Real.rpow_nonneg hT0.le _))
    _ = F * T ^ (k + d) * Real.log T := by
      rw [Real.rpow_add hT0]
      dsimp [F]
      ring
    _ ≤ F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
      apply mul_le_mul_of_nonneg_right _ hL
      apply mul_le_mul_of_nonneg_left _ hF
      exact Real.rpow_le_rpow_of_exponent_le hT1
        (ingham_exponent_add_sharp_gap_le hη.le hη' ha.le hσ)

/-- The endpoint a = 4/3 is permitted: the fixed strip supplies positive
nonlinear slack. The empty strip eta > 1/2 is handled without a restriction. -/
theorem exists_selberg_far_windows_of_ingham
    {a η : ℝ} (ha : a ≤ 4 / 3) (hη : 0 < η) (hI : InghamDensityBound) :
    ∃ F H : ℝ, 0 ≤ F ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 + η) (1 : ℝ),
        rightInclusiveWindow (T / 2) T σ ≤
          F * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  by_cases hη' : η ≤ 1 / 2
  · have hr : (4 / 3 : ℝ) < 4 / (3 - 2 * η) := by
      apply (lt_div_iff₀ (show 0 < 3 - 2 * η by linarith)).mpr
      linarith
    exact exists_selberg_far_windows_of_ingham_sharp (ha.trans_lt hr) hη hη' hI
  · refine ⟨0, 2, by norm_num, by norm_num, ?_⟩
    intro T hT σ hσ
    exfalso
    linarith [hσ.1, hσ.2]

/-- An Ingham-bound provider replaces the bespoke away-line window input. -/
theorem uniformSelbergDensity_of_near_excess_and_ingham
    {a η : ℝ} (ha : 0 < a) (ha' : a ≤ 4 / 3) (hη : 0 < η) (hI : InghamDensityBound)
    (hnear : ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) (1 / 2 + η),
        rightLogExcessWindow (T / 2) T α ≤
          D * T * Real.exp (-(a * Real.log T) * (α - 1 / 2))) :
    UniformSelbergDensity a :=
  uniformSelbergDensity_of_near_excess_and_far_windows ha (by linarith)
    hnear (exists_selberg_far_windows_of_ingham ha' hη hI)

end RiemannResearch.Analysis.ActualZeroOrdinate
