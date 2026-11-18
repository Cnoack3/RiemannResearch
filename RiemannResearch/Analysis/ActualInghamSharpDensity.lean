/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamDensityBound
import RiemannResearch.Analysis.ActualInghamSharpEndpoint

/-!
# The actual two-edge density bound with the sharp right moment

Put `q = 3*(1-σ)/(2-σ)`. The left and right integrals have budgets
`T (log T)^2` and `log T`. The signed Cauchy rectangle can therefore be
balanced at `Y = T log T`. It gives the log exponent `3+q` uniformly in
the entire closed half strip. Chourasiya and Simonič obtain `2+q` by the
Gabriel–Littlewood argument, <https://arxiv.org/abs/2507.15184>.
-/

noncomputable section
open Complex Set MeasureTheory Zeta23
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier

private theorem rightCountingMoment_log_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, Real.exp 16 ≤ T →
      inghamRightCountingMoment T ≤ A * Real.log T := by
  obtain ⟨K, hK, hr⟩ := exists_actual_moving_right_error_moment_log_one
    (δ := 1) (by norm_num)
  refine ⟨9 * K, by positivity, ?_⟩
  intro T hT
  let X := Nat.ceil T
  have hTp := (Real.exp_pos 16).trans_le hT
  have hT2 : 2 ≤ T := by linarith only [hT, Real.add_one_le_exp 16]
  have hℓ : 16 ≤ Real.log T := by simpa using Real.log_le_log (Real.exp_pos 16) hT
  have hx : T ≤ (X : ℝ) := Nat.le_ceil _
  have hx' : (X : ℝ) ≤ 2 * T := by dsimp [X]; linarith [Nat.ceil_lt_add_one hTp.le]
  have hx0 := hTp.trans_le hx
  have hx2 : 2 ≤ X := by exact_mod_cast hT2.trans hx
  have hspan : (2 * T - 1) / (X : ℝ) ≤ 2 := (div_le_iff₀ hx0).mpr (by linarith)
  have hlog : Real.log (X : ℝ) ≤ 2 * Real.log T := by
    apply (Real.log_le_log hx0 hx').trans
    rw [Real.log_mul (by norm_num) hTp.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hR := hr hx2 (H := 1) (T := 2 * T) (by linarith)
  simp only [inghamRightCountingMoment, mollifiedError, mul_comm _ I] at hR ⊢
  apply hR.trans
  have hfac := mul_le_mul
    (show 1 + (2 * T - 1) / (X : ℝ) ≤ 3 by linarith)
    (show 1 + Real.log (X : ℝ) ≤ 3 * Real.log T by linarith)
    (show 0 ≤ 1 + Real.log (X : ℝ) by linarith [Real.log_nonneg (show 1 ≤ (X : ℝ) by linarith)])
    (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith only [mul_le_mul_of_nonneg_left hfac hK.le]

/-- The sharp I3 input lowers the log factor uniformly, using the original
signed Cauchy observation at every zero with analytic multiplicity. -/
theorem exists_ingham_density_sharp_log_profile :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 16 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      let q := 3 * (1 - σ) / (2 - σ)
      rightInclusiveCount T σ ≤ C * T ^ q * (Real.log T) ^ (3 + q) := by
  obtain ⟨J, hJ, hR⟩ := rightCountingMoment_log_bound
  obtain ⟨C, hC, hcount⟩ := exists_ingham_density_of_right_moment_scale hJ
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ q
  have hTp := (Real.exp_pos 16).trans_le hT
  let ℓ := Real.log T
  have hℓ : 16 ≤ ℓ := by simpa [ℓ] using Real.log_le_log (Real.exp_pos 16) hT
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓp : 0 < ℓ := by linarith
  have hcmp : ℓ ≤ ℓ ^ 3 := by simpa using pow_le_pow_right₀ hℓ1 (by decide : 1 ≤ 3)
  have h := hcount T hT ℓ le_rfl hcmp (hR T hT) σ hσ
  change rightInclusiveCount T σ ≤ C * (T * ℓ ^ 2 / ℓ) ^ q * ℓ * ℓ ^ 2 at h
  rw [show T * ℓ ^ 2 / ℓ = T * ℓ by field_simp [hℓp.ne'], Real.mul_rpow hTp.le hℓp.le] at h
  refine h.trans_eq ?_
  change _ = C * T ^ q * ℓ ^ (3 + q)
  rw [Real.rpow_add hℓp, show ℓ ^ (3 : ℝ) = ℓ ^ (3 : ℕ) by norm_cast]
  ring

/-- One positive constant gives both total counting and the sharp-input
density profile at every height at least two. -/
theorem exists_ingham_density_sharp_all_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      let q := 3 * (1 - σ) / (2 - σ)
      rightInclusiveCount T σ ≤ C * min (T * Real.log T) (T ^ q * (Real.log T) ^ (3 + q)) := by
  obtain ⟨B, hB, hsharp⟩ := exists_ingham_density_sharp_log_profile
  obtain ⟨A, hA, hprev⟩ := exists_ingham_density_all_heights
  let m := (Real.log 2) ^ 4
  let F := (Ncount 0 (Real.exp 16) : ℝ) / m
  let C := max (max A B) F
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm : 0 < m := pow_pos hL _
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_left _ _)
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_left _ _)
  have hC := hA.trans_le hAC
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ q
  have hTp : 0 < T := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
  have hLp := hL.trans_le hl
  have hden : 0 < 2 - σ := by linarith [hσ.2]
  have hq : 0 ≤ q := div_nonneg (by linarith [hσ.2]) hden.le
  have hq' : q ≤ 1 := (div_le_iff₀ hden).mpr (by linarith [hσ.1])
  rw [mul_min_of_nonneg _ _ hC.le]
  refine le_min ?_ ?_
  · have ht := hprev T hT σ hσ
    exact ht.trans ((mul_le_mul_of_nonneg_left (min_le_left _ _) hA.le).trans
      (mul_le_mul_of_nonneg_right hAC (mul_nonneg hTp.le hLp.le)))
  · by_cases hr : Real.exp 16 ≤ T
    · exact (hsharp T hr σ hσ).trans (by rw [mul_assoc]; gcongr)
    · have hfinite : rightInclusiveCount T σ ≤ F * m := by
        rw [show F * m = (Ncount 0 (Real.exp 16) : ℝ) from div_mul_cancel₀ _ hm.ne']
        exact (rightInclusiveCount_monotone_height σ (le_of_not_ge hr)).trans
          (rightInclusiveCount_le_count _ _)
      have hml : m ≤ (Real.log T) ^ (3 + q) := by
        calc
          m = (Real.log 2) ^ (4 : ℝ) := by dsimp [m]; norm_cast
          _ ≤ (Real.log 2) ^ (3 + q) :=
            Real.rpow_le_rpow_of_exponent_ge hL hL' (by linarith)
          _ ≤ _ := Real.rpow_le_rpow hL.le hl (by linarith)
      exact hfinite.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) hm.le).trans
        (mul_le_mul_of_nonneg_left (hml.trans (le_mul_of_one_le_left
          (Real.rpow_nonneg hLp.le _) (Real.one_le_rpow (by linarith) hq))) hC.le))

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_density_sharp_all_heights' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_ingham_density_sharp_all_heights

end RiemannResearch.Analysis.ActualZeroOrdinate
