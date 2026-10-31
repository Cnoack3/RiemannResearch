/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arbitrarily small perturbations avoiding finitely many zero coefficients
Source: the user's squarefree full-support request, 30 October 2026.
The exact signed energy expansion precedes its arithmetic applications.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FullSupportPerturbation
theorem exists_coefficient_window {ι : Type*} (s : Finset ι)
    (b β : ι → ℝ) (hβ : ∀ i ∈ s, β i ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η →
      ∀ i ∈ s, b i + t * β i ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨η, hη, hwin⟩ := ih (fun i hi => hβ i (Finset.mem_insert_of_mem hi))
      by_cases hb : b a = 0
      · refine ⟨η, hη, ?_⟩
        intro t ht htη i hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          simpa only [hb, zero_add] using
            mul_ne_zero (ne_of_gt ht) (hβ a (Finset.mem_insert_self a s))
        · exact hwin t ht htη i hi
      · have hab : 0 < |b a| := abs_pos.mpr hb
        have hden : 0 < |β a| + 1 := by positivity
        refine ⟨min η (|b a| / (|β a| + 1)), lt_min hη (div_pos hab hden), ?_⟩
        intro t ht htη i hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          have hsmall : t * (|β a| + 1) < |b a| :=
            (lt_div_iff₀ hden).mp (lt_min_iff.mp htη).2
          intro hz
          have he : b a = -(t * β a) := by linarith
          have heabs := congrArg abs he
          rw [abs_neg, abs_mul, abs_of_pos ht] at heabs
          nlinarith
        · exact hwin t ht (lt_min_iff.mp htη).1 i hi

theorem exists_small_step {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (b β : ι → ℝ) (hβ : ∀ i ∈ s, β i ≠ 0)
    (g : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ‖t • g‖ < ε ∧ ∀ i ∈ s, b i + t * β i ≠ 0 := by
  obtain ⟨η, hη, hwin⟩ := exists_coefficient_window s b β hβ
  let t := min (η / 2) (ε / (2 * (1 + ‖g‖)))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htη : t < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsmall : t * (2 * (1 + ‖g‖)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨t, ht, ?_, hwin t ht htη⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith [norm_nonneg g]

theorem perturbation_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : E) (t : ℝ) :
    ‖f + t • g‖ ^ 2 = ‖f‖ ^ 2 + 2 * t * inner ℝ f g + t ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring
end RiemannResearch.Analysis.FullSupportPerturbation
