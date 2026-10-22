/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramAffineMinimum

/-!
# Exact capacity increments under finite-family enlargement

Source: the Pareto capacity handoff, Section 11, motivates tracking the gain
under conductor enlargement. The identities use the actual Gram form and allow
singular systems, repeated vectors, and noninjective maps of the old family.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normal_synthesis_energy (v : ι → H) (z : ι → ℝ)
    (hz : gram v z = fun _ => 1) :
    ‖Fintype.linearCombination ℝ v z‖ ^ 2 = ∑ i, z i := by
  rw [gram_quadratic, hz]
  simp only [mul_one]

theorem normal_synthesis_inner_of_family_map
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) :
    inner ℝ (Fintype.linearCombination ℝ v z)
      (Fintype.linearCombination ℝ w u) = ∑ i, z i := by
  rw [inner_synthesis_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i]
  change z i * gram w u (e i) = z i
  rw [hu]
  simp only [mul_one]

/-- Capacity gain is precisely the squared change in the synthesized normal
vector. This gives an additive identity even for singular Gram systems. -/
theorem normal_mass_increment_of_family_map
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) :
    (∑ j, u j) - (∑ i, z i) =
      ‖Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z‖ ^ 2 := by
  rw [norm_sub_sq_real, normal_synthesis_energy w u hu,
    normal_synthesis_energy v z hz, real_inner_comm,
    normal_synthesis_inner_of_family_map v w z u hu e he]
  ring

theorem normal_mass_eq_iff_synthesis_eq
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) :
    (∑ j, u j) = (∑ i, z i) ↔
      Fintype.linearCombination ℝ w u = Fintype.linearCombination ℝ v z := by
  have hgain := normal_mass_increment_of_family_map v w z u hz hu e he
  constructor
  · intro hmass
    have hs : ‖Fintype.linearCombination ℝ w u -
        Fintype.linearCombination ℝ v z‖ ^ 2 = 0 := by
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))
  · intro hvec
    rw [hvec, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hgain
    linarith

/-- Enlargement has no gain exactly when the old normal vector already
satisfies every normal equation imposed by the larger family. -/
theorem normal_mass_eq_iff_new_normal_equations
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) :
    (∑ j, u j) = (∑ i, z i) ↔
      ∀ j, inner ℝ (w j) (Fintype.linearCombination ℝ v z) = 1 := by
  constructor
  · intro hmass
    have hvec := (normal_mass_eq_iff_synthesis_eq v w z u hz hu e he).mp hmass
    intro j
    rw [← hvec]
    exact congrFun hu j
  · intro hnew
    have hcross := normal_synthesis_inner_of_family_map v w z u hu e he
    have hreverse : inner ℝ (Fintype.linearCombination ℝ w u)
        (Fintype.linearCombination ℝ v z) = ∑ j, u j := by
      rw [inner_synthesis_left]
      simp only [hnew, mul_one]
    rw [real_inner_comm] at hreverse
    linarith

/-- Each failed new normal equation supplies a signed quantitative lower
bound for the capacity gain; the source is not replaced by its unsigned parts. -/
theorem normal_equation_defect_sq_le_gain
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) (j : κ) :
    (1 - inner ℝ (w j) (Fintype.linearCombination ℝ v z)) ^ 2 ≤
      ‖w j‖ ^ 2 * ((∑ j, u j) - (∑ i, z i)) := by
  have h := abs_real_inner_le_norm (w j)
    (Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z)
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ (w j)
    (Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z))) h
  have hj : inner ℝ (w j) (Fintype.linearCombination ℝ w u) = 1 := congrFun hu j
  simpa only [← pow_two, sq_abs, mul_pow, inner_sub_right, hj,
    ← normal_mass_increment_of_family_map v w z u hz hu e he] using hs

theorem normal_increment_orthogonal_old_synthesis
    (v : ι → H) (w : κ → H) (z c : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) :
    inner ℝ (Fintype.linearCombination ℝ v c)
      (Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z) = 0 := by
  rw [inner_synthesis_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hnew : inner ℝ (v i) (Fintype.linearCombination ℝ w u) = 1 := by
    rw [he i]
    exact congrFun hu (e i)
  have hold : inner ℝ (v i) (Fintype.linearCombination ℝ v z) = 1 := congrFun hz i
  rw [inner_sub_right, hnew, hold, sub_self, mul_zero]

/-- Subtracting any old-span prediction from the new vector leaves the signed
source unchanged and improves the available Cauchy--Schwarz denominator. -/
theorem normal_equation_defect_sq_le_screened_gain
    (v : ι → H) (w : κ → H) (z c : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) (j : κ) :
    (1 - inner ℝ (w j) (Fintype.linearCombination ℝ v z)) ^ 2 ≤
      ‖w j - Fintype.linearCombination ℝ v c‖ ^ 2 *
        ((∑ j, u j) - (∑ i, z i)) := by
  have h := abs_real_inner_le_norm (w j - Fintype.linearCombination ℝ v c)
    (Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z)
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ
    (w j - Fintype.linearCombination ℝ v c)
    (Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z))) h
  have hsource : inner ℝ (w j - Fintype.linearCombination ℝ v c)
      (Fintype.linearCombination ℝ w u - Fintype.linearCombination ℝ v z) =
      1 - inner ℝ (w j) (Fintype.linearCombination ℝ v z) := by
    rw [inner_sub_left, normal_increment_orthogonal_old_synthesis v w z c u hz hu e he,
      sub_zero, inner_sub_right]
    have hj : inner ℝ (w j) (Fintype.linearCombination ℝ w u) = 1 := congrFun hu j
    rw [hj]
  simpa only [← pow_two, sq_abs, mul_pow, hsource,
    ← normal_mass_increment_of_family_map v w z u hz hu e he] using hs

end RiemannResearch.Analysis.FiniteHilbertGram
