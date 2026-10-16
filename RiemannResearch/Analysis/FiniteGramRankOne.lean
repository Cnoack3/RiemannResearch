/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramScalarConstraint
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rank-one head removal in a scalar constrained Gram problem

Source: user-provided argument, 16 October 2026, for the rank-one head
decomposition and capacity identities. The simultaneous source update and
optimizer identities below keep all signed terms. Both Gram inverses are
constructed from actual linear independence; no asymptotic bound is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCapacity
open FiniteHilbertGram

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {v : ι → E} {t : ι → F}

theorem inverseSource_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j)) :
    inverseSource hv b = (1 / (1 + a * capacity ht b)) • inverseSource ht b := by
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  apply gram_injective hv
  funext i
  rw [inverseSource_normal, hrel]
  have hsum : (∑ j, ((1 / (1 + a * capacity ht b)) • inverseSource ht b) j * b j) =
      (1 / (1 + a * capacity ht b)) * capacity ht b := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rfl
  rw [hsum, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, inverseSource_normal]
  field_simp [hden]

theorem capacity_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j)) :
    capacity hv b = capacity ht b / (1 + a * capacity ht b) := by
  unfold capacity
  rw [inverseSource_rank_one hv ht b a ha hrel]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  unfold capacity
  ring

theorem inverse_capacity_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (hb : b ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j)) :
    1 / capacity hv b = a + 1 / capacity ht b := by
  have hc := ne_of_gt (capacity_pos ht b hb)
  rw [capacity_rank_one hv ht b a ha hrel]
  field_simp [hc]
  ring

/-- Sherman--Morrison on every source, hence an identity of actual inverse operators. -/
theorem inverseSource_rank_one_apply (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b y : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j)) :
    inverseSource hv y = inverseSource ht y -
      (a * (∑ j, inverseSource ht y j * b j) / (1 + a * capacity ht b)) •
        inverseSource ht b := by
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  apply gram_injective hv
  funext i
  rw [inverseSource_normal, hrel]
  have hsum : (∑ j, (inverseSource ht y -
        (a * (∑ k, inverseSource ht y k * b k) / (1 + a * capacity ht b)) •
          inverseSource ht b) j * b j) =
      (∑ j, inverseSource ht y j * b j) -
        (a * (∑ k, inverseSource ht y k * b k) / (1 + a * capacity ht b)) *
          capacity ht b := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rfl
  rw [hsum, map_sub, map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inverseSource_normal]
  field_simp [hden]
  ring

/-- The unconstrained coefficients change because the source changes as well. -/
theorem inverseCoeff_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j))
    (f : E) (g : F) (s : ℝ)
    (hcross : ∀ i, cross v f i = cross t g i + a * s * b i) :
    inverseCoeff hv f = inverseCoeff ht g +
      (a * scalarMismatch ht b g s / (1 + a * capacity ht b)) • inverseSource ht b := by
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  apply gram_injective hv
  funext i
  change inner ℝ (v i) (Fintype.linearCombination ℝ v (inverseCoeff hv f)) = _
  rw [inverseCoeff_normal, hcross]
  rw [hrel]
  have hsum : (∑ j, (inverseCoeff ht g +
        (a * scalarMismatch ht b g s / (1 + a * capacity ht b)) • inverseSource ht b) j * b j) =
      (∑ j, inverseCoeff ht g j * b j) +
        (a * scalarMismatch ht b g s / (1 + a * capacity ht b)) * capacity ht b := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rfl
  rw [hsum, map_add, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, inverseSource_normal]
  rw [show gram t (inverseCoeff ht g) i = cross t g i from inverseCoeff_normal ht g i]
  unfold scalarMismatch
  field_simp [hden]
  ring

theorem scalarMismatch_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j))
    (f : E) (g : F) (s : ℝ)
    (hcross : ∀ i, cross v f i = cross t g i + a * s * b i) :
    scalarMismatch hv b f s =
      scalarMismatch ht b g s / (1 + a * capacity ht b) := by
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  unfold scalarMismatch
  rw [inverseCoeff_rank_one hv ht b a ha hrel f g s hcross]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  change s - ((∑ i, inverseCoeff ht g i * b i) +
    (a * scalarMismatch ht b g s / (1 + a * capacity ht b)) * capacity ht b) = _
  unfold scalarMismatch
  field_simp [hden]
  ring

/-- Removing a common head changes neither the constrained coefficient vector
nor any of its signed components. -/
theorem scalarCoefficients_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (hb : b ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j))
    (f : E) (g : F) (s : ℝ)
    (hcross : ∀ i, cross v f i = cross t g i + a * s * b i) :
    scalarCoefficients hv b f s = scalarCoefficients ht b g s := by
  have hc := ne_of_gt (capacity_pos ht b hb)
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  unfold scalarCoefficients
  rw [inverseCoeff_rank_one hv ht b a ha hrel f g s hcross,
    scalarMismatch_rank_one hv ht b a ha hrel f g s hcross,
    capacity_rank_one hv ht b a ha hrel, inverseSource_rank_one hv ht b a ha hrel]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hc, hden]
  ring

/-- The apparent full normalization penalty decreases exactly by this factor. -/
theorem scalarPenalty_rank_one (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (hb : b ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j))
    (f : E) (g : F) (s : ℝ)
    (hcross : ∀ i, cross v f i = cross t g i + a * s * b i) :
    scalarMismatch hv b f s ^ 2 / capacity hv b =
      scalarMismatch ht b g s ^ 2 /
        (capacity ht b * (1 + a * capacity ht b)) := by
  have hc := ne_of_gt (capacity_pos ht b hb)
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  rw [scalarMismatch_rank_one hv ht b a ha hrel f g s hcross,
    capacity_rank_one hv ht b a ha hrel]
  field_simp [hc, hden]

/-- The source update transfers precisely this much error into the unconstrained
residual. Together with scalarPenalty_rank_one, the constrained value is unchanged. -/
theorem residual_rank_one_value (hv : LinearIndependent ℝ v)
    (ht : LinearIndependent ℝ t) (b : ι → ℝ) (hb : b ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (hrel : ∀ c i, gram v c i = gram t c i + a * b i * (∑ j, c j * b j))
    (f : E) (g : F) (s : ℝ)
    (hcross : ∀ i, cross v f i = cross t g i + a * s * b i)
    (henergy : ∀ c, ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖g - Fintype.linearCombination ℝ t c‖ ^ 2 + a * (s - ∑ i, c i * b i) ^ 2) :
    ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 =
      ‖g - Fintype.linearCombination ℝ t (inverseCoeff ht g)‖ ^ 2 +
        a * scalarMismatch ht b g s ^ 2 / (1 + a * capacity ht b) := by
  have hc := ne_of_gt (capacity_pos ht b hb)
  have hden : 1 + a * capacity ht b ≠ 0 := by
    have := mul_nonneg ha (capacity_nonneg ht b)
    linarith
  have he := henergy (scalarCoefficients hv b f s)
  rw [scalarCoefficients_source hv b hb f s, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] at he
  have he' : ‖f - Fintype.linearCombination ℝ v (scalarCoefficients hv b f s)‖ ^ 2 =
      ‖g - Fintype.linearCombination ℝ t (scalarCoefficients ht b g s)‖ ^ 2 := by
    calc
      _ = ‖g - Fintype.linearCombination ℝ t (scalarCoefficients hv b f s)‖ ^ 2 := he
      _ = _ := by rw [scalarCoefficients_rank_one hv ht b hb a ha hrel f g s hcross]
  rw [scalarCoefficients_energy hv b hb f s, scalarCoefficients_energy ht b hb g s,
    ← residual_schur_value hv f, ← residual_schur_value ht g,
    scalarPenalty_rank_one hv ht b hb a ha hrel f g s hcross] at he'
  calc
    _ = ‖g - Fintype.linearCombination ℝ t (inverseCoeff ht g)‖ ^ 2 +
        scalarMismatch ht b g s ^ 2 / capacity ht b -
        scalarMismatch ht b g s ^ 2 / (capacity ht b * (1 + a * capacity ht b)) := by
      linarith only [he']
    _ = _ := by
      have hden' : 1 + capacity ht b * a ≠ 0 := by simpa only [mul_comm] using hden
      field_simp [hc, hden, hden']
      ring

end RiemannResearch.Analysis.FiniteGramCapacity
