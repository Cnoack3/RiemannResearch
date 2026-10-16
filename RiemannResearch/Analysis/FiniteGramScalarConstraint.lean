/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A scalar constraint on the actual finite Gram projection

Source: user-provided `Q_LCM_Periods_RH_Criterion_and_Research_Agenda_2026-10-16.md`,
Section 8, for the statement and completion-of-squares proof strategy.
The actual Gram inverse is constructed from independence. Every signed mixed
term is retained in the complete norm-square remainder. No asymptotic estimate
or RH hypothesis is used.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteGramCapacity

open FiniteHilbertGram FiniteHilbertConstraints

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact completion for an arbitrary scalar source normalization. -/
theorem scalar_source_completion {v : ι → E} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) (hb : b ≠ 0) (s : ℝ) (hc : (∑ i, c i * b i) = s) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 = s ^ 2 / capacity hv b +
      ‖Fintype.linearCombination ℝ v c -
        (s / capacity hv b) • minimumVector hv b‖ ^ 2 := by
  have hp := ne_of_gt (capacity_pos hv b hb)
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, inner_synthesis_minimumVector, hc, ← capacity_eq_norm_sq]
  field_simp [hp]
  ring

/-- Signed normalization still missing after the unconstrained projection. -/
def scalarMismatch {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (f : E) (s : ℝ) : ℝ :=
  s - ∑ i, inverseCoeff hv f i * b i

/-- The actual inverse-Gram coefficient optimizer under one scalar constraint. -/
def scalarCoefficients {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (f : E) (s : ℝ) : ι → ℝ :=
  inverseCoeff hv f + (scalarMismatch hv b f s / capacity hv b) • inverseSource hv b

theorem scalarCoefficients_source {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) (f : E) (s : ℝ) :
    (∑ i, scalarCoefficients hv b f s i * b i) = s := by
  have hp := ne_of_gt (capacity_pos hv b hb)
  simp only [scalarCoefficients, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  change (∑ i, inverseCoeff hv f i * b i) +
    (scalarMismatch hv b f s / capacity hv b) * capacity hv b = s
  rw [div_mul_cancel₀ _ hp]
  unfold scalarMismatch
  ring

/-- The complete constrained value is the unconstrained error plus the
normalization penalty. This is the manuscript's formula (8.1). -/
theorem scalarCoefficients_energy {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) (f : E) (s : ℝ) :
    ‖f - Fintype.linearCombination ℝ v (scalarCoefficients hv b f s)‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i, inverseCoeff hv f i * cross v f i +
        scalarMismatch hv b f s ^ 2 / capacity hv b := by
  have hp := ne_of_gt (capacity_pos hv b hb)
  rw [residual_completion hv f, residual_schur_value]
  have hd : scalarCoefficients hv b f s - inverseCoeff hv f =
      (scalarMismatch hv b f s / capacity hv b) • inverseSource hv b := by
    unfold scalarCoefficients
    abel
  rw [hd, map_smul]
  change _ + ‖(scalarMismatch hv b f s / capacity hv b) • minimumVector hv b‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← capacity_eq_norm_sq]
  field_simp [hp]

/-- Exact constrained completion: the only omitted quantity in a lower bound
would be this nonnegative full synthesis norm square. -/
theorem scalarCoefficients_completion {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) (f : E) (s : ℝ) (c : ι → ℝ)
    (hc : (∑ i, c i * b i) = s) :
    ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (scalarCoefficients hv b f s)‖ ^ 2 +
        ‖Fintype.linearCombination ℝ v (c - scalarCoefficients hv b f s)‖ ^ 2 := by
  have hd : (∑ i, (c - inverseCoeff hv f) i * b i) = scalarMismatch hv b f s := by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hc, scalarMismatch]
  have he := scalar_source_completion hv b (c - inverseCoeff hv f) hb
    (scalarMismatch hv b f s) hd
  have hrem : Fintype.linearCombination ℝ v (c - inverseCoeff hv f) -
      (scalarMismatch hv b f s / capacity hv b) • minimumVector hv b =
      Fintype.linearCombination ℝ v (c - scalarCoefficients hv b f s) := by
    unfold scalarCoefficients minimumVector inverseSource
    rw [map_sub, map_sub, map_add, map_smul]
    abel
  rw [hrem] at he
  rw [residual_completion hv f c, he, scalarCoefficients_energy hv b hb f s,
    residual_schur_value]
  ring

theorem scalarCoefficients_isLeast {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) (f : E) (s : ℝ) :
    IsLeast {e : ℝ | ∃ c : ι → ℝ, (∑ i, c i * b i) = s ∧
      ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 = e}
      (‖f - Fintype.linearCombination ℝ v (scalarCoefficients hv b f s)‖ ^ 2) := by
  constructor
  · exact ⟨scalarCoefficients hv b f s, scalarCoefficients_source hv b hb f s, rfl⟩
  · rintro e ⟨c, hc, rfl⟩
    rw [scalarCoefficients_completion hv b hb f s c hc]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem scalarCoefficients_unique {v : ι → E} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) (f : E) (s : ℝ) (c : ι → ℝ)
    (hc : (∑ i, c i * b i) = s)
    (he : ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (scalarCoefficients hv b f s)‖ ^ 2) :
    c = scalarCoefficients hv b f s := by
  have ht := scalarCoefficients_completion hv b hb f s c hc
  have hz : ‖Fintype.linearCombination ℝ v (c - scalarCoefficients hv b f s)‖ ^ 2 = 0 := by
    linarith
  have hz' := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hcoeff : c - scalarCoefficients hv b f s = 0 := by
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using hz'
  exact sub_eq_zero.mp hcoeff

end RiemannResearch.Analysis.FiniteGramCapacity
