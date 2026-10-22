/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.Analysis.WeakConvergenceDenseTests
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Bounded combinations with escaping conductors are weakly null

Source: user-provided `Squarefree_Infinite_CRT_Continuation_2026-10-16`,
Section 4.2, for the statement and exact linear-head energy argument.
The number and signs of the coefficients are unrestricted. The full Q norm
is the bound, and squarefreeness is unnecessary for this obstruction.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoHilbert
open ArithmeticCumulative ZetaTwoProbability

/-- Finite combinations whose every conductor exceeds H. -/
def qConductorTailSpan (H : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ d : ℕ, H < d ∧ f = qResidue d}

/-- Before the first possible wrap, every such combination is exactly linear. -/
theorem qConductorTailSpan_head (H : ℕ) (hH : 1 ≤ H)
    (f : QHilbert) (hf : f ∈ qConductorTailSpan H)
    (k : ℕ) (hk : k ≤ H) : qSequence f k = (k : ℝ) * qSequence f 1 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨d, hd, rfl⟩ := hf
      simp only [qSequence_qResidue, residueFraction,
        Nat.mod_eq_of_lt (show k < d by omega),
        Nat.mod_eq_of_lt (show 1 < d by omega), Nat.cast_one]
      ring
  | zero => cases k <;> simp [qSequence]
  | add f g hf hg ihf ihg =>
      change qSequenceLinear (f + g) k = (k : ℝ) * qSequenceLinear (f + g) 1
      simp only [map_add, Pi.add_apply]
      change qSequence f k + qSequence g k =
        (k : ℝ) * (qSequence f 1 + qSequence g 1)
      rw [ihf, ihg]
      ring
  | smul c f hf ih =>
      change qSequenceLinear (c • f) k = (k : ℝ) * qSequenceLinear (c • f) 1
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      change c * qSequence f k = (k : ℝ) * (c * qSequence f 1)
      rw [ih]
      ring

/-- Exact energy of a linear physical head, before comparison with the full norm. -/
theorem qLinearHead_energy_exact (f : QHilbert) (H : ℕ)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence f k = (k : ℝ) * qSequence f 1) :
    (∑ k ∈ Finset.Icc 1 H, positiveQWeight k * (qSequence f k) ^ 2) =
      (H : ℝ) * (qSequence f 1) ^ 2 / zetaTwo := by
  have he (k : ℕ) (hk : k ∈ Finset.Icc 1 H) :
      positiveQWeight k * (qSequence f k) ^ 2 = (qSequence f 1) ^ 2 / zetaTwo := by
    have hk' := Finset.mem_Icc.mp hk
    rw [hh k (by omega) hk'.2]
    unfold positiveQWeight
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    field_simp [hkR]
  simp_rw [Finset.sum_congr rfl he]
  simp [Nat.card_Icc, mul_div_assoc]

theorem qLinearHead_energy_le (f : QHilbert) (H : ℕ)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence f k = (k : ℝ) * qSequence f 1) :
    (H : ℝ) * (qSequence f 1) ^ 2 / zetaTwo ≤ ‖f‖ ^ 2 := by
  rw [← qLinearHead_energy_exact f H hh, qNorm_weighted_sq]
  exact (qSequence_square_summable f).sum_le_tsum _
    (fun k _ => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))

/-- A bound on the complete Q norm forces the slopes of cofinal linear heads to zero. -/
theorem qLinearHead_slope_tendsto_zero
    (F : ℕ → QHilbert) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ j, ‖F j‖ ≤ C)
    (hh : ∀ j k, 0 < k → k ≤ H j →
      qSequence (F j) k = (k : ℝ) * qSequence (F j) 1) :
    Tendsto (fun j => qSequence (F j) 1) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => (qSequence (F j) 1) ^ 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => zetaTwo * C ^ 2 / (H j : ℝ)) atTop (𝓝 0) := by
      have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hH).const_mul
        (zetaTwo * C ^ 2)
      simpa only [Function.comp_def, mul_zero, mul_one_div] using h
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) _ ht
    filter_upwards [hH.eventually (eventually_gt_atTop 0)] with j hj
    have he := qLinearHead_energy_le (F j) (H j) (hh j)
    have hn : ‖F j‖ ^ 2 ≤ C ^ 2 := by nlinarith [hb j, norm_nonneg (F j)]
    have hmul : (H j : ℝ) * (qSequence (F j) 1) ^ 2 ≤ zetaTwo * C ^ 2 := by
      have he' := (div_le_iff₀ zetaTwo_pos).mp (he.trans hn)
      nlinarith
    apply (le_div_iff₀ (show (0 : ℝ) < H j by exact_mod_cast hj)).mpr
    nlinarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, sub_zero, Real.sqrt_sq_eq_abs, Real.sqrt_zero,
    Real.norm_eq_abs] using h

/-- All continuous Hilbert pairings vanish for bounded legal combinations
whose entire conductor support escapes. This includes the squarefree subclass. -/
theorem qConductorTailSpan_weak_tendsto_zero
    (F : ℕ → QHilbert) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hpos : ∀ j, 1 ≤ H j) (hmem : ∀ j, F j ∈ qConductorTailSpan (H j))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ j, ‖F j‖ ≤ C) (x : QHilbert) :
    Tendsto (fun j => inner ℝ x (F j)) atTop (𝓝 0) := by
  have hh := fun j k (_ : 0 < k) (hk : k ≤ H j) =>
    qConductorTailSpan_head (H j) (hpos j) (F j) (hmem j) k hk
  have hs := qLinearHead_slope_tendsto_zero F H hH C hC hb hh
  have hp (k : ℕ) : Tendsto (fun j => qSequence (F j) k) atTop (𝓝 0) := by
    have ht := hs.const_mul (k : ℝ)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hH.eventually (eventually_ge_atTop k)] with j hj
    exact (qConductorTailSpan_head (H j) (hpos j) (F j) (hmem j) k hj).symm
  apply RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span hC
    (Filter.Eventually.of_forall hb) _
    (by rw [QExactHeadAverages.qPoint_span_dense]; trivial)
  rintro y ⟨n, rfl⟩
  simpa only [qPoint_inner, mul_zero] using (hp (n + 1)).const_mul (qWeight n)

end RiemannResearch.RH.ZetaTwoHilbert
