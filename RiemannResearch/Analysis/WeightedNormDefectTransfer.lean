/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedScalarEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Divergence transfer from a positive cofinal prefix-norm saving

Source: independently developed consequence of the finite-head/tail pairing
decay in WeightedScalarEnergy. No mathematical priority is asserted.

A divergent weighted model and a fixed positive norm saving over its COMPLETE
signed discrepancy force nonsummability of the actual energy. Relative error
energy may tend to one. The proof retains the exact cross term before using
normalized pairing decay. The concrete RH consumer is
ParetoMovingRemainderTransfer.riemannHypothesis_of_moving_norm_defect.
Arithmetic model divergence and the positive cofinal saving remain explicit
hypotheses; this generic theorem does not furnish them.
-/


open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.WeightedScalarEnergy

/-- A fixed positive saving in prefix norms is sufficient; the allowed relative
saving may vanish. Model divergence and the complete error remain explicit. -/

theorem actual_square_not_summable_of_cofinal_norm_defect
    (w g m : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hdiv : Tendsto (fun N => square (Finset.range N) w m) atTop atTop)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ N0 : ℕ, ∃ N ≥ N0,
      δ ≤ Real.sqrt (square (Finset.range N) w m) -
        Real.sqrt (square (Finset.range N) w (fun j => g j-m j))) :
    ¬ Summable (fun j => w j * (g j)^2) := by
  intro hg
  have hzero := normalized_product_tendsto_zero w m g hw hg hdiv
  have hsmall : ∀ᶠ N in atTop,
      (product (Finset.range N) w m g)^2 / square (Finset.range N) w m < δ^2/4 :=
    hzero.eventually (gt_mem_nhds (by positivity : 0 < δ^2/4))
  obtain ⟨N0,hN0⟩ := eventually_atTop.1 hsmall
  obtain ⟨N,hN,hgapN⟩ := hgap N0
  let M := square (Finset.range N) w m
  let T := square (Finset.range N) w (fun j => g j-m j)
  let A := square (Finset.range N) w g
  let X := product (Finset.range N) w m g
  have hM : 0 ≤ M := square_nonneg _ _ _ (fun j _ => hw j)
  have hT : 0 ≤ T := square_nonneg _ _ _ (fun j _ => hw j)
  have hA : 0 ≤ A := square_nonneg _ _ _ (fun j _ => hw j)
  have hMsq : (Real.sqrt M)^2=M := Real.sq_sqrt hM
  have hTsq : (Real.sqrt T)^2=T := Real.sq_sqrt hT
  have he : M-T=2*X-A := by
    dsimp [M,T,A,X]
    have ht := square_sub (Finset.range N) w m g 1
    simp only [one_mul, one_pow, mul_one] at ht
    rw [ht]
    ring
  change δ ≤ Real.sqrt M-Real.sqrt T at hgapN
  have hspos : 0 < Real.sqrt M := by
    nlinarith [Real.sqrt_nonneg T]
  have hMpos : 0 < M := Real.sqrt_pos.1 hspos
  have hmul := mul_le_mul_of_nonneg_right hgapN
    (add_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg T))
  have hlin : δ * Real.sqrt M ≤ 2 * X := by
    nlinarith [mul_nonneg hδ.le (Real.sqrt_nonneg T)]
  have hX : 0 ≤ 2*X := (mul_nonneg hδ.le (Real.sqrt_nonneg M)).trans hlin
  have hsq := (sq_le_sq₀ (mul_nonneg hδ.le (Real.sqrt_nonneg M)) hX).2 hlin
  have hbound : δ^2/4 ≤ X^2/M := by
    apply (le_div_iff₀ hMpos).2
    nlinarith [hsq]
  have hnsmall : X^2/M < δ^2/4 := hN0 N hN
  exact (not_lt_of_ge hbound) hnsmall
end RiemannResearch.Analysis.WeightedScalarEnergy
