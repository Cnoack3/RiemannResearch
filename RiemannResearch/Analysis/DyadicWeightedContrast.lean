/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedScalarEnergy

/-!
# Exact dyadic grouping and weighted contrast perturbations

Source: elementary finite dyadic telescoping and the finite weighted Gram
inequality. These support the statements and proof strategy.
The concrete consumer is RH/ParetoFirstSitePrimeContrastPerturbations.lean.
No row independence or arithmetic divergence estimate is assumed.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.DyadicWeightedContrast
theorem dyadic_block_sum_eq (a : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2^j), a (2^j+i)) =
      (∑ n ∈ Finset.range (2^J), a n) - a 0 := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hp : (2:ℕ)^(J+1) = 2^J+2^J := by rw [pow_succ]; omega
    rw [Finset.sum_range_succ, ih, hp, Finset.sum_range_add]
    ring

theorem dyadic_block_summable_of_nonneg (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Summable (fun j => ∑ i ∈ Finset.range (2^j), a (2^j+i)) := by
  apply summable_of_sum_range_le
    (fun j => Finset.sum_nonneg (fun i _ => ha (2^j+i)))
  intro J
  rw [dyadic_block_sum_eq]
  exact (sub_le_self _ (ha 0)).trans
    (hs.sum_le_tsum (Finset.range (2^J)) (fun n _ => ha n))
/-- Arbitrary changing finite tests cannot accumulate infinite normalized
pairing energy against a weighted square-summable signed sequence. -/
theorem dyadic_pairing_energy_summable (w e : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (he : Summable (fun n => w n * (e n)^2)) :
    Summable (fun j =>
      (RiemannResearch.Analysis.WeightedScalarEnergy.product (Finset.range (2^j))
        (fun i => w (2^j+i)) (c j) (fun i => e (2^j+i)))^2 /
      RiemannResearch.Analysis.WeightedScalarEnergy.square (Finset.range (2^j))
        (fun i => w (2^j+i)) (c j)) := by
  open RiemannResearch.Analysis.WeightedScalarEnergy in
  have hb := dyadic_block_summable_of_nonneg (fun n => w n * (e n)^2)
    (fun n => mul_nonneg (hw n) (sq_nonneg _)) he
  apply Summable.of_nonneg_of_le
    (fun j => div_nonneg (sq_nonneg _)
      (RiemannResearch.Analysis.WeightedScalarEnergy.square_nonneg _ _ _
        (fun i _ => hw (2^j+i)))) _ hb
  intro j
  let wj := fun i => w (2^j+i)
  let ej := fun i => e (2^j+i)
  have hwj : ∀ i ∈ Finset.range (2^j), 0 ≤ wj i := fun i _ => hw (2^j+i)
  change (RiemannResearch.Analysis.WeightedScalarEnergy.product
      (Finset.range (2^j)) wj (c j) ej)^2 /
    RiemannResearch.Analysis.WeightedScalarEnergy.square
      (Finset.range (2^j)) wj (c j) ≤
    RiemannResearch.Analysis.WeightedScalarEnergy.square
      (Finset.range (2^j)) wj ej
  by_cases hD : RiemannResearch.Analysis.WeightedScalarEnergy.square
      (Finset.range (2^j)) wj (c j) = 0
  · simpa [hD] using RiemannResearch.Analysis.WeightedScalarEnergy.square_nonneg
      (Finset.range (2^j)) wj ej hwj
  · have hp : 0 < RiemannResearch.Analysis.WeightedScalarEnergy.square
        (Finset.range (2^j)) wj (c j) :=
      lt_of_le_of_ne (RiemannResearch.Analysis.WeightedScalarEnergy.square_nonneg
        _ _ _ hwj) (Ne.symm hD)
    apply (div_le_iff₀ hp).mpr
    simpa only [mul_comm] using RiemannResearch.Analysis.WeightedScalarEnergy.gram_nonneg
      (Finset.range (2^j)) wj (c j) ej hwj

end RiemannResearch.Analysis.DyadicWeightedContrast
