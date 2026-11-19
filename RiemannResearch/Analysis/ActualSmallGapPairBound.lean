/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriSmallGapCriterion
import RiemannResearch.Analysis.MontgomeryFormFactor

/-!
# A diagonal upper bound for the pair sum after small-gap deletion

This is the finite comparison in the proof of Lamzouri's Theorem 3.3.
The surviving occurrences are computed from the actual chronological cutoff.
The Fourier-side test may be any real function with unit diagonal mass and
nonpositive values outside the specified gap scale.
-/

noncomputable section

open Zeta23 MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def unmarkedGapIndices (gapLimit T : ℝ) : Finset ℕ :=
  Finset.range (Ncount 0 T) \ smallGapEndpoints gapLimit T

def gapCoordinate (T : ℝ) (i j : ℕ) : ℝ :=
  (cutoffOrdinate T i - cutoffOrdinate T j) * Real.log T / (2 * Real.pi)

def pairWeight (T : ℝ) (i j : ℕ) : ℝ :=
  MontgomeryPoisson.cauchyWeight (cutoffOrdinate T i - cutoffOrdinate T j)

theorem gapCoordinate_swap (T : ℝ) (i j : ℕ) :
    gapCoordinate T j i = -gapCoordinate T i j := by
  unfold gapCoordinate
  ring

theorem gapCoordinate_separated {gapLimit T : ℝ} {i j : ℕ}
    (hlog : 0 ≤ Real.log T) (hi : i ∈ unmarkedGapIndices gapLimit T)
    (hj : j ∈ unmarkedGapIndices gapLimit T) (hne : i ≠ j) :
    gapLimit < |gapCoordinate T i j| := by
  have hp : 0 < 2 * Real.pi := by positivity
  have go {a b : ℕ} (hab : a < b) (ha : a ∈ unmarkedGapIndices gapLimit T)
      (hb : b ∈ unmarkedGapIndices gapLimit T) : gapLimit < gapCoordinate T b a := by
    have sep := separation_of_unmarked_index hlog hab
      (Finset.mem_range.mp (Finset.mem_sdiff.mp hb).1) (Finset.mem_sdiff.mp ha).2
    apply (lt_div_iff₀ hp).2
    linarith only [sep]
  rcases lt_or_gt_of_ne hne with h | h
  · have hs := go h hi hj
    rw [gapCoordinate_swap] at hs
    exact hs.trans_le (neg_le_abs _)
  · exact (go h hj hi).trans_le (le_abs_self _)

/-- Unnormalized finite sum on the surviving real ordinates. -/
def unmarkedGapPairSum (gapLimit T : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑ i ∈ unmarkedGapIndices gapLimit T, ∑ j ∈ unmarkedGapIndices gapLimit T,
    pairWeight T i j * F (gapCoordinate T i j)

/-- Fourier-side separation suppresses every off-diagonal contribution. -/
theorem unmarkedGapPairSum_le_survivors {gapLimit T : ℝ} {F : ℝ → ℝ}
    (hlog : 0 ≤ Real.log T) (hF0 : F 0 = 1)
    (houtside : ∀ u, gapLimit < |u| → F u ≤ 0) :
    unmarkedGapPairSum gapLimit T F ≤ ((unmarkedGapIndices gapLimit T).card : ℝ) := by
  classical
  let S := unmarkedGapIndices gapLimit T
  have hrow (i : ℕ) (hi : i ∈ S) :
      ∑ j ∈ S, pairWeight T i j * F (gapCoordinate T i j) ≤ 1 := by
    calc
      _ ≤ ∑ j ∈ S, (if i = j then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · subst j
          norm_num [pairWeight, MontgomeryPoisson.cauchyWeight, gapCoordinate, hF0]
        · simp only [if_neg hij]
          have hw : 0 ≤ pairWeight T i j := by
            unfold pairWeight MontgomeryPoisson.cauchyWeight
            positivity
          exact mul_nonpos_of_nonneg_of_nonpos hw
            (houtside _ (gapCoordinate_separated hlog hi hj hij))
      _ = 1 := by simp [hi]
  calc
    unmarkedGapPairSum gapLimit T F ≤ ∑ i ∈ S, (1 : ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp [S]

/-- The bound remains valid with the denominator counting all zero copies. -/
theorem normalized_unmarkedGapPairSum_le_one {gapLimit T : ℝ} {F : ℝ → ℝ}
    (hlog : 0 ≤ Real.log T) (hF0 : F 0 = 1)
    (houtside : ∀ u, gapLimit < |u| → F u ≤ 0) :
    unmarkedGapPairSum gapLimit T F / (Ncount 0 T : ℝ) ≤ 1 := by
  by_cases hz : Ncount 0 T = 0
  · simp [hz]
  · have hN : (0 : ℝ) < (Ncount 0 T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    apply (div_le_one hN).2
    apply (unmarkedGapPairSum_le_survivors hlog hF0 houtside).trans
    have hc : (unmarkedGapIndices gapLimit T).card ≤ Ncount 0 T := by
      calc
        _ ≤ (Finset.range (Ncount 0 T)).card := Finset.card_le_card Finset.sdiff_subset
        _ = _ := Finset.card_range _
    exact_mod_cast hc

/-- The real form factor for the finite family of surviving ordinates. -/
def unmarkedFormFactor (gapLimit T α : ℝ) : ℝ :=
  (MontgomeryFormFactor.pairSum
    (fun i : unmarkedGapIndices gapLimit T => cutoffOrdinate T i) (α * Real.log T)).re

theorem unmarkedFormFactor_nonneg (gapLimit T α : ℝ) : 0 ≤ unmarkedFormFactor gapLimit T α :=
  MontgomeryFormFactor.pairSum_nonneg _ _

private theorem unmarked_integrand (gapLimit T : ℝ) (f : ℝ → ℝ) (α : ℝ) :
    f α * unmarkedFormFactor gapLimit T α =
      ∑ i ∈ unmarkedGapIndices gapLimit T, ∑ j ∈ unmarkedGapIndices gapLimit T,
        pairWeight T i j *
          (f α * Real.cos (2 * Real.pi * α * gapCoordinate T i j)) := by
  classical
  have hp : 2 * Real.pi ≠ 0 := by positivity
  simp only [unmarkedFormFactor, MontgomeryFormFactor.pairSum, Complex.re_sum,
    ZeroOrdinate.phase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, Real.exp_zero, one_mul, Finset.mul_sum]
  rw [← Finset.sum_coe_sort (unmarkedGapIndices gapLimit T)
    (fun i : ℕ => ∑ j ∈ unmarkedGapIndices gapLimit T, pairWeight T i j *
      (f α * Real.cos (2 * Real.pi * α * gapCoordinate T i j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_coe_sort (unmarkedGapIndices gapLimit T)
    (fun j : ℕ => pairWeight T i j * (f α * Real.cos (2 * Real.pi * α * gapCoordinate T i j)))]
  apply Finset.sum_congr rfl
  intro j hj
  have harg : (α * Real.log T) * (cutoffOrdinate T i-cutoffOrdinate T j) =
      2 * Real.pi * α * gapCoordinate T i j := by
    unfold gapCoordinate
    field_simp <;> ring
  rw [harg]
  unfold pairWeight
  ring

private theorem integrable_cosine_weight {f : ℝ → ℝ} (hf : Integrable f)
    (u w : ℝ) : Integrable (fun x : ℝ => w * (f x * Real.cos (2*Real.pi*x*u))) := by
  apply Integrable.const_mul
  apply hf.mul_bdd (c := 1)
  · exact (show Continuous (fun x : ℝ => Real.cos (2*Real.pi*x*u)) by fun_prop).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs] using (Real.abs_cos_le_one (2*Real.pi*x*u))

theorem integrable_unmarked_test {f : ℝ → ℝ} (hf : Integrable f) (gapLimit T : ℝ) :
    Integrable (fun α => f α * unmarkedFormFactor gapLimit T α) := by
  simp_rw [unmarked_integrand]
  apply integrable_finsetSum
  intro i hi
  exact integrable_finsetSum _ (fun j hj =>
    integrable_cosine_weight hf (gapCoordinate T i j) (pairWeight T i j))

/-- Exact finite Fourier interchange for every real integrable test. -/
theorem unmarked_pairSum_eq_integral (gapLimit T : ℝ) {f : ℝ → ℝ} (hf : Integrable f) :
    (∫ α : ℝ, f α * unmarkedFormFactor gapLimit T α) =
      unmarkedGapPairSum gapLimit T (LamzouriSmallGapCriterion.cosineTransform f) := by
  simp_rw [unmarked_integrand]
  have h (i j : ℕ) := integrable_cosine_weight hf (gapCoordinate T i j) (pairWeight T i j)
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => h i j))]
  unfold unmarkedGapPairSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => h i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]
  rfl

/-- The tested Fourier-side sum is monotone in the original frequency test.
Individual Fourier values may have either sign. -/
theorem unmarked_pairSum_mono {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfg : ∀ α, f α ≤ g α) (gapLimit T : ℝ) :
    unmarkedGapPairSum gapLimit T (LamzouriSmallGapCriterion.cosineTransform f) ≤
      unmarkedGapPairSum gapLimit T (LamzouriSmallGapCriterion.cosineTransform g) := by
  rw [← unmarked_pairSum_eq_integral gapLimit T hf, ← unmarked_pairSum_eq_integral gapLimit T hg]
  exact integral_mono (integrable_unmarked_test hf gapLimit T)
    (integrable_unmarked_test hg gapLimit T)
    (fun α => mul_le_mul_of_nonneg_right (hfg α) (unmarkedFormFactor_nonneg gapLimit T α))

end RiemannResearch.Analysis.ActualZeroOrdinate
