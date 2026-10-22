/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CumulativeSignedGap
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Automatic disappearance of relative negative-prefix variation

The normalized negative-prefix penalty need not be supplied as a separate
analytic estimate. If the terminal positive absorption mass diverges and
every earlier negative excursion is at most a fixed multiple of that mass,
the penalty tends to zero automatically. This uses actual summable decreases
of a convergent antitone residual, and retains all signed head and tail sums.
No arithmetic cumulative-budget provider is proved here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.HeadTailStrengthening

/-- Bounded relative negative excursions are enough: an `o(A)` prefix floor
is unnecessary because only the summable residual-energy decreases are charged.
The positive terminal prefix may be selected cofinally. -/
theorem negativePrefixVariationPenalty_div_tendsto_zero_of_relative_floor
    (a D : ℕ → ℝ) (k : ℕ → ℕ) (delta C : ℝ)
    (hD : Antitone D) (hlim : Tendsto D atTop (𝓝 delta))
    (hk : Tendsto k atTop atTop) (hC : 0 ≤ C)
    (hmass : Tendsto (fun n => signedGapPrefix a (k n)) atTop atTop)
    (hfloor : ∀ᶠ n in atTop, ∀ i < k n,
      -(C * signedGapPrefix a (k n)) ≤ signedGapPrefix a (i+1)) :
    Tendsto (fun n => negativePrefixVariationPenalty a D (k n) /
      signedGapPrefix a (k n)) atTop (𝓝 0) := by
  have hv (i : ℕ) : 0 ≤ D i - D (i+1) :=
    sub_nonneg.mpr (hD (Nat.le_succ i))
  have htel (m : ℕ) :
      (∑ i ∈ Finset.range m, (D i - D (i+1))) = D 0 - D m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hvariation : Summable (fun i => D i - D (i+1)) := by
    have hs : HasSum (fun i => D i - D (i+1)) (D 0 - delta) := by
      apply (hasSum_iff_tendsto_nat_of_nonneg hv _).mpr
      simpa only [htel] using tendsto_const_nhds.sub hlim
    exact hs.summable
  have hmajorSum : Summable (fun i => C * (D i - D (i+1))) :=
    hvariation.mul_left C
  let T (n i : ℕ) : ℝ := if i ∈ Finset.range (k n) then
    max (-(signedGapPrefix a (i+1))) 0 * (D i - D (i+1)) /
      signedGapPrefix a (k n) else 0
  have hinv : Tendsto (fun n => (signedGapPrefix a (k n))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hmass
  have hpoint (i : ℕ) : Tendsto (fun n => T n i) atTop (𝓝 0) := by
    have ht := hinv.const_mul
      (max (-(signedGapPrefix a (i+1))) 0 * (D i - D (i+1)))
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hk.eventually (eventually_ge_atTop (i+1))] with n hn
    have hi : i ∈ Finset.range (k n) :=
      Finset.mem_range.mpr (Nat.lt_of_succ_le hn)
    simp only [T, if_pos hi, div_eq_mul_inv]
  have hpos : ∀ᶠ n in atTop, 0 < signedGapPrefix a (k n) :=
    hmass.eventually (eventually_gt_atTop (0 : ℝ))
  have hmajor : ∀ᶠ n in atTop, ∀ i, ‖T n i‖ ≤ C * (D i - D (i+1)) := by
    filter_upwards [hpos, hfloor] with n hn hf
    intro i
    by_cases hi : i ∈ Finset.range (k n)
    · have hnum : max (-(signedGapPrefix a (i+1))) 0 ≤
          C * signedGapPrefix a (k n) := by
        apply max_le
        · linarith only [hf i (Finset.mem_range.mp hi)]
        · exact mul_nonneg hC hn.le
      have hq : max (-(signedGapPrefix a (i+1))) 0 /
          signedGapPrefix a (k n) ≤ C :=
        (div_le_iff₀ hn).mpr hnum
      have hnonneg : 0 ≤ T n i := by
        simp only [T, if_pos hi]
        exact div_nonneg (mul_nonneg (le_max_right _ _) (hv i)) hn.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        T n i = (max (-(signedGapPrefix a (i+1))) 0 /
            signedGapPrefix a (k n)) * (D i - D (i+1)) := by
          simp only [T, if_pos hi]
          ring
        _ ≤ C * (D i - D (i+1)) :=
          mul_le_mul_of_nonneg_right hq (hv i)
    · simp only [T, if_neg hi, norm_zero]
      exact mul_nonneg hC (hv i)
  have ht := tendsto_tsum_of_dominated_convergence hmajorSum hpoint hmajor
  have he (n : ℕ) : (∑' i, T n i) =
      negativePrefixVariationPenalty a D (k n) / signedGapPrefix a (k n) := by
    rw [tsum_eq_sum (s := Finset.range (k n))
      (by intro i hi; simp only [T, if_neg hi])]
    unfold negativePrefixVariationPenalty
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [T, if_pos hi]
  simpa only [he, tsum_zero] using ht

/-- A cofinal cumulative signed criterion with no separate variation-smallness
provider. Earlier negative prefixes may be as large as `O(A_(k n))`.
The remaining provider is the signed cumulative tail budget and its signed
head-and-remainder numerator, normalized by a diverging positive prefix. -/
theorem limit_eq_zero_of_cofinal_signed_prefix_relative_floor
    (D H L a Z : ℕ → ℝ) (k : ℕ → ℕ) (delta C : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hk : Tendsto k atTop atTop) (hmono : Antitone D)
    (hid : ∀ n, D n = H n + L n) (hC : 0 ≤ C)
    (hmass : Tendsto (fun n => signedGapPrefix a (k n)) atTop atTop)
    (hfloor : ∀ᶠ n in atTop, ∀ i < k n,
      -(C * signedGapPrefix a (k n)) ≤ signedGapPrefix a (i+1))
    (hbudget : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range (k n), (L i - (1-a i)*D i)) ≤ Z (k n))
    (hsmall : Tendsto (fun n =>
      ((∑ i ∈ Finset.range (k n), (H i)) + Z (k n)) /
        signedGapPrefix a (k n)) atTop (𝓝 0)) : delta = 0 := by
  have hvar := negativePrefixVariationPenalty_div_tendsto_zero_of_relative_floor
    a D k delta C hmono hD hk hC hmass hfloor
  have hcombined : Tendsto (fun n =>
      ((∑ i ∈ Finset.range (k n), (H i)) + Z (k n) +
        negativePrefixVariationPenalty a D (k n)) /
          signedGapPrefix a (k n)) atTop (𝓝 0) := by
    simpa only [← add_div, zero_add] using hsmall.add hvar
  exact limit_eq_zero_of_cofinal_signed_prefix_variation D H L a Z k delta
    hdelta hD hk hmono hid
    (hmass.eventually (eventually_gt_atTop (0 : ℝ))) hbudget hcombined

end RiemannResearch.Analysis.HeadTailStrengthening
