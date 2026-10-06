/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MovingSignedGap
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cumulative signed gaps with exact negative-prefix variation

Source: user-provided Green-Pareto-Schur continuation, Appendix A,
and the requested improvement of 6 October 2026.
This strengthens the stagewise moving-gap consumer. The increments `a n`
may have either sign. Negative cumulative prefixes are allowed with their exact energy-variation
penalty, and the signed tail budget is imposed cumulatively. No arithmetic provider is
claimed. All physical signed tail interactions remain in `L`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.HeadTailStrengthening

/-- Abel's lower bound for a decreasing sequence and nonnegative cumulative
weights. Individual weights may be negative and total variation is unrestricted. -/
theorem prefix_sum_mul_antitone_lower
    (a D : ℕ → ℝ) (hD : Antitone D)
    (hprefix : ∀ n, 0 ≤ ∑ i ∈ Finset.range n, (a i)) (n : ℕ) :
    (∑ i ∈ Finset.range n, (a i)) * D n ≤
      ∑ i ∈ Finset.range n, (a i * D i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : D (n+1) ≤ D n := hD (Nat.le_succ n)
    have hp : 0 ≤ (∑ i ∈ Finset.range n, (a i)) + a n := by
      simpa only [Finset.sum_range_succ] using hprefix (n+1)
    simp only [Finset.sum_range_succ]
    calc
      ((∑ i ∈ Finset.range n, (a i)) + a n) * D (n+1)
          ≤ ((∑ i ∈ Finset.range n, (a i)) + a n) * D n :=
        mul_le_mul_of_nonneg_left hm hp
      _ ≤ (∑ i ∈ Finset.range n, (a i * D i)) + a n * D n := by
        nlinarith only [ih]

/-- Cumulative signed budget before any absolute-value bound on the head. -/
theorem signed_prefix_gap_bound
    (D H L a : ℕ → ℝ) (Z : ℝ) (n : ℕ)
    (hD : Antitone D) (hid : ∀ i, D i = H i + L i)
    (hprefix : ∀ m, 0 ≤ ∑ i ∈ Finset.range m, (a i))
    (hpos : 0 < ∑ i ∈ Finset.range n, (a i))
    (hbudget : (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) ≤ Z) :
    D n ≤ ((∑ i ∈ Finset.range n, (H i))+Z) /
      (∑ i ∈ Finset.range n, (a i)) := by
  have hab := prefix_sum_mul_antitone_lower a D hD hprefix n
  have heq : (∑ i ∈ Finset.range n, (a i * D i)) =
      (∑ i ∈ Finset.range n, (H i)) +
      (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    nlinarith only [hid i]
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hab, heq, hbudget]

/-- Individual gaps need not be positive, and signed head terms may cancel
across stages. A cumulative smallness provider suffices. -/
theorem limit_eq_zero_of_signed_prefix_gap
    (D H L a Z : ℕ → ℝ) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hmono : Antitone D) (hid : ∀ n, D n = H n + L n)
    (hprefix : ∀ n, 0 ≤ ∑ i ∈ Finset.range n, (a i))
    (hpos : ∀ᶠ n in atTop, 0 < ∑ i ∈ Finset.range n, (a i))
    (hbudget : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) ≤ Z n)
    (hsmall : Tendsto (fun n =>
      ((∑ i ∈ Finset.range n, (H i))+Z n) /
        (∑ i ∈ Finset.range n, (a i))) atTop (𝓝 0)) : delta = 0 := by
  have hb : ∀ᶠ n in atTop, D n ≤
      ((∑ i ∈ Finset.range n, (H i))+Z n) /
        (∑ i ∈ Finset.range n, (a i)) := by
    filter_upwards [hpos, hbudget] with n hn hb
    exact signed_prefix_gap_bound D H L a (Z n) n hmono hid hprefix hn hb
  exact le_antisymm (le_of_tendsto_of_tendsto hD hsmall hb) hdelta

end RiemannResearch.Analysis.HeadTailStrengthening

namespace RiemannResearch.Analysis.HeadTailStrengthening

/-- Complete signed cumulative absorption mass. -/
def signedGapPrefix (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (a i)

/-- Negative cumulative excursions are charged only against actual decreases
of the residual energy; no termwise absolute value of a head or tail is used. -/
def negativePrefixVariationPenalty (a D : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (max (-(signedGapPrefix a (i+1))) 0 * (D i - D (i+1)))

/-- Exact summation by parts, retaining the finite terminal energy. -/
theorem signed_prefix_Abel_identity (a D : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (a i * D i)) =
      signedGapPrefix a n * D n +
        (∑ i ∈ Finset.range n,
          (signedGapPrefix a (i+1) * (D i - D (i+1)))) := by
  induction n with
  | zero => simp [signedGapPrefix]
  | succ n ih =>
    have hp : signedGapPrefix a (n+1) = signedGapPrefix a n + a n := by
      simp [signedGapPrefix, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hp]
    ring

/-- The sharp one-sided Abel repair: prefixes may have either sign. -/
theorem signed_prefix_variation_lower (a D : ℕ → ℝ)
    (hD : Antitone D) (n : ℕ) :
    signedGapPrefix a n * D n ≤
      (∑ i ∈ Finset.range n, (a i * D i)) +
        negativePrefixVariationPenalty a D n := by
  have hs : 0 ≤ (∑ i ∈ Finset.range n,
      ((signedGapPrefix a (i+1) + max (-(signedGapPrefix a (i+1))) 0) *
        (D i - D (i+1)))) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · linarith [le_max_left (-(signedGapPrefix a (i+1))) (0 : ℝ)]
    · exact sub_nonneg.mpr (hD (Nat.le_succ i))
  have he : (∑ i ∈ Finset.range n, (a i * D i)) +
      negativePrefixVariationPenalty a D n =
      signedGapPrefix a n * D n +
        (∑ i ∈ Finset.range n,
          ((signedGapPrefix a (i+1) + max (-(signedGapPrefix a (i+1))) 0) *
            (D i - D (i+1)))) := by
    rw [signed_prefix_Abel_identity]
    unfold negativePrefixVariationPenalty
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  linarith only [hs, he]

theorem negativePrefixVariationPenalty_nonneg (a D : ℕ → ℝ)
    (hD : Antitone D) (n : ℕ) :
    0 ≤ negativePrefixVariationPenalty a D n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (le_max_right _ _)
    (sub_nonneg.mpr (hD (Nat.le_succ i)))

/-- The former nonnegative-prefix consumer is recovered with zero penalty. -/
theorem negativePrefixVariationPenalty_eq_zero_of_nonneg_prefix
    (a D : ℕ → ℝ) (n : ℕ)
    (hprefix : ∀ i, 0 ≤ signedGapPrefix a i) :
    negativePrefixVariationPenalty a D n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hm : max (-(signedGapPrefix a (i+1))) 0 = 0 :=
    max_eq_right (by linarith [hprefix (i+1)])
  simp only [hm, zero_mul]

/-- A bounded negative prefix floor costs only bounded total energy variation. -/
theorem negativePrefixVariationPenalty_le_floor (a D : ℕ → ℝ)
    (hD : Antitone D) (C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hfloor : ∀ i < n, -C ≤ signedGapPrefix a (i+1)) :
    negativePrefixVariationPenalty a D n ≤ C * (D 0 - D n) := by
  have htel : (∑ i ∈ Finset.range n, (D i - D (i+1))) = D 0 - D n := by
    clear hfloor
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  calc
    negativePrefixVariationPenalty a D n ≤
        ∑ i ∈ Finset.range n, (C * (D i - D (i+1))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
      · apply max_le
        · linarith [hfloor i (Finset.mem_range.mp hi)]
        · exact hC
      · exact sub_nonneg.mpr (hD (Nat.le_succ i))
    _ = C * (D 0 - D n) := by rw [← Finset.mul_sum, htel]

/-- The signed budget is cumulative; all stage interactions survive until
the exact sum has formed. Negative prefixes are permitted with their penalty. -/
theorem signed_prefix_gap_variation_bound
    (D H L a : ℕ → ℝ) (Z : ℝ) (n : ℕ)
    (hD : Antitone D) (hid : ∀ i, D i = H i + L i)
    (hpos : 0 < signedGapPrefix a n)
    (hbudget : (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) ≤ Z) :
    D n ≤ ((∑ i ∈ Finset.range n, (H i)) + Z +
        negativePrefixVariationPenalty a D n) / signedGapPrefix a n := by
  have hab := signed_prefix_variation_lower a D hD n
  have heq : (∑ i ∈ Finset.range n, (a i * D i)) =
      (∑ i ∈ Finset.range n, (H i)) +
      (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    nlinarith only [hid i]
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hab, heq, hbudget]

/-- Bounded negative prefix excursions do not require a penalty provider:
the complete defect consumes only a shifted terminal absorption mass. -/
theorem signed_prefix_gap_floor_bound
    (D H L a : ℕ → ℝ) (Z C : ℝ) (n : ℕ)
    (hD : Antitone D) (hid : ∀ i, D i = H i + L i)
    (hC : 0 ≤ C) (hfloor : ∀ i < n, -C ≤ signedGapPrefix a (i+1))
    (hpos : 0 < signedGapPrefix a n + C)
    (hbudget : (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) ≤ Z) :
    D n ≤ ((∑ i ∈ Finset.range n, (H i)) + Z + C*D 0) /
      (signedGapPrefix a n + C) := by
  have hab := signed_prefix_variation_lower a D hD n
  have hp := negativePrefixVariationPenalty_le_floor a D hD C hC n hfloor
  have heq : (∑ i ∈ Finset.range n, (a i * D i)) =
      (∑ i ∈ Finset.range n, (H i)) +
      (∑ i ∈ Finset.range n, (L i - (1-a i)*D i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    nlinarith only [hid i]
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hab, hp, heq, hbudget]

/-- Cofinal cancellation with energy-weighted negative-prefix variation.
No sign restriction on an individual gap or on an intermediate prefix. -/
theorem limit_eq_zero_of_cofinal_signed_prefix_variation
    (D H L a Z : ℕ → ℝ) (k : ℕ → ℕ) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hD : Tendsto D atTop (𝓝 delta))
    (hk : Tendsto k atTop atTop) (hmono : Antitone D)
    (hid : ∀ n, D n = H n + L n)
    (hpos : ∀ᶠ n in atTop, 0 < signedGapPrefix a (k n))
    (hbudget : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range (k n), (L i - (1-a i)*D i)) ≤ Z (k n))
    (hsmall : Tendsto (fun n =>
      ((∑ i ∈ Finset.range (k n), (H i)) + Z (k n) +
        negativePrefixVariationPenalty a D (k n)) /
          signedGapPrefix a (k n)) atTop (𝓝 0)) : delta = 0 := by
  have hb : ∀ᶠ n in atTop, D (k n) ≤
      ((∑ i ∈ Finset.range (k n), (H i)) + Z (k n) +
        negativePrefixVariationPenalty a D (k n)) /
          signedGapPrefix a (k n) := by
    filter_upwards [hpos, hbudget] with n hn hb
    exact signed_prefix_gap_variation_bound D H L a (Z (k n)) (k n)
      hmono hid hn hb
  exact le_antisymm (le_of_tendsto_of_tendsto (hD.comp hk) hsmall hb) hdelta

end RiemannResearch.Analysis.HeadTailStrengthening
