/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.PrimeOrdinateMinors
import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.ActualZeroCountAsymptotics

/-!
# Prime determinants on successive actual zeta ordinates

All indices are chronological copies. The last pair and triple in each sum
end at the last actual ordinate. Fujii, *On the difference between r
consecutive ordinates of the zeros of the Riemann zeta function*, Proc.
Japan Acad. 51 (1975), 741–743, Theorem 1,
https://doi.org/10.3792/pja/1195518466, provides classical moment estimates.
The finite transfers preserve the mixed cubic term. They make no spacing,
simplicity or RH assumption. The unconditional count-normalized limit below
uses the project's actual Riemann–von Mangoldt bound alone.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.PrimeOrdinateMinors
open ActualZeroOrdinate

/-- Sum of powers of interior gaps only. -/
def interiorGapMoment (k : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Ncount 0 T - 1), (cutoffGap T j)^k

/-- The mixed cubic moment on two adjacent interior gaps. -/
def mixedGapSum (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Ncount 0 T - 2),
    cutoffGap T j * cutoffGap T (j+1) * (cutoffGap T j + cutoffGap T (j+1))

/-- Total absolute pair determinant, with each consecutive pair counted once. -/
def pairSum (p q : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Ncount 0 T - 1),
    ‖pairMinor p q (cutoffOrdinate T j) (cutoffOrdinate T (j+1))‖

/-- Total absolute quadratic determinant over genuine consecutive triples. -/
def tripleSum (p q : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Ncount 0 T - 2),
    ‖tripleMinor p q (cutoffOrdinate T j) (cutoffOrdinate T (j+1)) (cutoffOrdinate T (j+2))‖

/-- Mixed cubic mass equals twice the cubic moment less the two endpoints
and the weighted squared variation of successive gaps. -/
theorem mixed_cubic_balance (g : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, g j * g (j+1) * (g j + g (j+1))) =
      2*(∑ j ∈ Finset.range (n+1), (g j)^3) - (g 0)^3 - (g n)^3 -
        ∑ j ∈ Finset.range n, (g j - g (j+1))^2 * (g j + g (j+1)) := by
  have he : (∑ j ∈ Finset.range n, g j * g (j+1) * (g j + g (j+1))) +
      (∑ j ∈ Finset.range n, (g j - g (j+1))^2 * (g j + g (j+1))) =
      (∑ j ∈ Finset.range n, (g j)^3) + ∑ j ∈ Finset.range n, (g (j+1))^3 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h₀ := Finset.sum_range_succ (fun j => (g j)^3) n
  have h₁ := Finset.sum_range_succ' (fun j => (g j)^3) n
  linarith

private theorem sum_adjacent_le (N : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ Finset.range (N-2), (f j + f (j+1))) ≤ 2 * ∑ j ∈ Finset.range (N-1), f j := by
  by_cases hN : 2 ≤ N
  · have he : N-1 = N-2+1 := by omega
    rw [he, Finset.sum_add_distrib]
    linarith only [Finset.sum_range_succ f (N-2), Finset.sum_range_succ' f (N-2),
      hf 0, hf (N-2)]
  · rw [show N-2=0 by omega, show N-1=0 by omega]
    simp

/-- The pair main term is exactly the first-to-last span times the log separation.
The cubic error bound includes neither initial nor final padding. -/
theorem pairSum_defect (p q : ℕ) (T : ℝ) :
    let d := logDistance p q
    let span := cutoffOrdinate T (Ncount 0 T - 1) - cutoffOrdinate T 0
    0 ≤ d * span - pairSum p q T ∧
      d * span - pairSum p q T ≤ d^3/24 * interiorGapMoment 3 T := by
  let d := logDistance p q
  let n := Ncount 0 T - 1
  let g := cutoffGap T
  have hpair (j : ℕ) : ‖pairMinor p q (cutoffOrdinate T j) (cutoffOrdinate T (j+1))‖ =
      chord (d*g j) := by
    rw [pairMinor_norm]
    change chord (d * |g j|) = chord (d*g j)
    rw [abs_of_nonneg (cutoffGap_nonneg T j)]
  have he : d*(cutoffOrdinate T n-cutoffOrdinate T 0) - pairSum p q T =
      ∑ j ∈ Finset.range n, (d*g j - chord (d*g j)) := by
    have htel : (∑ j ∈ Finset.range n, g j) = cutoffOrdinate T n - cutoffOrdinate T 0 :=
      Finset.sum_range_sub (cutoffOrdinate T) n
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htel]
    simp only [pairSum, hpair, n]
  dsimp only
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (chord_le
      (mul_nonneg (logDistance_nonneg p q) (cutoffGap_nonneg T j)))
  · rw [interiorGapMoment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := chord_defect_le (mul_nonneg (logDistance_nonneg p q) (cutoffGap_nonneg T j))
    dsimp only [g, d]
    linarith only [h]

private theorem triple_defect_at (p q : ℕ) (T : ℝ) (j : ℕ) :
    let d := logDistance p q
    let g := cutoffGap T j
    let h := cutoffGap T (j+1)
    let v := ‖tripleMinor p q (cutoffOrdinate T j) (cutoffOrdinate T (j+1))
      (cutoffOrdinate T (j+2))‖
    0 ≤ d^3*(g*h*(g+h)) - v ∧ d^3*(g*h*(g+h)) - v ≤ d^5/4*(g^5+h^5) := by
  let g := cutoffGap T j
  let h := cutoffGap T (j+1)
  have hg : 0 ≤ g := cutoffGap_nonneg T j
  have hh : 0 ≤ h := cutoffGap_nonneg T (j+1)
  have e₁ : cutoffOrdinate T j + g = cutoffOrdinate T (j+1) := by dsimp [g, cutoffGap]; ring
  have e₂ : cutoffOrdinate T j + g + h = cutoffOrdinate T (j+2) := by
    dsimp [g, h, cutoffGap]; ring
  have hb := tripleMinor_defect p q (cutoffOrdinate T j) hg hh
  dsimp only at hb ⊢
  rw [e₂, e₁] at hb
  have hp : g*h*(g+h)*(g^2+g*h+h^2) ≤ 3*(g^5+h^5) := by
    have hpos : 0 ≤ 3*g^2+2*g*h+3*h^2 := by positivity
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg (g-h)) (add_nonneg hg hh)) hpos]
  have hmul := mul_le_mul_of_nonneg_left hp (pow_nonneg (logDistance_nonneg p q) 5)
  change 0 ≤ _ - _ ∧ _ - _ ≤ _ * (g^5 + h^5)
  constructor <;> linarith only [hb.1, hb.2, hmul]

/-- Summed fifth-order error, uniform in both prime columns. -/
theorem tripleSum_defect (p q : ℕ) (T : ℝ) :
    let d := logDistance p q
    0 ≤ d^3 * mixedGapSum T - tripleSum p q T ∧
      d^3 * mixedGapSum T - tripleSum p q T ≤ d^5/2 * interiorGapMoment 5 T := by
  dsimp only
  rw [mixedGapSum, Finset.mul_sum, tripleSum, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg fun j _ => (triple_defect_at p q T j).1
  · calc
      _ ≤ ∑ j ∈ Finset.range (Ncount 0 T-2),
            logDistance p q^5/4 * ((cutoffGap T j)^5+(cutoffGap T (j+1))^5) :=
          Finset.sum_le_sum (fun j _ => (triple_defect_at p q T j).2)
      _ = _ := (Finset.mul_sum ..).symm
      _ ≤ (logDistance p q^5/4) * (2*interiorGapMoment 5 T) :=
          mul_le_mul_of_nonneg_left (sum_adjacent_le _ (fun j => (cutoffGap T j)^5)
            (fun j => pow_nonneg (cutoffGap_nonneg T j) 5))
          (div_nonneg (pow_nonneg (logDistance_nonneg p q) 5) (by norm_num))
      _ = _ := by ring

/-- The absolute pair and triple averages both vanish for fixed columns. -/
theorem tendsto_consecutive_minor_means (p q : ℕ) :
    Tendsto (fun T : ℝ => pairSum p q T / (Ncount 0 T : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => tripleSum p q T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  have hpair (T : ℝ) (hT : 0 ≤ T) : pairSum p q T ≤ logDistance p q*T := by
    have h₀ : 0 ≤ cutoffOrdinate T 0 := by
      by_cases hn : 0 < Ncount 0 T
      · exact (cutoffOrdinate_bounds hn).1.le
      · rw [cutoffOrdinate_of_count_le (Nat.le_of_not_gt hn)]; exact hT
    have hspan : cutoffOrdinate T (Ncount 0 T-1) - cutoffOrdinate T 0 ≤ T := by
      linarith [cutoffOrdinate_le T (Ncount 0 T-1)]
    exact (sub_nonneg.mp (pairSum_defect p q T).1).trans
      (mul_le_mul_of_nonneg_left hspan (logDistance_nonneg p q))
  have ht (T : ℝ) : tripleSum p q T ≤ 4 * pairSum p q T := by
    unfold tripleSum pairSum
    rw [Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum fun j _ => tripleMinor_norm_le_four_pair p q
      (cutoffOrdinate T j) (cutoffOrdinate T (j+1)) (cutoffOrdinate T (j+2)))
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intros; positivity
  have hp : Tendsto (fun T : ℝ => pairSum p q T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun T : ℝ => logDistance p q * T / (Ncount 0 T : ℝ))
      (Eventually.of_forall (fun T => div_nonneg
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg _))) ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact div_le_div_of_nonneg_right (hpair T hT) (Nat.cast_nonneg _)
    · simpa only [mul_div_assoc, mul_zero] using tendsto_height_div_count.const_mul (logDistance p q)
  refine ⟨hp, squeeze_zero' (g := fun T : ℝ => 4 * pairSum p q T / (Ncount 0 T : ℝ))
    (Eventually.of_forall (fun T => div_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg _))) ?_ ?_⟩
  · exact Eventually.of_forall fun T => div_le_div_of_nonneg_right (ht T) (Nat.cast_nonneg _)
  · simpa only [mul_div_assoc, mul_zero] using hp.const_mul 4

end RiemannResearch.Analysis.PrimeOrdinateMinors
