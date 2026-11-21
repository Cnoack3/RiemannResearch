import RiemannResearch.RH.ScreenedParityPhysicalBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Localized one-sided Pareto estimates

The finite-window identity keeps the signed contribution from sites outside
the window. A positive legal test converts a one-sided excess into an
absolute first-moment bound. The final inequality measures the exceptional
set by its actual Pareto mass and squared energy.

Source: Christian Noack's quadratic-window handoff, Sections 1 and 2.
-/

noncomputable section
open scoped BigOperators InnerProductSpace Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization

/-- Exact two-sign decomposition of the tested mass on a finite set. -/
theorem window_test_signed_identity (W : Finset ℕ) (p q z : ℕ → ℝ) :
    (∑ n ∈ W, p n * (q n * |z n|)) + (∑ n ∈ W, p n * (q n * z n)) =
      2 * ∑ n ∈ W, p n * (q n * max (z n) 0) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : 0 ≤ z n
  · rw [abs_of_nonneg h, max_eq_left h]
    ring
  · rw [abs_of_neg (lt_of_not_ge h), max_eq_right (le_of_not_ge h)]
    ring

/-- Upper control on the positive excess bounds the absolute mass of the
window, with its full signed pairing still present on the left. -/
theorem window_test_le_positive_excess (W : Finset ℕ) (p q z : ℕ → ℝ)
    {a b C : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hp : ∀ n ∈ W, 0 ≤ p n) (hl : ∀ n ∈ W, a ≤ q n)
    (hu : ∀ n ∈ W, q n ≤ b) :
    a * (∑ n ∈ W, p n * |z n|) + (∑ n ∈ W, p n * (q n * z n)) ≤
      2 * b * (C * (∑ n ∈ W, p n) + ∑ n ∈ W, p n * max (z n - C) 0) := by
  calc
    _ ≤ (∑ n ∈ W, p n * (q n * |z n|)) + ∑ n ∈ W, p n * (q n * z n) := by
      apply add_le_add _ le_rfl
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      rw [show a * (p n * |z n|) = p n * (a * |z n|) by ring]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hl n hn) (abs_nonneg _)) (hp n hn)
    _ = 2 * ∑ n ∈ W, p n * (q n * max (z n) 0) := window_test_signed_identity W p q z
    _ ≤ 2 * ∑ n ∈ W, p n * (b * (C + max (z n - C) 0)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (hp n hn)
      have hm : max (z n) 0 ≤ C + max (z n - C) 0 := by
        apply max_le
        · linarith [le_max_left (z n - C) 0]
        · linarith [le_max_right (z n - C) 0]
      exact (mul_le_mul_of_nonneg_right (hu n hn) (le_max_right _ _)).trans
        (mul_le_mul_of_nonneg_left hm hb)
    _ = ∑ n ∈ W, ((2 * b * C) * p n + (2 * b) * (p n * max (z n - C) 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- In an orthogonal test with support starting at the window's left edge,
the signed pairing outside the window costs at most `b * exteriorMass`.
The explicit factor on the exterior is `a + b`. -/
theorem window_full_mass_le_positive_excess (W : Finset ℕ) (p q z : ℕ → ℝ)
    {a b C exteriorMass : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hp : ∀ n ∈ W, 0 ≤ p n) (hl : ∀ n ∈ W, a ≤ q n)
    (hu : ∀ n ∈ W, q n ≤ b)
    (hbalance : -(∑ n ∈ W, p n * (q n * z n)) ≤ b * exteriorMass) :
    a * ((∑ n ∈ W, p n * |z n|) + exteriorMass) ≤
      2 * b * (C * (∑ n ∈ W, p n) + ∑ n ∈ W, p n * max (z n - C) 0) +
        (a + b) * exteriorMass := by
  have h := window_test_le_positive_excess W p q z hb hC hp hl hu
  linarith only [h, hbalance]

/-- Orthogonality identifies the signed interior pairing exactly with the
opposite of the signed exterior pairing. The first site is H, and the window
contains L consecutive sites. -/
theorem legal_window_signed_exterior (q z : ThresholdHilbert) (hq : q ∈ closedSpace)
    (hz : z ∈ closedSpaceᗮ) (H L : ℕ) (hzero : ∀ j, j < H → hilbertSequence q j = 0) :
    -(∑ k ∈ Finset.range L, positiveWeight (k + H) *
        (hilbertSequence q (k + H) * hilbertSequence z (k + H))) =
      ∑' k : ℕ, positiveWeight (k + L + H) *
        (hilbertSequence q (k + L + H) * hilbertSequence z (k + L + H)) := by
  let f j := positiveWeight j * (hilbertSequence q j * hilbertSequence z j)
  have hs : Summable f := weighted_product_summable_of_square
    (hilbertSequence_square_summable q) (hilbertSequence_square_summable z)
  have hinner : (∑' j, f j) = 0 := (hilbert_inner_weighted q z).symm.trans (hz q hq)
  have hhead : (∑ j ∈ Finset.range H, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [f, hzero j (Finset.mem_range.mp hj)]
  have hshift : (∑' j : ℕ, f (j + H)) = 0 := by
    have ht := hs.sum_add_tsum_nat_add H
    rw [hhead, hinner, zero_add] at ht
    exact ht
  have ht := ((summable_nat_add_iff H).mpr hs).sum_add_tsum_nat_add L
  change (∑ k ∈ Finset.range L, f (k + H)) + (∑' k : ℕ, f (k + L + H)) =
    ∑' j : ℕ, f (j + H) at ht
  change -(∑ k ∈ Finset.range L, f (k + H)) = (∑' k : ℕ, f (k + L + H))
  linarith only [ht, hshift]

/-- The one-sided estimate for the full tail of an actual Pareto annihilator.
Only the physical window requires a lower bound for the test. Its signed
exterior is controlled by the true exterior absolute mass. -/
theorem annihilator_absolute_tail_le_window_excess (q z : ThresholdHilbert)
    (hq : q ∈ closedSpace) (hz : z ∈ closedSpaceᗮ) (H L : ℕ)
    {a b C : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hzero : ∀ n, n < H → hilbertSequence q n = 0)
    (hlo : ∀ k, k < L → a ≤ hilbertSequence q (k + H))
    (hbound : ∀ n, 0 ≤ hilbertSequence q n ∧ hilbertSequence q n ≤ b) :
    a * (∑' k : ℕ, positiveWeight (k + H) * |hilbertSequence z (k + H)|) ≤
      2 * b * (C * (∑ k ∈ Finset.range L, positiveWeight (k + H)) +
        ∑ k ∈ Finset.range L, positiveWeight (k + H) * max (hilbertSequence z (k + H) - C) 0) +
        (a + b) * ∑' k : ℕ, positiveWeight (k + L + H) * |hilbertSequence z (k + L + H)| := by
  let A j := positiveWeight j * |hilbertSequence z j|
  let f j := positiveWeight j * (hilbertSequence q j * hilbertSequence z j)
  have hA : Summable A := hilbertL1Norm_summable z
  have hf : Summable f := weighted_product_summable_of_square
    (hilbertSequence_square_summable q) (hilbertSequence_square_summable z)
  have hAs : Summable (fun k : ℕ => A (k + L + H)) :=
    (summable_nat_add_iff L).mpr ((summable_nat_add_iff H).mpr hA)
  have hfs : Summable (fun k : ℕ => f (k + L + H)) :=
    (summable_nat_add_iff L).mpr ((summable_nat_add_iff H).mpr hf)
  have hbalance : -(∑ k ∈ Finset.range L, f (k + H)) ≤ b * ∑' k : ℕ, A (k + L + H) := by
    calc
      _ = ∑' k : ℕ, f (k + L + H) := legal_window_signed_exterior q z hq hz H L hzero
      _ ≤ ∑' k : ℕ, A (k + L + H) * b := by
        apply Summable.tsum_le_tsum _ hfs (hAs.mul_right _)
        intro k
        let n := k + L + H
        change positiveWeight n * (hilbertSequence q n * hilbertSequence z n) ≤
          (positiveWeight n * |hilbertSequence z n|) * b
        calc
          _ ≤ positiveWeight n * (hilbertSequence q n * |hilbertSequence z n|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (le_abs_self _) (hbound n).1) (positiveWeight_nonneg n)
          _ ≤ positiveWeight n * (b * |hilbertSequence z n|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hbound n).2 (abs_nonneg _)) (positiveWeight_nonneg n)
          _ = _ := by ring
      _ = _ := by rw [tsum_mul_right, mul_comm]
  have h := window_full_mass_le_positive_excess (Finset.range L)
    (fun k => positiveWeight (k + H)) (fun k => hilbertSequence q (k + H))
    (fun k => hilbertSequence z (k + H)) hb hC
    (fun k _ => positiveWeight_nonneg _) (fun k hk => hlo k (Finset.mem_range.mp hk))
    (fun k _ => (hbound (k + H)).2) hbalance
  have ht := ((summable_nat_add_iff H).mpr hA).sum_add_tsum_nat_add L
  change (∑ k ∈ Finset.range L, A (k + H)) + (∑' k : ℕ, A (k + L + H)) =
    ∑' k : ℕ, A (k + H) at ht
  change a * (∑' k : ℕ, A (k + H)) ≤ _
  rw [← ht]
  exact h

/-- Exceptional absolute mass is bounded by the product of its actual
Pareto mass and its actual squared energy, before passing to global bounds. -/
theorem exceptional_absolute_mass_sq (z : ThresholdHilbert) (S : Finset ℕ) :
    (∑ n ∈ S, positiveWeight n * |hilbertSequence z n|)^2 ≤
      (∑ n ∈ S, positiveWeight n) *
        (∑ n ∈ S, positiveWeight n * (hilbertSequence z n)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro n _
    exact positiveWeight_nonneg n
  · intro n _
    exact mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)
  · intro n _
    rw [mul_pow, sq_abs]
    apply le_of_eq
    ring

/-- A set of `S.card` sites beyond H has Pareto mass at most
`S.card / H^2`. -/
theorem exceptional_pareto_mass_le_card_div_sq (S : Finset ℕ) (H : ℕ) (hH : 0 < H)
    (hl : ∀ n ∈ S, H ≤ n) :
    (∑ n ∈ S, positiveWeight n) ≤ (S.card : ℝ) / (H : ℝ)^2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ ∑ _n ∈ S, (1 : ℝ) / (H : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnr : (H : ℝ) ≤ n := by exact_mod_cast hl n hn
      have hnpos : (0 : ℝ) < n := hHR.trans_le hnr
      change 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ _
      apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hHR)).mpr
      simp only [one_mul, pow_two]
      exact mul_le_mul hnr (by linarith) hHR.le hnpos.le
    _ = _ := by simp [div_eq_mul_inv]

/-- Exceptional-count estimate with the global Hilbert energy. -/
theorem exceptional_absolute_mass_sq_le_card (z : ThresholdHilbert) (S : Finset ℕ)
    (H : ℕ) (hH : 0 < H) (hl : ∀ n ∈ S, H ≤ n) :
    (∑ n ∈ S, positiveWeight n * |hilbertSequence z n|)^2 ≤
      ((S.card : ℝ) / (H : ℝ)^2) * ‖z‖^2 := by
  apply (exceptional_absolute_mass_sq z S).trans
  apply mul_le_mul (exceptional_pareto_mass_le_card_div_sq S H hH hl)
  · rw [hilbert_norm_weighted_sq]
    exact (hilbertSequence_square_summable z).sum_le_tsum S
      (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
  · exact Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
  · positivity

/-- The actual one-sided excess over a threshold, with the exception count
taken in the same window and at the same threshold. -/
theorem window_excess_sq_le_exception_count (z : ThresholdHilbert)
    (W : Finset ℕ) (H : ℕ) (hH : 0 < H) (hl : ∀ n ∈ W, H ≤ n)
    (C : ℝ) (hC : 0 ≤ C) :
    (∑ n ∈ W, positiveWeight n * max (hilbertSequence z n - C) 0)^2 ≤
      (((W.filter (fun n => C < hilbertSequence z n)).card : ℝ) / (H : ℝ)^2) * ‖z‖^2 := by
  classical
  let S := W.filter (fun n => C < hilbertSequence z n)
  have hle : (∑ n ∈ W, positiveWeight n * max (hilbertSequence z n - C) 0) ≤
      ∑ n ∈ S, positiveWeight n * |hilbertSequence z n| := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n _
    by_cases hn : C < hilbertSequence z n
    · rw [if_pos hn]
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg n)
      exact max_le ((sub_le_self _ hC).trans (le_abs_self _)) (abs_nonneg _)
    · rw [if_neg hn, max_eq_right (sub_nonpos.mpr (le_of_not_gt hn)), mul_zero]
  have hx : 0 ≤ ∑ n ∈ W, positiveWeight n * max (hilbertSequence z n - C) 0 :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (le_max_right _ _))
  have hy : 0 ≤ ∑ n ∈ S, positiveWeight n * |hilbertSequence z n| :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (abs_nonneg _))
  apply ((sq_le_sq₀ hx hy).mpr hle).trans
  exact exceptional_absolute_mass_sq_le_card z S H hH
    (fun n hn => hl n (Finset.mem_filter.mp hn).1)

end RiemannResearch.RH.Pareto
