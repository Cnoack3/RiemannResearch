import RiemannResearch.Analysis.LogarithmicPrimePairs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Removing a triangular weight from logarithmic prime-pair sums

The one-sided triangular weight is the positive-gap part of the interval
overlap kernel. Its right and left secants bound the sharp statistic because
von Mangoldt coefficients are nonnegative. The exact increment retains every
pair crossing the lower cutoff. The limiting quadratic triangular moment
for the actual arithmetic coefficients is an explicit hypothesis.
-/

noncomputable section
open Filter Finset
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.LogarithmicPrimePairs

def trianglePairAverage (A B u X : ℝ) : ℝ :=
  (∑ h ∈ Ioc 0 (shiftWidth u X),
    (u - (h : ℝ) / Real.log X) * pairBlock A B X h) / (X * Real.log X)

private theorem sharp_eq (A B u X : ℝ) :
    sharpPairAverage A B u X =
      (∑ h ∈ Ioc 0 (shiftWidth u X), pairBlock A B X h) / (X * Real.log X) := by
  unfold sharpPairAverage pairBlock
  rw [sum_comm]

private theorem split_prefix (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ h ∈ Ioc 0 b, f h) = (∑ h ∈ Ioc 0 a, f h) + ∑ h ∈ Ioc a b, f h := by
  have hu : Ioc 0 b = Ioc 0 a ∪ Ioc a b := by
    ext j
    simp only [mem_Ioc, mem_union]
    omega
  rw [hu, sum_union]
  exact disjoint_left.mpr fun _ hi hj => (not_lt_of_ge (mem_Ioc.mp hi).2) (mem_Ioc.mp hj).1

/-- The positive mass in the newly admitted band is the exact increment remainder. -/
theorem triangle_increment {a b X : ℝ} (A B : ℝ) (hab : a ≤ b) (hX : 1 < X) :
    trianglePairAverage A B b X - trianglePairAverage A B a X =
      (b - a) * sharpPairAverage A B a X +
        (∑ h ∈ Ioc (shiftWidth a X) (shiftWidth b X),
          (b - (h : ℝ) / Real.log X) * pairBlock A B X h) / (X * Real.log X) := by
  have hw : shiftWidth a X ≤ shiftWidth b X :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hab (Real.log_pos hX).le)
  have hs : (∑ h ∈ Ioc 0 (shiftWidth a X), (b - (h : ℝ) / Real.log X) * pairBlock A B X h) =
      (∑ h ∈ Ioc 0 (shiftWidth a X), (a - (h : ℝ) / Real.log X) * pairBlock A B X h) +
        (b - a) * ∑ h ∈ Ioc 0 (shiftWidth a X), pairBlock A B X h := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    ring
  unfold trianglePairAverage
  rw [split_prefix (fun h => (b - (h : ℝ) / Real.log X) * pairBlock A B X h) hw, hs,
    sharp_eq A B a X]
  ring

theorem triangle_increment_bounds {a b X : ℝ} (A B : ℝ) (ha : 0 < a)
    (hab : a < b) (hX : 1 < X) :
    (b - a) * sharpPairAverage A B a X ≤
        trianglePairAverage A B b X - trianglePairAverage A B a X ∧
      trianglePairAverage A B b X - trianglePairAverage A B a X ≤
        (b - a) * sharpPairAverage A B b X := by
  have hl := Real.log_pos hX
  have hden : 0 ≤ X * Real.log X := mul_nonneg (by linarith) hl.le
  have hW : shiftWidth a X ≤ shiftWidth b X :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hab.le hl.le)
  have hband (h : ℕ) (hh : h ∈ Ioc (shiftWidth a X) (shiftWidth b X)) :
      a < (h : ℝ) / Real.log X ∧ (h : ℝ) / Real.log X ≤ b := by
    obtain ⟨hlow, hhigh⟩ := mem_Ioc.mp hh
    constructor
    · by_contra! he
      exact (not_le_of_gt hlow) (Nat.le_floor ((div_le_iff₀ hl).mp he))
    · apply (div_le_iff₀ hl).mpr
      exact (show (h : ℝ) ≤ (shiftWidth b X : ℝ) by exact_mod_cast hhigh).trans
        (Nat.floor_le (mul_nonneg (ha.trans hab).le hl.le))
  rw [triangle_increment A B hab.le hX]
  constructor
  · apply le_add_of_nonneg_right
    apply div_nonneg _ hden
    exact sum_nonneg fun h hh =>
      mul_nonneg (sub_nonneg.mpr (hband h hh).2) (pairBlock_nonneg A B X h)
  · have hsum : (∑ h ∈ Ioc (shiftWidth a X) (shiftWidth b X),
          (b - (h : ℝ) / Real.log X) * pairBlock A B X h) ≤
        (b - a) * ∑ h ∈ Ioc (shiftWidth a X) (shiftWidth b X), pairBlock A B X h := by
      rw [mul_sum]
      exact sum_le_sum fun h hh => mul_le_mul_of_nonneg_right
        (sub_le_sub_left (hband h hh).1.le _) (pairBlock_nonneg A B X h)
    rw [sharp_eq A B a X, sharp_eq A B b X, split_prefix (pairBlock A B X) hW,
      add_div, mul_add]
    apply add_le_add le_rfl
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hsum hden

private theorem secant_limit {A B : ℝ}
    (ht : ∀ u : ℝ, 0 < u → Tendsto (trianglePairAverage A B u) atTop (𝓝 ((B - A) * u^2 / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun X => (trianglePairAverage A B b X - trianglePairAverage A B a X) / (b - a))
      atTop (𝓝 ((B - A) * (a + b) / 2)) := by
  have h := ((ht b (ha.trans hab)).sub (ht a ha)).div_const (b - a)
  have he : ((B - A) * b^2 / 2 - (B - A) * a^2 / 2) / (b - a) =
      (B - A) * (a + b) / 2 := by
    apply (div_eq_iff (sub_pos.mpr hab).ne').mpr
    ring
  rwa [he] at h

/-- A quadratic triangular law at positive fixed widths implies the sharp law,
including any pairs lying exactly at the cutoff. -/
theorem sharpPairAverage_of_triangle {A B : ℝ} (hAB : A < B)
    (ht : ∀ u : ℝ, 0 < u → Tendsto (trianglePairAverage A B u) atTop (𝓝 ((B - A) * u^2 / 2)))
    {d : ℝ} (hd : 0 < d) :
    Tendsto (sharpPairAverage A B d) atTop (𝓝 ((B - A) * d)) := by
  let c := B - A
  have hc : 0 < c := sub_pos.mpr hAB
  apply tendsto_order.mpr
  constructor
  · intro y hy
    change y < c * d at hy
    let e := min (d / 2) ((c * d - y) / c)
    have he : 0 < e := lt_min (by linarith) (div_pos (sub_pos.mpr hy) hc)
    have he1 : e ≤ d / 2 := min_le_left _ _
    have he2 : e * c ≤ c * d - y := (le_div_iff₀ hc).mp (min_le_right _ _)
    have ha : 0 < d - e := by linarith
    have hab : d - e < d := by linarith
    have hy' : y < (B - A) * (d - e + d) / 2 := by
      change y < c * (d - e + d) / 2
      nlinarith
    filter_upwards [(secant_limit ht ha hab).eventually (eventually_gt_nhds hy'),
      eventually_gt_atTop (1 : ℝ)] with X hsec hX
    apply hsec.trans_le
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    simpa only [mul_comm (d - (d - e)) _] using
      (triangle_increment_bounds A B ha hab hX).2
  · intro y hy
    change c * d < y at hy
    let e := (y - c * d) / c
    have he : 0 < e := div_pos (sub_pos.mpr hy) hc
    have he2 : e * c = y - c * d := div_mul_cancel₀ _ hc.ne'
    have hab : d < d + e := by linarith
    have hy' : (B - A) * (d + (d + e)) / 2 < y := by
      change c * (d + (d + e)) / 2 < y
      nlinarith
    filter_upwards [(secant_limit ht hd hab).eventually (eventually_lt_nhds hy'),
      eventually_gt_atTop (1 : ℝ)] with X hsec hX
    apply lt_of_le_of_lt _ hsec
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    simpa only [mul_comm (d + e - d) _] using
      (triangle_increment_bounds A B hd hab hX).1

end RiemannResearch.Analysis.LogarithmicPrimePairs
