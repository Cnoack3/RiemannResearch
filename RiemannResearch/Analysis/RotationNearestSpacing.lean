import RiemannResearch.Analysis.RotationMinimumSpacing
import Mathlib.Algebra.Order.Round
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
# Actual nearest-integer errors and block spacing

Source: user-provided `DyadicRegularizedVerificationContinuation20260910 (2).md`
and the ordinary proof in `RH/Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`,
Section 3. This module supplies actual centered orbit points and chooses a
minimum denominator on every finite prefix. Its intended RH consumer is the
logarithmic Gram prefix bound; no norm or RH conclusion is assumed here.
-/

namespace RiemannResearch.Analysis

/-- The actual centered representative of the n-th rotation orbit point. -/
noncomputable def rotationCenteredError (α : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * α - (round ((n : ℝ) * α) : ℝ)

/-- Distance of the n-th rotation orbit point to the nearest integer. -/
noncomputable def rotationNearestDistance (α : ℝ) (n : ℕ) : ℝ :=
  |rotationCenteredError α n|

theorem rotationNearestDistance_nonneg (α : ℝ) (n : ℕ) :
    0 ≤ rotationNearestDistance α n := abs_nonneg _

theorem rotationNearestDistance_le_half (α : ℝ) (n : ℕ) :
    rotationNearestDistance α n ≤ 1 / 2 := by
  exact abs_sub_round ((n : ℝ) * α)

theorem rotationCenteredError_mem_Icc (α : ℝ) (n : ℕ) :
    rotationCenteredError α n ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  exact abs_le.mp (rotationNearestDistance_le_half α n)

/-- The chosen integer really minimizes the approximation error over all
integers; this does not assume any Diophantine lower bound. -/
theorem rotationNearestDistance_le_integer_error (α : ℝ) (n : ℕ) (z : ℤ) :
    rotationNearestDistance α n ≤ |(n : ℝ) * α - (z : ℝ)| := by
  let r : ℤ := round ((n : ℝ) * α)
  change |(n : ℝ) * α - (r : ℝ)| ≤ |(n : ℝ) * α - (z : ℝ)|
  by_cases h : r = z
  · rw [h]
  have hd : (0 : ℤ) < |r - z| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hd1 : (1 : ℤ) ≤ |r - z| := hd
  have hdR : (1 : ℝ) ≤ |(r : ℝ) - (z : ℝ)| := by
    exact_mod_cast hd1
  have htri := abs_sub_le (r : ℝ) ((n : ℝ) * α) (z : ℝ)
  rw [abs_sub_comm (r : ℝ) ((n : ℝ) * α)] at htri
  have hhalf : |(n : ℝ) * α - (r : ℝ)| ≤ 1 / 2 :=
    abs_sub_round ((n : ℝ) * α)
  linarith

theorem rotationNearestDistance_pos {α : ℝ} (hα : Irrational α)
    {n : ℕ} (hn : 0 < n) : 0 < rotationNearestDistance α n := by
  apply abs_pos.mpr
  apply sub_ne_zero.mpr
  exact (hα.natCast_mul (Nat.ne_of_gt hn)).ne_int _

/-- Every positive finite prefix has an actual minimum denominator. -/
theorem exists_rotationNearestDistance_minimum (α : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧
      ∀ h : ℕ, 0 < h → h ≤ N →
        rotationNearestDistance α q ≤ rotationNearestDistance α h := by
  have hne : (Finset.Icc 1 N).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  obtain ⟨q, hq, hmin⟩ :=
    Finset.exists_min_image (Finset.Icc 1 N) (rotationNearestDistance α) hne
  obtain ⟨hqpos, hqN⟩ := Finset.mem_Icc.mp hq
  refine ⟨q, hqpos, hqN, ?_⟩
  intro h hh hhN
  exact hmin h (Finset.mem_Icc.mpr ⟨hh, hhN⟩)

/-- The determinant spacing theorem specialized to the actual nearest
integers, rather than an unspecified approximation family. -/
theorem rotationNearestDistance_minimum_spacing {α : ℝ} (hα : Irrational α)
    {h q : ℕ} (hh : 0 < h) (hhq : h < q)
    (hminimum : rotationNearestDistance α q ≤ rotationNearestDistance α h) :
    1 / (2 * (q : ℝ)) < rotationNearestDistance α h := by
  exact integer_approximation_minimum_spacing α h q
    (round ((h : ℝ) * α)) (round ((q : ℝ) * α)) hh hhq
    (rotationNearestDistance_pos hα (lt_trans hh hhq)) hminimum

/-- The nearest error at an index difference is bounded by the distance
between the corresponding centered representatives. -/
theorem rotationNearestDistance_sub_le_centered_distance (α : ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    rotationNearestDistance α (j - i) ≤
      |rotationCenteredError α j - rotationCenteredError α i| := by
  have h := rotationNearestDistance_le_integer_error α (j - i)
    (round ((j : ℝ) * α) - round ((i : ℝ) * α))
  have heq : ((j - i : ℕ) : ℝ) * α -
        ((round ((j : ℝ) * α) - round ((i : ℝ) * α) : ℤ) : ℝ) =
      rotationCenteredError α j - rotationCenteredError α i := by
    rw [Nat.cast_sub hij, Int.cast_sub]
    dsimp [rotationCenteredError]
    ring
  rwa [heq] at h

/-- All actual centered orbit points in an index block shorter than a
minimum denominator are separated as ordinary real numbers. -/
theorem rotationCenteredError_block_spacing {α : ℝ} (hα : Irrational α)
    {q : ℕ}
    (hminimum : ∀ h : ℕ, 0 < h → h < q →
      rotationNearestDistance α q ≤ rotationNearestDistance α h)
    {i j : ℕ} (hij : i < j) (hdiff : j - i < q) :
    1 / (2 * (q : ℝ)) <
      |rotationCenteredError α j - rotationCenteredError α i| := by
  have hdpos : 0 < j - i := Nat.sub_pos_of_lt hij
  exact lt_of_lt_of_le
    (rotationNearestDistance_minimum_spacing hα hdpos hdiff
      (hminimum (j - i) hdpos hdiff))
    (rotationNearestDistance_sub_le_centered_distance α (Nat.le_of_lt hij))

/-- A fully selected minimum denominator, with spacing for every block.
The sole assumption on the rotation parameter is irrationality. -/
theorem exists_rotationCenteredError_prefix_minimum_spacing {α : ℝ}
    (hα : Irrational α) {N : ℕ} (hN : 0 < N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧
      (∀ h : ℕ, 0 < h → h ≤ N →
        rotationNearestDistance α q ≤ rotationNearestDistance α h) ∧
      ∀ i j : ℕ, i < j → j - i < q →
        1 / (2 * (q : ℝ)) <
          |rotationCenteredError α j - rotationCenteredError α i| := by
  obtain ⟨q, hq, hqN, hminimum⟩ :=
    exists_rotationNearestDistance_minimum α hN
  refine ⟨q, hq, hqN, hminimum, ?_⟩
  intro i j hij hdiff
  apply rotationCenteredError_block_spacing hα (q := q) ?_ hij hdiff
  intro h hh hhq
  exact hminimum h hh (le_trans (Nat.le_of_lt hhq) hqN)

/-- Positivity of the actual nearest errors at every positive index already
characterizes irrationality; there is no additional arithmetic hypothesis. -/
theorem irrational_of_rotationNearestDistance_pos {α : ℝ}
    (hpos : ∀ q : ℕ, 0 < q → 0 < rotationNearestDistance α q) :
    Irrational α := by
  apply (irrational_iff_ne_rational α).2
  intro a b hb heq
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hmul : α * (b : ℝ) = (a : ℝ) := (eq_div_iff hbR).mp heq
  have hq : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hqcast : (b.natAbs : ℝ) = |(b : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rcases le_total (0 : ℝ) (b : ℝ) with hbpos | hbneg
  · have hz : (b.natAbs : ℝ) * α - (a : ℝ) = 0 := by
      rw [hqcast, abs_of_nonneg hbpos]
      nlinarith
    have hle := rotationNearestDistance_le_integer_error α b.natAbs a
    rw [hz, abs_zero] at hle
    exact (not_le_of_gt (hpos b.natAbs hq)) hle
  · have hz : (b.natAbs : ℝ) * α - ((-a : ℤ) : ℝ) = 0 := by
      rw [hqcast, abs_of_nonpos hbneg, Int.cast_neg]
      nlinarith
    have hle := rotationNearestDistance_le_integer_error α b.natAbs (-a)
    rw [hz, abs_zero] at hle
    exact (not_le_of_gt (hpos b.natAbs hq)) hle

end RiemannResearch.Analysis
