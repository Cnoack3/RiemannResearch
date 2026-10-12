import RiemannResearch.RH.MultiRangeDivisorCorrections
import RiemannResearch.RH.CRTLegalCoordinates

/-!
# Uniqueness of balanced divisor coordinates

The non-anchor coefficients are recovered by actual Möbius difference
functionals. No matrix independence or inverse is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative CRTBlock Probability.ConditionalIID

private theorem mobiusDifference_add_mul_general (m : ℕ)
    (F G : ℕ → ℝ) (a : ℝ) :
    mobiusDifference m (fun n => F n + a * G n) =
      mobiusDifference m F + a * mobiusDifference m G := by
  unfold mobiusDifference
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

private theorem mobiusDifference_scaled_sum {ι : Type*} (m : ℕ)
    (s : Finset ι) (c : ι → ℝ) (f : ι → ℕ → ℝ) :
    mobiusDifference m (fun n => ∑ d ∈ s, c d * f d n) =
      ∑ d ∈ s, c d * mobiusDifference m (f d) := by
  unfold mobiusDifference
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro d hd
  ring

private theorem mobiusDifference_normalized (m d : ℕ) (hm : 1 < m) :
    mobiusDifference m (residueFraction d) = -(if m = d then 1 else 0) := by
  classical
  have he : normalizedResidueSynthesis {d} (fun _ => 1) = residueFraction d := by
    funext n
    simp [normalizedResidueSynthesis]
  simpa only [he, Finset.mem_singleton] using
    normalizedResidueSynthesis_mobiusDifference {d} (fun _ => 1) m hm

/-- Away from the anchor the true arithmetic charge reads the coefficient. -/
theorem divisorAnchorDirection_charge (A d m : ℕ)
    (hm : 1 < m) (hmA : m ≠ A) :
    mobiusDifference m (divisorAnchorDirection A d) = if m = d then 1 else 0 := by
  have he : divisorAnchorDirection A d = fun n =>
      -residueFraction d n + ((A : ℝ) / d) * residueFraction A n := by
    funext n
    unfold divisorAnchorDirection
    ring
  rw [he, mobiusDifference_add_mul_general]
  have hn : mobiusDifference m (fun n => -residueFraction d n) =
      -mobiusDifference m (residueFraction d) := by
    unfold mobiusDifference
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hn, mobiusDifference_normalized m d hm, mobiusDifference_normalized m A hm]
  simp [hmA]

/-- Exact recovery of every non-anchor coefficient, with its sign intact. -/
theorem divisorRangeCorrection_charge (A : ℕ) (s : Finset ℕ)
    (x : ℕ → ℝ) (m : ℕ) (hm : 1 < m) (hmA : m ≠ A) :
    mobiusDifference m (divisorRangeCorrection A s x) =
      if m ∈ s then x m else 0 := by
  classical
  unfold divisorRangeCorrection
  rw [mobiusDifference_scaled_sum]
  simp_rw [divisorAnchorDirection_charge A _ m hm hmA]
  simp [mul_ite]

/-- Coefficients on a finite anchor-free divisor set are unique. -/
theorem divisorRangeCorrection_coefficients_unique (A : ℕ) (s : Finset ℕ)
    (x y : ℕ → ℝ) (hs : ∀ d ∈ s, 1 < d ∧ d ≠ A)
    (h : divisorRangeCorrection A s x = divisorRangeCorrection A s y) :
    ∀ d ∈ s, x d = y d := by
  intro d hd
  have he := congrArg (mobiusDifference d) h
  rw [divisorRangeCorrection_charge A s x d (hs d hd).1 (hs d hd).2,
    divisorRangeCorrection_charge A s y d (hs d hd).1 (hs d hd).2,
    if_pos hd, if_pos hd] at he
  exact he

/-- The anchor-free chart is injective, including for an empty divisor set. -/
theorem divisorRangeCorrection_zero_iff (A : ℕ) (s : Finset ℕ)
    (x : ℕ → ℝ) (hs : ∀ d ∈ s, 1 < d ∧ d ≠ A) :
    divisorRangeCorrection A s x = 0 ↔ ∀ d ∈ s, x d = 0 := by
  constructor
  · intro h d hd
    have he := congrArg (mobiusDifference d) h
    rw [divisorRangeCorrection_charge A s x d (hs d hd).1 (hs d hd).2,
      if_pos hd] at he
    simpa [mobiusDifference] using he
  · intro hx
    funext n
    change (∑ d ∈ s, x d * divisorAnchorDirection A d n) = 0
    apply Finset.sum_eq_zero
    intro d hd
    rw [hx d hd, zero_mul]

/-- Equality of interpolating witnesses forces equality of their coordinates. -/
theorem correctedMobiusHead_coefficients_unique (Y : ℕ) (s : Finset ℕ)
    (x y : ℕ → ℝ) (hY : 0 < Y) (hs : ∀ d ∈ s, Y + 1 < d)
    (h : correctedMobiusHead Y s x = correctedMobiusHead Y s y) :
    ∀ d ∈ s, x d = y d := by
  apply divisorRangeCorrection_coefficients_unique (Y + 1) s x y
  · intro d hd
    have := hs d hd
    omega
  · funext n
    have he := congrFun h n
    change canonicalMobiusHead Y n + divisorRangeCorrection (Y + 1) s x n =
      canonicalMobiusHead Y n + divisorRangeCorrection (Y + 1) s y n at he
    exact add_left_cancel he

end RiemannResearch.RH.Pareto
