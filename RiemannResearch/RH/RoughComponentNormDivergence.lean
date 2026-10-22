import RiemannResearch.RH.RoughProfileBounds
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.Analysis.PointwiseEnergyDivergence

/-!
# A single nonzero rough limiting profile is outside the Pareto Hilbert space

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
section 7. The obstruction uses the actual four-floor arithmetic profile and
the actual weight 1/(n(n+1)); it is independent of RH.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators Topology
open Filter

noncomputable section

/-- The weighted energy of the prescribed rough profile has a strictly
positive limit at each distant coordinate. -/
theorem roughMobiusProfile_weighted_square_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => positiveWeight (n + 1) *
      ((ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q (n + 1)) ^ 2)
      atTop (𝓝 ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2))) := by
  have ht := (roughHeadProfile_weighted_square_tendsto q hq).const_mul
    ((ArithmeticFunction.moebius q : ℝ) ^ 2)
  convert ht using 1
  · funext n
    ring
  · ring

/-- Therefore no nonzero Möbius rough profile is square integrable. -/
theorem roughMobiusProfile_not_square_summable (q : ℕ) (hq : 0 < q)
    (hmu : ArithmeticFunction.moebius q ≠ 0) :
    ¬ Summable (fun n : ℕ => positiveWeight (n + 1) *
      ((ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q (n + 1)) ^ 2) := by
  intro hs
  have he := tendsto_nhds_unique
    (roughMobiusProfile_weighted_square_tendsto q hq) hs.tendsto_atTop_zero
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hmuR : (ArithmeticFunction.moebius q : ℝ) ≠ 0 := by exact_mod_cast hmu
  have hp : 0 < (ArithmeticFunction.moebius q : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2) :=
    div_pos (sq_pos_of_ne_zero hmuR) (by positivity)
  linarith

/-- There is no actual Hilbert vector with this forced component profile. -/
theorem roughMobiusProfile_not_in_paretoHilbert (q : ℕ) (hq : 0 < q)
    (hmu : ArithmeticFunction.moebius q ≠ 0) :
    ¬ ∃ f : ThresholdHilbert, ∀ n, 0 < n → hilbertSequence f n =
      (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q n := by
  rintro ⟨f, hf⟩
  have hs := (summable_nat_add_iff 1).2 (hilbertSequence_square_summable f)
  apply roughMobiusProfile_not_square_summable q hq hmu
  simpa only [hf _ (Nat.succ_pos _)] using hs

/-- Any sequence converging pointwise to the forced nonzero rough profile
has full Pareto square norm tending to infinity. -/
theorem roughMobiusProfile_pointwise_forces_energy_divergence
    (q : ℕ) (hq : 0 < q) (hmu : ArithmeticFunction.moebius q ≠ 0)
    (F : ℕ → ℕ → ℝ)
    (hs : ∀ j, Summable (fun n : ℕ => positiveWeight (n + 1) * F j (n + 1) ^ 2))
    (hp : ∀ n, 0 < n → Tendsto (fun j => F j n) atTop
      (𝓝 ((ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q n))) :
    Tendsto (fun j => ∑' n : ℕ, positiveWeight (n + 1) * F j (n + 1) ^ 2)
      atTop atTop := by
  apply RiemannResearch.Analysis.total_nonnegative_energy_tendsto_atTop
    (fun j n => positiveWeight (n + 1) * F j (n + 1) ^ 2)
    (fun n => positiveWeight (n + 1) *
      ((ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q (n + 1)) ^ 2)
  · intro j n
    exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)
  · intro n
    exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)
  · exact hs
  · intro n
    exact ((hp (n + 1) (Nat.succ_pos _)).pow 2).const_mul _
  · exact roughMobiusProfile_not_square_summable q hq hmu

end
end RiemannResearch.RH.Pareto
