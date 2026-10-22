/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoWeights

/-!
# Physical coordinates of the Pareto Hilbert space

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md.
These coordinate, summability, and pairing identities use the existing genuine
`ThresholdHilbert` carrier independently of the Gibbs kernel and operator.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Physical coordinates indexed from zero, as required by the Gibbs kernel. -/
def hilbertGibbsPhysical (f : ThresholdHilbert) (n : ℕ) : ℝ :=
  f n / Real.sqrt (paretoWeight n)

theorem hilbertGibbsPhysical_eq (f : ThresholdHilbert) (n : ℕ) :
    hilbertGibbsPhysical f n = hilbertSequence f (n+1) := rfl

theorem hilbertGibbsPhysical_square (f : ThresholdHilbert) (n : ℕ) :
    paretoWeight n * hilbertGibbsPhysical f n ^ 2 = (f n) ^ 2 := by
  simpa only [positiveWeight_succ, hilbertGibbsPhysical_eq] using
    hilbertSequence_weighted_square f n

theorem hilbertGibbsPhysical_square_summable (f : ThresholdHilbert) :
    Summable (fun n => paretoWeight n * hilbertGibbsPhysical f n ^ 2) := by
  simpa only [hilbertGibbsPhysical_square] using hilbert_coordinate_square_summable f

theorem hilbertGibbsPhysical_abs_summable (f : ThresholdHilbert) :
    Summable (fun n => paretoWeight n * |hilbertGibbsPhysical f n|) :=
  pareto_abs_summable_of_square (hilbertGibbsPhysical_square_summable f)

theorem hilbertGibbsPhysical_add (f g : ThresholdHilbert) :
    hilbertGibbsPhysical (f+g) = fun n => hilbertGibbsPhysical f n + hilbertGibbsPhysical g n := by
  funext n
  simp [hilbertGibbsPhysical, add_div]

theorem hilbertGibbsPhysical_smul (c : ℝ) (f : ThresholdHilbert) :
    hilbertGibbsPhysical (c • f) = fun n => c * hilbertGibbsPhysical f n := by
  funext n
  simp [hilbertGibbsPhysical, mul_div_assoc]

/-- The existing Hilbert target has physical value one on every index. -/
theorem hilbertGibbs_one_physical :
    hilbertGibbsPhysical hilbertOne = fun _ => 1 := by
  funext n
  rw [hilbertGibbsPhysical_eq, hilbertOne_sequence]
  simp [zeroAnchor]

/-- The existing Hilbert inner product is the full physical weighted pairing. -/
theorem hilbertGibbs_inner_physical (f g : ThresholdHilbert) :
    inner ℝ f g = ∑' n, paretoWeight n *
      (hilbertGibbsPhysical f n * hilbertGibbsPhysical g n) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply']
  change f n * g n = paretoWeight n *
    ((f n / Real.sqrt (paretoWeight n)) * (g n / Real.sqrt (paretoWeight n)))
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (paretoWeight_pos n).le]
  field_simp [ne_of_gt (paretoWeight_pos n)]

theorem hilbertGibbs_inner_one (f : ThresholdHilbert) :
    inner ℝ f hilbertOne = ∑' n, paretoWeight n * hilbertGibbsPhysical f n := by
  rw [hilbertGibbs_inner_physical, hilbertGibbs_one_physical]
  simp only [mul_one]

end
end RiemannResearch.RH.Pareto
