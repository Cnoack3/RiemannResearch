import RiemannResearch.RH.ExactHeadResidualTail

/-!
# Tail localization of Pareto dilation pairings

Source: the support-sensitive Cauchy--Schwarz argument in
`RH/Residual_Abel_Obstruction_20260924.md`, Section 1.
The argument is extended here to two arbitrary Pareto Hilbert vectors.
No mathematical novelty or RH conclusion is claimed.

A dilation by N+1 vanishes on the first N weighted coordinates. Thus only
the tail of the testing vector enters its correlation bound. Its squared
correlation divided by N+1 tends to zero without any arithmetic hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

theorem hilbertDilation_coordinate_eq_zero_of_lt
    (f : ThresholdHilbert) (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : n + 1 < m) :
    hilbertDilation m hm f n = 0 := by
  have hs : hilbertSequence (hilbertDilation m hm f) (n + 1) = 0 := by
    rw [hilbertDilation_sequence]
    simp [dilation, Nat.div_eq_of_lt hn]
  rw [hilbertSequence_succ] at hs
  exact (div_eq_zero_iff).mp hs |>.resolve_right (by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity)

theorem hilbertDilation_pairing_sq_le_tail
    (f g : ThresholdHilbert) (N : ℕ) :
    (inner ℝ f (hilbertDilation (N + 1) (by omega) g)) ^ 2 ≤
      ((N : ℝ) + 1) * ‖g‖ ^ 2 * ‖hilbertTailShift f N‖ ^ 2 := by
  have h := hilbertTailShift_inner_sq_le f
    (hilbertDilation (N + 1) (by omega) g) N
    (fun n hn => hilbertDilation_coordinate_eq_zero_of_lt g
      (N + 1) (by omega) n (by omega))
  rw [hilbertDilation_norm_sq] at h
  push_cast at h
  nlinarith [h]

theorem hilbertDilation_normalized_pairing_sq_tendsto_zero
    (f g : ThresholdHilbert) :
    Tendsto (fun N : ℕ =>
      (inner ℝ f (hilbertDilation (N + 1) (by omega) g)) ^ 2 /
        ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N => ‖g‖ ^ 2 * ‖hilbertTailShift f N‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using (hilbertTailShift_energy_tendsto_zero f).const_mul (‖g‖ ^ 2)
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2
  nlinarith [hilbertDilation_pairing_sq_le_tail f g N]

end RiemannResearch.RH.Pareto
