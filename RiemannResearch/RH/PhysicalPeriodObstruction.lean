/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.MeanOnePeriodObstruction
import RiemannResearch.LinearAlgebra.MeanOneSchur

/-!
# Ordinary mean-one period obstruction for actual arithmetic packets

Source: actual packet specialization and reflection refinement developed in
the user-directed continuation of `CriticalZeroMeanOneAdvance20261008.md`,
Sections 4 and 5. Packet reflection and the ordinary period mean reuse
`ArithmeticPacketCore.packet_reflection_totient` and `synthesis_period_mean`.

The totient constraint is connected to the literal period sum. Actual packet
boundedness, periodicity and the zero at every common multiple are proved
inputs. Every progression mass and affine correction square is retained.
The resulting finite inverse-core floor does not prove saturation at -4*pi.
-/

namespace RiemannResearch.RH.Pareto.PhysicalPeriodObstruction
noncomputable section
open Matrix
open scoped BigOperators
open PhysicalPacketCore MeanOnePeriodObstruction

theorem synthesis_periodic (s : Finset ℕ) (c : s → ℝ) (L : ℕ)
    (hdiv : ∀ q ∈ s, q ∣ L) (k : ℕ) :
    synthesis s c (k + L) = synthesis s c k := by
  unfold synthesis FiniteSchur.combination
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  unfold ramanujanPacket
  apply Finset.sum_congr rfl
  intro a ha
  have haL : a ∣ L := dvd_trans (Nat.dvd_of_mem_divisors ha) (hdiv q.val q.property)
  have hr : residue a (k + L) = residue a k := by
    unfold residue
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd haL]
    simp
  rw [hr]

theorem synthesis_zero (s : Finset ℕ) (c : s → ℝ) : synthesis s c 0 = 0 :=
  synthesis_zero_at_common_multiple s c 0 (fun q _hq => dvd_zero q)

/-- Starting a period at 1 rather than at 0 retains the mean exactly. -/
theorem period_sum_shift (L : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hfL : f L = 0) :
    (∑ i : Fin L, f (i.val + 1)) = ∑ i : Fin L, f i.val := by
  have hs := Finset.sum_range_succ' f L
  rw [Finset.sum_range_succ] at hs
  simp only [hf0, hfL, add_zero, zero_add] at hs
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (i + 1)),
    Fin.sum_univ_eq_sum_range f]
  exact hs.symm

/-- The actual totient constraint gives the literal positive period sum L. -/
theorem synthesis_positive_period_sum (L : ℕ) (hL : 0 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    (∑ i : Fin L, synthesis s c (i.val + 1)) = (L : ℝ) := by
  have hm := synthesis_period_mean L s c hL hs hdiv
  rw [hc] at hm
  norm_num at hm
  have hLr : (L : ℝ) ≠ 0 := by positivity
  have hsum : (∑ i : Fin L, synthesis s c i.val) = (L : ℝ) := by
    simpa only [one_mul] using (div_eq_iff hLr).mp hm
  rw [period_sum_shift L (synthesis s c) (synthesis_zero s c)
    (synthesis_zero_at_common_multiple s c L hdiv), hsum]

/-- The full physical affine square at every ordinary mean-one coefficient
vector. All arithmetic hypotheses other than the coefficient constraint are
discharged by the actual packet definitions. -/
theorem synthesis_meanOne_period_completion (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    paretoError (synthesis s c) = progressionWeight L L + 1 / reciprocalMass L +
      ∑ i : Fin (L - 1), progressionWeight L (i.val + 1) *
        (1 - synthesis s c (i.val + 1) +
          1 / (reciprocalMass L * progressionWeight L (i.val + 1))) ^ 2 := by
  exact physical_meanOne_completion L hL (synthesis s c) (synthesis_bounded s c)
    (synthesis_zero s c) (synthesis_periodic s c L hdiv)
    (synthesis_positive_period_sum L (by omega) s c hs hdiv hc)

theorem synthesis_meanOne_period_lower_bound (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    progressionWeight L L + 1 / reciprocalMass L ≤ paretoError (synthesis s c) := by
  exact physical_meanOne_lower_bound L hL (synthesis s c) (synthesis_bounded s c)
    (synthesis_zero s c) (synthesis_periodic s c L hdiv)
    (synthesis_positive_period_sum L (by omega) s c hs hdiv hc)

theorem synthesis_meanOne_period_explicit_lower_bound (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    progressionWeight L L + 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)) ≤
      paretoError (synthesis s c) := by
  exact physical_meanOne_explicit_lower_bound L hL (synthesis s c) (synthesis_bounded s c)
    (synthesis_zero s c) (synthesis_periodic s c L hdiv)
    (synthesis_positive_period_sum L (by omega) s c hs hdiv hc)

/-- The full reflection law of the actual divisor-sum packet synthesis. -/
theorem synthesis_reflection (L : ℕ) (s : Finset ℕ) (c : s → ℝ)
    (hs : ∀ q ∈ s, 1 < q) (hdiv : ∀ q ∈ s, q ∣ L)
    (k : ℕ) (hk : k < L) :
    synthesis s c k + synthesis s c (L - 1 - k) = ramanujanTotientVector s ⬝ᵥ c := by
  unfold synthesis FiniteSchur.combination
  rw [← Finset.sum_add_distrib]
  unfold dotProduct ramanujanTotientVector
  apply Finset.sum_congr rfl
  intro q hq
  have hr := packet_reflection_totient L q.val k (hs q.val q.property)
    (hdiv q.val q.property) hk
  nlinarith only [congrArg (fun x : ℝ => c q * x) hr]

/-- At ordinary mean one, the last nonzero period class is forced to value 2. -/
theorem synthesis_meanOne_last_value (L : ℕ) (hL : 0 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    synthesis s c (L - 1) = 2 := by
  have hr := synthesis_reflection L s c hs hdiv 0 hL
  simpa only [synthesis_zero, zero_add, Nat.sub_zero, hc] using hr

/-- The packet reflection supplies a stronger complete-weight floor than the
ordinary mean constraint alone: both forced period classes remain visible. -/
theorem synthesis_meanOne_reflection_lower_bound (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    progressionWeight L L + progressionWeight L (L - 1) ≤ paretoError (synthesis s c) := by
  classical
  rw [period_error_split L hL (synthesis s c) (synthesis_bounded s c)
    (synthesis_zero s c) (synthesis_periodic s c L hdiv)]
  apply add_le_add_right
  let j : Fin (L - 1) := ⟨L - 2, by omega⟩
  have hj : j.val + 1 = L - 1 := by dsimp [j]; omega
  have hb := Finset.single_le_sum
    (fun i (hi : i ∈ (Finset.univ : Finset (Fin (L - 1)))) =>
      mul_nonneg (progressionWeight_pos L (i.val + 1) (by omega) (by omega)).le
        (sq_nonneg (1 - synthesis s c (i.val + 1))))
    (Finset.mem_univ j)
  rw [hj, synthesis_meanOne_last_value L (by omega) s c hs hdiv hc] at hb
  norm_num at hb
  exact hb

/-- The actual reflection floor dominates the generic affine mean floor. -/
theorem reflection_floor_dominates_affine (L : ℕ) (hL : 1 < L) :
    1 / reciprocalMass L ≤ progressionWeight L (L - 1) := by
  classical
  let j : Fin (L - 1) := ⟨L - 2, by omega⟩
  have hj : j.val + 1 = L - 1 := by dsimp [j]; omega
  have hw := progressionWeight_pos L (L - 1) (by omega) (by omega)
  have hs := Finset.single_le_sum
    (fun i (hi : i ∈ (Finset.univ : Finset (Fin (L - 1)))) =>
      (one_div_pos.mpr (progressionWeight_pos L (i.val + 1) (by omega) (by omega))).le)
    (Finset.mem_univ j)
  rw [hj] at hs
  change 1 / progressionWeight L (L - 1) ≤ reciprocalMass L at hs
  have hm := mul_le_mul_of_nonneg_left hs hw.le
  have hunit : progressionWeight L (L - 1) * (1 / progressionWeight L (L - 1)) = 1 := by
    field_simp [ne_of_gt hw]
  rw [hunit] at hm
  exact (div_le_iff₀ (reciprocalMass_pos L hL)).mpr hm

/-- A rational envelope for the two complete forced-class masses. -/
theorem reflection_floor_ge_explicit (L : ℕ) (hL : 1 < L) :
    2 / ((L : ℝ) ^ 2 - 1) ≤ progressionWeight L L + progressionWeight L (L - 1) := by
  have hfirst := positiveWeight_le_progressionWeight L L (by omega)
  have hprev := positiveWeight_le_progressionWeight L (L - 1) (by omega)
  have hLr : (1 : ℝ) < L := by exact_mod_cast hL
  have hLn : 0 < (L : ℝ) - 1 := by linarith
  have hLp : 0 < (L : ℝ) + 1 := by linarith
  have hsq : (L : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have he : positiveWeight L + positiveWeight (L - 1) = 2 / ((L : ℝ) ^ 2 - 1) := by
    unfold positiveWeight
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    push_cast
    field_simp [ne_of_gt (by linarith : (0 : ℝ) < L), ne_of_gt hLn, ne_of_gt hLp, hsq]
    <;> ring
  rw [← he]
  exact add_le_add hfirst hprev

theorem synthesis_meanOne_reflection_explicit_lower_bound (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (c : s → ℝ) (hs : ∀ q ∈ s, 1 < q)
    (hdiv : ∀ q ∈ s, q ∣ L) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    2 / ((L : ℝ) ^ 2 - 1) ≤ paretoError (synthesis s c) :=
  (reflection_floor_ge_explicit L hL).trans
    (synthesis_meanOne_reflection_lower_bound L hL s c hs hdiv hc)

/-- Actual reflection yields a denominator-positive, complete-mass inverse
charge floor at the constrained physical optimizer. -/
theorem inverseCharge_reflection_floor (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (hdiv : ∀ q ∈ s, q ∣ L) :
    progressionWeight L L + progressionWeight L (L - 1) < 1 ∧
      inverseCharge s ≤ -4 * Real.pi /
        (1 - (progressionWeight L L + progressionWeight L (L - 1))) := by
  have he := synthesis_meanOne_reflection_lower_bound L hL s (constrainedOptimizer s)
    hs hdiv (constrainedOptimizer_totient s hs hodd)
  rw [constrainedOptimizer_error s hs hodd] at he
  have hn : 4 * Real.pi / inverseCharge s < 0 :=
    div_neg_of_pos_of_neg (by positivity) (inverseCharge_neg s hs hodd)
  have hlt : progressionWeight L L + progressionWeight L (L - 1) < 1 := by linarith
  refine ⟨hlt, ?_⟩
  have herror : progressionWeight L L + progressionWeight L (L - 1) ≤
      1 - 4 * Real.pi / (-inverseCharge s) := by
    simpa only [div_neg, sub_neg_eq_add] using he
  have hb := RiemannResearch.LinearAlgebra.MeanOneSchur.inverseCharge_bound_of_error_lower
    Real.pi (-inverseCharge s) (progressionWeight L L + progressionWeight L (L - 1))
    (neg_pos.mpr (inverseCharge_neg s hs hodd)) hlt herror
  have hneg := neg_le_neg hb
  simpa only [neg_neg, neg_div, neg_mul] using hneg

theorem inverseCharge_reflection_explicit_floor (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (hdiv : ∀ q ∈ s, q ∣ L) :
    inverseCharge s ≤ -4 * Real.pi / (1 - 2 / ((L : ℝ) ^ 2 - 1)) := by
  have he := synthesis_meanOne_reflection_explicit_lower_bound L hL s (constrainedOptimizer s)
    hs hdiv (constrainedOptimizer_totient s hs hodd)
  rw [constrainedOptimizer_error s hs hodd] at he
  have hn : 4 * Real.pi / inverseCharge s < 0 :=
    div_neg_of_pos_of_neg (by positivity) (inverseCharge_neg s hs hodd)
  have hlt : 2 / ((L : ℝ) ^ 2 - 1) < 1 := by linarith
  have herror : 2 / ((L : ℝ) ^ 2 - 1) ≤ 1 - 4 * Real.pi / (-inverseCharge s) := by
    simpa only [div_neg, sub_neg_eq_add] using he
  have hb := RiemannResearch.LinearAlgebra.MeanOneSchur.inverseCharge_bound_of_error_lower
    Real.pi (-inverseCharge s) (2 / ((L : ℝ) ^ 2 - 1))
    (neg_pos.mpr (inverseCharge_neg s hs hodd)) hlt herror
  have hneg := neg_le_neg hb
  simpa only [neg_neg, neg_div, neg_mul] using hneg

/-- The complete-period lower floor is strictly below one because it is
bounded above by the actual constrained optimum, whose inverse charge is
negative. This denominator positivity is proved rather than assumed. -/
theorem complete_period_floor_lt_one (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (hdiv : ∀ q ∈ s, q ∣ L) :
    progressionWeight L L + 1 / reciprocalMass L < 1 := by
  have he := synthesis_meanOne_period_lower_bound L hL s (constrainedOptimizer s)
    hs hdiv (constrainedOptimizer_totient s hs hodd)
  rw [constrainedOptimizer_error s hs hodd] at he
  have hn : 4 * Real.pi / inverseCharge s < 0 :=
    div_neg_of_pos_of_neg (by positivity) (inverseCharge_neg s hs hodd)
  linarith

/-- Actual inverse-core charge floor, strengthened by the affine mean-one
obstruction. The complete infinite progression mass is retained. -/
theorem inverseCharge_complete_period_floor (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (hdiv : ∀ q ∈ s, q ∣ L) :
    inverseCharge s ≤ -4 * Real.pi /
      (1 - (progressionWeight L L + 1 / reciprocalMass L)) := by
  have he := synthesis_meanOne_period_lower_bound L hL s (constrainedOptimizer s)
    hs hdiv (constrainedOptimizer_totient s hs hodd)
  rw [constrainedOptimizer_error s hs hodd] at he
  have hgamma : 0 < -inverseCharge s := neg_pos.mpr (inverseCharge_neg s hs hodd)
  have herror : progressionWeight L L + 1 / reciprocalMass L ≤
      1 - 4 * Real.pi / (-inverseCharge s) := by
    simpa only [div_neg, sub_neg_eq_add] using he
  have hb := RiemannResearch.LinearAlgebra.MeanOneSchur.inverseCharge_bound_of_error_lower
    Real.pi (-inverseCharge s) (progressionWeight L L + 1 / reciprocalMass L)
    hgamma (complete_period_floor_lt_one L hL s hs hodd hdiv) herror
  have hn := neg_le_neg hb
  simpa only [neg_neg, neg_div, neg_mul] using hn

theorem inverseCharge_explicit_period_floor (L : ℕ) (hL : 1 < L)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (hdiv : ∀ q ∈ s, q ∣ L) :
    inverseCharge s ≤ -4 * Real.pi /
      (1 - (progressionWeight L L + 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)))) := by
  have he := synthesis_meanOne_period_explicit_lower_bound L hL s (constrainedOptimizer s)
    hs hdiv (constrainedOptimizer_totient s hs hodd)
  rw [constrainedOptimizer_error s hs hodd] at he
  have hn : 4 * Real.pi / inverseCharge s < 0 :=
    div_neg_of_pos_of_neg (by positivity) (inverseCharge_neg s hs hodd)
  have hlt : progressionWeight L L + 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)) < 1 := by
    linarith
  have herror : progressionWeight L L + 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)) ≤
      1 - 4 * Real.pi / (-inverseCharge s) := by
    simpa only [div_neg, sub_neg_eq_add] using he
  have hb := RiemannResearch.LinearAlgebra.MeanOneSchur.inverseCharge_bound_of_error_lower
    Real.pi (-inverseCharge s)
      (progressionWeight L L + 3 / ((L : ℝ) * ((L : ℝ) ^ 2 - 1)))
    (neg_pos.mpr (inverseCharge_neg s hs hodd)) hlt herror
  have hneg := neg_le_neg hb
  simpa only [neg_neg, neg_div, neg_mul] using hneg

end
end RiemannResearch.RH.Pareto.PhysicalPeriodObstruction
