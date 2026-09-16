import RiemannResearch.RH.CommonScaleRoughPackets
import RiemannResearch.RH.ArithmeticChargeEscape
import RiemannResearch.RH.BalancedContinuousCoordinates

/-!
# The fifth common-scale charge is forced by approximation to one

Source: user-provided `RH_Minimal_Seeds_Continuation_20260916.md`, Section 11,
equations (11.8)--(11.12). The fifth rough-component charge is the sum of the
actual physical remainder coefficients at `5,10,15,30`. Convergence in the
actual Pareto Hilbert space forces its limit to `1/15`; that limit is proved
here, rather than assumed as a domain-specific norm hypothesis.

For squarefree finite remainder packets, these four indices comprise the
entire component whose rough root is five. The divergence theorem permits
arbitrary other signed repair coefficients, including the root-one charge.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter FiniteSeedComponentCharge
noncomputable section

/-- Extract the four physical coefficients in the squarefree rough-five component. -/
def fifthRoughComponentCharge (f : ThresholdHilbert) : ℝ :=
  -componentCharge (smoothChargeSet 5 0) (hilbertSequence f)

theorem fifthRoughComponentCharge_eq_four (f : ThresholdHilbert) :
    fifthRoughComponentCharge f =
      physicalRemainderCoefficient 5 (hilbertSequence f) +
      physicalRemainderCoefficient 10 (hilbertSequence f) +
      physicalRemainderCoefficient 15 (hilbertSequence f) +
      physicalRemainderCoefficient 30 (hilbertSequence f) := by
  have hcut : smoothChargeSet 5 0 = {5, 10, 15, 30} := by decide
  simp [fifthRoughComponentCharge, componentCharge, hcut,
    physicalRemainderCoefficient]
  <;> ring

/-- Actual Hilbert approximation forces the exact nonzero fifth charge.
Finite support, squarefreeness, and any RH assumption are unnecessary for
this four-coordinate continuity statement. -/
theorem fifthRoughComponentCharge_tendsto
    (P : ℕ → ThresholdHilbert) (hP : Tendsto P atTop (nhds hilbertOne)) :
    Tendsto (fun j => fifthRoughComponentCharge (P j)) atTop (nhds (1 / 15 : ℝ)) := by
  have hpoint (n : ℕ) (hn : 0 < n) :
      Tendsto (fun j => hilbertSequence (P j) n) atTop (nhds (1 : ℝ)) := by
    have h := ((anchoredEvaluationCLM n).continuous.tendsto hilbertOne).comp hP
    change Tendsto (fun j => anchoredEvaluationCLM n (P j)) atTop
      (nhds (anchoredEvaluationCLM n hilbertOne)) at h
    simpa only [anchoredEvaluationCLM_apply, hilbertOne_sequence, zeroAnchor,
      if_neg (Nat.ne_of_gt hn)] using h
  have hcut : smoothChargeSet 5 0 = {5, 10, 15, 30} := by decide
  have hpos (d : ℕ) (hd : d ∈ smoothChargeSet 5 0) : 0 < d := by
    rw [hcut] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> omega
  have hsignal : componentSignal (smoothChargeSet 5 0) = -(1 / 15 : ℝ) := by
    rw [smoothChargeSet_signal 5 0 (by norm_num) (by norm_num)]
    have hm := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)
    norm_num [hm]
  have h := componentCharge_tendsto_target
    (F := fun j => hilbertSequence (P j))
    (fun j => hilbertSequence_zero (P j)) hpoint (smoothChargeSet 5 0) hpos
  simpa [fifthRoughComponentCharge, hsignal] using h.neg

/-- A convergent full-family approximation forces divergence of any common
outward packet carrying its actual fifth rough-component charge.
The identification hypothesis is an exact coefficient formula, not a norm
bound or a nonvanishing-limit assumption. -/
theorem commonScaleRoughPacket_norm_tendsto_of_approximation
    (P : ℕ → ThresholdHilbert) (hP : Tendsto P atTop (nhds hilbertOne))
    (A : ℕ → ℕ) (hA : ∀ j, 2 ≤ A j) (hAinf : Tendsto A atTop atTop)
    (s : ℕ → Finset ℕ+) (q : ℕ → ℕ+ → ℝ)
    (hs : ∀ j u, u ∈ s j → Nat.Coprime (u : ℕ) 6)
    (hq : ∀ j, (if (5 : ℕ+) ∈ s j then q j 5 else 0) =
      fifthRoughComponentCharge (P j)) :
    Tendsto (fun j =>
      ‖commonScaleRoughPacket (A j) (by have := hA j; omega) (s j) (q j)‖)
      atTop atTop := by
  apply commonScaleRoughPacket_norm_tendsto_atTop A hA hAinf s q hs
    (r := (1 / 15 : ℝ)) (by norm_num)
  simpa only [hq] using fifthRoughComponentCharge_tendsto P hP

/-- The repaired approximants themselves escape to infinity. This is the
construction-specific obstruction (11.12), with its charge limit discharged. -/
theorem commonScale_repaired_norm_tendsto_of_approximation
    (P : ℕ → ThresholdHilbert) (hP : Tendsto P atTop (nhds hilbertOne))
    (A : ℕ → ℕ) (hA : ∀ j, 2 ≤ A j) (hAinf : Tendsto A atTop atTop)
    (s : ℕ → Finset ℕ+) (q : ℕ → ℕ+ → ℝ)
    (hs : ∀ j u, u ∈ s j → Nat.Coprime (u : ℕ) 6)
    (hq : ∀ j, (if (5 : ℕ+) ∈ s j then q j 5 else 0) =
      fifthRoughComponentCharge (P j)) :
    Tendsto (fun j =>
      ‖P j - commonScaleRoughPacket (A j) (by have := hA j; omega) (s j) (q j)‖)
      atTop atTop := by
  have hC := commonScaleRoughPacket_norm_tendsto_of_approximation
    P hP A hA hAinf s q hs hq
  have hbounded : ∀ᶠ j in atTop, ‖P j‖ ≤ ‖hilbertOne‖ + 1 := by
    have h := hP.norm.eventually
      (Iio_mem_nhds (by linarith : ‖hilbertOne‖ < ‖hilbertOne‖ + 1))
    exact h.mono (fun j hj => le_of_lt hj)
  exact commonScale_repaired_norm_tendsto_atTop P
    (fun j => commonScaleRoughPacket (A j) (by have := hA j; omega) (s j) (q j))
    hC hbounded

end
end RiemannResearch.RH.Pareto
