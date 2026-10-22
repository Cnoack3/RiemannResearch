import RiemannResearch.RH.ParetoSignedTails
import RiemannResearch.RH.NearbyDilationGram

/-!
# Automatic square-tail decay for actual Pareto Hilbert sequences

Source: Christian Noack's
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 25, Lemma 25.1. This file proves the exact squared form of the
pointwise Cauchy--Schwarz estimate and the resulting vanishing statement.
The extra absolute summability needed for certificate exclusion is not
deduced from this regularity.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The complete physical squared energy on indices at least `n`. -/
def signedTailEnergy (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' j, positiveWeight (j + n) * h (j + n) ^ 2

theorem signedTailEnergy_nonneg (h : ℕ → ℝ) (n : ℕ) :
    0 ≤ signedTailEnergy h n := by
  apply tsum_nonneg
  intro j
  exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)

theorem signedTailEnergy_tendsto_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Tendsto (signedTailEnergy h) atTop (nhds 0) := by
  have he (n : ℕ) : signedTailEnergy h n =
      (∑' k, positiveWeight k * h k ^ 2) -
        ∑ k ∈ Finset.range n, positiveWeight k * h k ^ 2 := by
    have hx := hs.sum_add_tsum_nat_add n
    change (∑ k ∈ Finset.range n, positiveWeight k * h k ^ 2) +
      signedTailEnergy h n = _ at hx
    linarith
  have ht := (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => ∑' k, positiveWeight k * h k ^ 2) atTop
      (nhds (∑' k, positiveWeight k * h k ^ 2))).sub hs.hasSum.tendsto_sum_nat
  simpa only [← he, sub_self] using ht

/-- Cauchy--Schwarz for the actual signed primitive, in exact squared form.
The zero coordinate is excluded because its Pareto mass is zero. -/
theorem signedTail_mul_sq_le_tailEnergy {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * signedTail h n ^ 2 ≤ signedTailEnergy h n := by
  have hE := (summable_nat_add_iff n).mpr hs
  have hb := (summable_nat_add_iff n).mpr (signedCoefficient_summable hs)
  have hw := (summable_nat_add_iff n).mpr positiveWeight_summable
  let c : ℝ := (n : ℝ) * signedTail h n
  have hquad :
      (∑' j, positiveWeight (j + n) * (h (j + n) - c) ^ 2) =
        signedTailEnergy h n - 2 * c * signedTail h n + c ^ 2 / (n : ℝ) := by
    calc
      _ = ∑' j, ((positiveWeight (j + n) * h (j + n) ^ 2 -
          (2 * c) * signedCoefficient h (j + n)) +
            c ^ 2 * positiveWeight (j + n)) := by
        apply tsum_congr
        intro j
        unfold signedCoefficient
        ring
      _ = _ := by
        rw [(hE.sub (hb.mul_left (2 * c))).tsum_add (hw.mul_left (c ^ 2)),
          hE.tsum_sub (hb.mul_left (2 * c)), tsum_mul_left, tsum_mul_left,
          positiveWeight_tail_tsum n hn]
        change signedTailEnergy h n - 2 * c * signedTail h n +
          c ^ 2 * (1 / (n : ℝ)) = _
        ring
  have hnn : (n : ℝ) ≠ 0 := by positivity
  have hc : c ^ 2 / (n : ℝ) = (n : ℝ) * signedTail h n ^ 2 := by
    dsimp [c]
    field_simp
  have hpos : 0 ≤ ∑' j, positiveWeight (j + n) * (h (j + n) - c) ^ 2 := by
    apply tsum_nonneg
    intro j
    exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)
  rw [hquad, hc] at hpos
  dsimp [c] at hpos
  nlinarith

/-- The squared version of `sqrt n * A_n → 0`, following from the
vanishing of the actual Hilbert energy tail. -/
theorem signedTail_mul_sq_tendsto_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Tendsto (fun n : ℕ => (n : ℝ) * signedTail h n ^ 2) atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)))
      (Filter.eventually_atTop.2 ⟨1, fun n hn =>
        signedTail_mul_sq_le_tailEnergy hs n (by omega)⟩)
      (signedTailEnergy_tendsto_zero hs)

end
end RiemannResearch.RH.Pareto
