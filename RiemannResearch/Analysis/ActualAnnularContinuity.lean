import RiemannResearch.Analysis.ActualAnnularTruncationMembership

/-!
# Continuity of the actual annular prime vector

Finite support permits local fixed-cutoff replacement at every positive
scale. Below 1 the actual vector is exactly its linear centering. These
facts give global raw-function continuity and measurability, with no energy
or prime-correlation hypothesis. Source: the exact annular support identity.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.WeightedMellinTopology
open RiemannResearch.RH
open RiemannResearch.RH.AnnularPrimePair

private theorem actualPrimeSignal_eq_fixed_cutoff_pos {x X : ℝ}
    (hx : 0 < x) (hX : x ≤ X) :
    actualPrimeSignal x = annularPrimeFinite (indices X) x := by
  unfold actualPrimeSignal annularPrimeFinite
  congr 1
  apply Finset.sum_subset (indices_mono hX)
  intro n hn hnnot
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnf : Nat.floor x < n := by
    by_contra h
    exact hnnot (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
  have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnf
  have hr : 1 ≤ (n : ℝ) / x :=
    (le_div_iff₀ hx).mpr (by simpa using hxn.le)
  rw [annularArithmeticWeight_eq_zero_of_one_le hr]
  exact mul_zero _

theorem actualAnnularVector_continuous : Continuous actualAnnularVector := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hc : ContinuousAt
        (fun y : ℝ => (annularPrimeFinite (indices (x + 1)) y : ℂ)) x := by
      apply Complex.continuous_ofReal.continuousAt.comp
      have hp : ContinuousOn (annularPrimeFinite (indices (x + 1))) (Ioi (0 : ℝ)) := by
        unfold annularPrimeFinite
        apply ContinuousOn.sub
        · apply continuousOn_finsetSum
          intro n hn
          exact continuousOn_const.mul
            (continuous_annularArithmeticWeight.comp_continuousOn'
              (continuousOn_const.div continuousOn_id
                (fun y hy => ne_of_gt hy)))
        · exact continuousOn_const.mul continuousOn_id
      exact hp.continuousAt (isOpen_Ioi.mem_nhds hx)
    have he : actualAnnularVector =ᶠ[𝓝 x]
        (fun y : ℝ => (annularPrimeFinite (indices (x + 1)) y : ℂ)) := by
      have hi : Ioo 0 (x + 1) ∈ 𝓝 x :=
        isOpen_Ioo.mem_nhds ⟨hx, by linarith⟩
      filter_upwards [hi] with y hy
      exact congrArg (fun r : ℝ => (r : ℂ))
        (actualPrimeSignal_eq_fixed_cutoff_pos hy.1 hy.2.le)
    exact hc.congr_of_eventuallyEq he
  · have hc : ContinuousAt (fun y : ℝ => (-(7/64:ℝ) * y : ℂ)) x :=
      continuousAt_const.mul Complex.continuous_ofReal.continuousAt
    have he : actualAnnularVector =ᶠ[𝓝 x]
        (fun y : ℝ => (-(7/64:ℝ) * y : ℂ)) := by
      have hi : Iio (1 : ℝ) ∈ 𝓝 x := Iio_mem_nhds (by linarith)
      filter_upwards [hi] with y hy
      have hf : Nat.floor y = 0 := Nat.floor_eq_zero.mpr hy
      simp [actualAnnularVector, actualPrimeSignal, annularPrimeFinite, indices, hf]
    exact hc.congr_of_eventuallyEq he

theorem actualAnnularVector_measurable : Measurable actualAnnularVector :=
  actualAnnularVector_continuous.measurable

end RiemannResearch.Analysis.WeightedMellinTopology
