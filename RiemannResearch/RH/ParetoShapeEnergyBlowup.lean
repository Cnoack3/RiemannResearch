import RiemannResearch.RH.ParetoShapeThreshold
import RiemannResearch.Analysis.PointwiseEnergyDivergence

/-!
# Actual Mellin-energy blow-up at the critical Pareto shape

Finite-sum Fatou gives divergence of the actual complete energy, not only
divergence of an upper estimate. The proof applies at every positive real
part and survives deleting any finite number of physical cells.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ShapeCapacity

/-- For a fixed cell and parameter, the actual dual cell energy is
continuous in the positive Pareto shape. -/
theorem shapeMellinCellEnergy_continuousAt_shape (α a : ℝ) (s : ℂ)
    (hα : 0 < α) (ha : 0 < a) :
    ContinuousAt (fun β => shapeMellinCellEnergy β s a) α := by
  have hw : Continuous (fun β : ℝ => shapeCellWeight β a) := by
    unfold shapeCellWeight
    fun_prop (disch := positivity)
  exact continuousAt_const.div hw.continuousAt (shapeCellWeight_pos α a hα ha).ne'

/-- The actual complete Mellin energy tends to infinity as the shape
approaches `2 Re(s)` from below. No zero or RH premise occurs. This holds
after every finite cutoff, not merely for the full series. -/
theorem shapeMellinShiftEnergy_tendsto_atTop (s : ℂ) (hs : 0 < s.re) (k : ℕ) :
    Tendsto (fun α : ℝ => ∑' n : ℕ,
      shapeMellinCellEnergy α s (((n + k : ℕ) : ℝ) + 1))
      (𝓝[<] (2 * s.re)) atTop := by
  have hb : 0 < 2 * s.re := by positivity
  have hpos : ∀ᶠ α : ℝ in 𝓝[<] (2 * s.re), 0 < α :=
    (eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds
  have hbelow : ∀ᶠ α : ℝ in 𝓝[<] (2 * s.re), α < 2 * s.re :=
    self_mem_nhdsWithin
  apply RiemannResearch.Analysis.total_nonnegative_energy_tendsto_atTop_filter
    (𝓝[<] (2 * s.re))
    (fun α n => shapeMellinCellEnergy α s (((n + k : ℕ) : ℝ) + 1))
    (fun n => shapeMellinCellEnergy (2 * s.re) s (((n + k : ℕ) : ℝ) + 1))
  · filter_upwards [hpos] with α hα
    intro n
    exact shapeMellinCellEnergy_nonneg α s _ hα (by positivity)
  · intro n
    exact shapeMellinCellEnergy_nonneg (2 * s.re) s _ hb (by positivity)
  · filter_upwards [hpos, hbelow] with α hα hαb
    exact (shapeMellinShiftEnergy_summable_iff α s hα hs k).2 hαb
  · intro n
    exact (shapeMellinCellEnergy_continuousAt_shape (2 * s.re)
      (((n + k : ℕ) : ℝ) + 1) s hb (by positivity)).tendsto.mono_left
        nhdsWithin_le_nhds
  · rw [shapeMellinShiftEnergy_summable_iff (2 * s.re) s hb hs k]
    exact lt_irrefl _

/-- Normalization by the nonzero Mellin parameter leaves the genuine
boundary blow-up unchanged. -/
theorem normalizedShapeMellinShiftEnergy_tendsto_atTop
    (s : ℂ) (hs : 0 < s.re) (k : ℕ) :
    Tendsto (fun α : ℝ => ∑' n : ℕ,
      ‖mellinCellCertificate s (((n + k : ℕ) : ℝ) + 1)‖ ^ 2 /
        shapeCellWeight α (((n + k : ℕ) : ℝ) + 1))
      (𝓝[<] (2 * s.re)) atTop := by
  have hs0 : s ≠ 0 := by intro hz; simp [hz] at hs
  simp_rw [normalized_cell_energy_eq, tsum_div_const]
  exact (shapeMellinShiftEnergy_tendsto_atTop s hs k).atTop_div_const
    (pow_pos (norm_pos_iff.mpr hs0) 2)

/-- In particular, every normalized critical-line certificate has
diverging tail energy as the Pareto shape increases to one. -/
theorem criticalNormalizedTailEnergy_tendsto_atTop (t : ℝ) :
    Tendsto (fun α : ℝ => ∑' n : ℕ,
      ‖mellinCellCertificate (MellinFrequency.criticalPoint t) ((n : ℝ) + 2)‖ ^ 2 /
        shapeCellWeight α ((n : ℝ) + 2)) (𝓝[<] (1 : ℝ)) atTop := by
  simpa only [MellinFrequency.criticalPoint_re,
    show 2 * (1 / 2 : ℝ) = 1 by norm_num,
    Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      normalizedShapeMellinShiftEnergy_tendsto_atTop (MellinFrequency.criticalPoint t)
        (by rw [MellinFrequency.criticalPoint_re]; norm_num) 1

end RiemannResearch.RH.Pareto.ShapeCapacity
