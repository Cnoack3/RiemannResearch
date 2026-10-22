import RiemannResearch.RH.ParetoCompactHead
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Strong convergence of the actual physical Pareto cutoffs

The cutoffs exhaust every fixed Hilbert vector. Consequently the physical
tail also vanishes for every strongly convergent moving vector sequence,
including cumulative finite projection optimizers. No arithmetic or RH
premise is used, and no claim is made about the complete arithmetic trial tail.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The head energy is exactly the first N physical weighted squares. -/
theorem compactHead_norm_sq_eq_physical_sum (N : ℕ) (f : ThresholdHilbert) :
    ‖compactHead N f‖ ^ 2 =
      ∑ j ∈ Finset.range N, paretoWeight j * hilbertGibbsPhysical f j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hilbertGibbs_inner_physical]
  calc
    _ = ∑ j ∈ Finset.range N, paretoWeight j *
        (hilbertGibbsPhysical (compactHead N f) j *
          hilbertGibbsPhysical (compactHead N f) j) := by
      apply tsum_eq_sum
      intro j hj
      rw [compactHead_coordinate, if_neg (by simpa using hj)]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [compactHead_coordinate, if_pos (Finset.mem_range.mp hj)]
      ring

/-- The complementary orthogonal restriction has norm at most one. -/
theorem compactHead_tail_norm_le (N : ℕ) (f : ThresholdHilbert) :
    ‖f - compactHead N f‖ ≤ ‖f‖ := by
  nlinarith [compactHead_pythagoras N f,
    sq_nonneg ‖compactHead N f‖,
    norm_nonneg (f - compactHead N f), norm_nonneg f]

/-- Exhausting physical head energies recover every fixed vector's full energy. -/
theorem compactHead_norm_sq_tendsto (f : ThresholdHilbert) :
    Tendsto (fun N => ‖compactHead N f‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) := by
  have hsum := (hilbertGibbsPhysical_square_summable f).hasSum.tendsto_sum_nat
  have htotal :
      (∑' j, paretoWeight j * hilbertGibbsPhysical f j ^ 2) = ‖f‖ ^ 2 := by
    simp only [hilbertGibbsPhysical_square, hilbert_norm_sq]
  simpa only [compactHead_norm_sq_eq_physical_sum, htotal] using hsum

/-- Every fixed vector has vanishing complementary physical tail energy. -/
theorem compactHead_tail_energy_tendsto_zero (f : ThresholdHilbert) :
    Tendsto (fun N => ‖f - compactHead N f‖ ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun N => ‖f‖ ^ 2 - ‖compactHead N f‖ ^ 2) atTop
      (𝓝 (‖f‖ ^ 2 - ‖f‖ ^ 2)) :=
    tendsto_const_nhds.sub (compactHead_norm_sq_tendsto f)
  have he (N : ℕ) : ‖f - compactHead N f‖ ^ 2 =
      ‖f‖ ^ 2 - ‖compactHead N f‖ ^ 2 := by
    linarith [compactHead_pythagoras N f]
  simpa only [← he, sub_self] using h

/-- Every fixed vector has vanishing complementary physical tail norm. -/
theorem compactHead_tail_norm_tendsto_zero (f : ThresholdHilbert) :
    Tendsto (fun N => ‖f - compactHead N f‖) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    (compactHead_tail_energy_tendsto_zero f)
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm,
    Real.sqrt_zero] using h

/-- Actual physical cutoffs converge strongly to the identity. -/
theorem compactHead_tendsto (f : ThresholdHilbert) :
    Tendsto (fun N => compactHead N f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using compactHead_tail_norm_tendsto_zero f

/-- Quantitative moving-vector tail control separates convergence error from
the fixed limiting vector's physical tail. -/
theorem compactHead_moving_tail_norm_le (N : ℕ) (f g : ThresholdHilbert) :
    ‖f - compactHead N f‖ ≤ ‖f - g‖ + ‖g - compactHead N g‖ := by
  have he : f - compactHead N f =
      ((f-g) - compactHead N (f-g)) + (g - compactHead N g) := by
    rw [compactHead_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans
    (by simpa only [add_comm] using
      add_le_add_right (compactHead_tail_norm_le N (f-g)) ‖g-compactHead N g‖)

/-- The growing physical cutoff captures every strongly convergent moving
sequence, even when its limit is not the target vector. -/
theorem compactHead_moving_tail_norm_tendsto_zero
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun N => ‖f N - compactHead N (f N)‖) atTop (𝓝 0) := by
  have hmajor := (tendsto_iff_norm_sub_tendsto_zero.mp hf).add
    (compactHead_tail_norm_tendsto_zero g)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => compactHead_moving_tail_norm_le N (f N) g)
  simpa only [Function.comp_def, zero_add] using hmajor

theorem compactHead_moving_tail_energy_tendsto_zero
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun N => ‖f N - compactHead N (f N)‖ ^ 2) atTop (𝓝 0) := by
  simpa only [zero_pow (by decide : 2 ≠ 0)] using
    (compactHead_moving_tail_norm_tendsto_zero f g hf).pow 2

/-- The same moving-vector result allows any cofinal physical cutoff. -/
theorem compactHead_moving_cofinal_tail_norm_tendsto_zero
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) (M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => ‖f n - compactHead (M n) (f n)‖) atTop (𝓝 0) := by
  have hmajor := (tendsto_iff_norm_sub_tendsto_zero.mp hf).add
    ((compactHead_tail_norm_tendsto_zero g).comp hM)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => compactHead_moving_tail_norm_le (M n) (f n) g)
  simpa only [Function.comp_def, zero_add] using hmajor

/-- Cofinal physical heads retain the same strong limit as the moving vector. -/
theorem compactHead_moving_cofinal_tendsto
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) (M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => compactHead (M n) (f n)) atTop (𝓝 g) := by
  have ht : Tendsto (fun n => f n - compactHead (M n) (f n)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using
      compactHead_moving_cofinal_tail_norm_tendsto_zero f g hf M hM
  have he (n : ℕ) : f n - (f n - compactHead (M n) (f n)) =
      compactHead (M n) (f n) := by abel
  simpa only [he, sub_zero] using hf.sub ht

namespace CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Cumulative legal stage optimizers converge for every target, without
requiring that the target lie in the closed legal span. -/
theorem finiteOptimizer_tendsto (v : ThresholdHilbert) :
    Tendsto (fun n => (finiteSpace n).starProjection v) atTop
      (𝓝 (closedSpace.starProjection v)) :=
  walkProjection_tendsto residueAtom id Function.surjective_id v

/-- Every cofinal optimizer sequence has vanishing complete physical tail
under every cofinal physical cutoff. This unconditional tightness concerns
the optimal projection, and does not imply arithmetic trial tightness. -/
theorem actualOptimizer_physicalTail_energy_tendsto_zero
    (v : ThresholdHilbert) (n N : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => ‖(finiteSpace (n k)).starProjection v -
      compactHead (N k) ((finiteSpace (n k)).starProjection v)‖ ^ 2)
      atTop (𝓝 0) := by
  have h := compactHead_moving_cofinal_tail_norm_tendsto_zero
    (fun k => (finiteSpace (n k)).starProjection v)
    (closedSpace.starProjection v) ((finiteOptimizer_tendsto v).comp hn) N hN
  simpa only [zero_pow (by decide : 2 ≠ 0)] using h.pow 2

end CoefficientStabilization

end RiemannResearch.RH.Pareto
