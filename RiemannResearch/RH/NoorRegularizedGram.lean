import RiemannResearch.RH.NoorRegularizedApproximation
import RiemannResearch.Analysis.ShiftedLiftGram
import RiemannResearch.Analysis.NoorLogarithmGram

/-!
# Explicit arithmetic matrices and canonical finite shifted minimizers

Source: continuation of the user-provided
RH_Finite_Arithmetic_Shifted_Lifts_2026-09-24 handoff and the existing
forward_residue_decomposition. The latter identifies the actual residue
generators with Noor's logarithmic family; see NoorShiftedResidueDensity
for its source attribution. The matrix and lcm calculations here are
elementary deductions; no mathematical novelty is asserted.

All Gram and source entries use the complete Hilbert inner product.
The actual inverse matrix provides the unique finite minimizer, with
unconditional vanishing unscaled energy. The final RH implication still
has the explicit open divided-gap hypothesis hrate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.Noor
open RiemannResearch.Analysis.ShiftedLift
open CoefficientStabilization

theorem shiftedResidue_inner (i j : ℕ) :
    inner ℝ (forwardDifference (hardyCoordinates (residueAtom i)))
      (forwardDifference (hardyCoordinates (residueAtom j))) =
      (Real.log (i+2 : ℕ) * Real.log (j+2 : ℕ) +
        (∑' n : ℕ, 1 / (n : ℝ)^2) *
          (1 - 1 / (i+2 : ℕ) - 1 / (j+2 : ℕ) +
            ((i+2 : ℕ) : ℝ) * (j+2 : ℕ) /
              (Nat.lcm (i+2) (j+2) : ℝ)^2)) /
      (((i+2 : ℕ) : ℝ) * (j+2 : ℕ)) := by
  have hi : ((i+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj : ((j+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := congrArg₂ (fun x y : Space => inner ℝ x y)
    (forward_residue_decomposition i) (forward_residue_decomposition j)
  simp only [inner_smul_left, inner_smul_right, conj_trivial] at h
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial, lp.inner_single_left,
    lp.inner_single_right, logVector_apply, logSequence_zero, lp.single_apply_self] at h
  rw [logVector_inner (i+2) (j+2) (by omega) (by omega),
    logVector_inner 1 (j+2) (by omega) (by omega),
    logVector_inner (i+2) 1 (by omega) (by omega),
    logVector_inner 1 1 (by omega) (by omega)] at h
  simp only [Nat.lcm_one_left, Nat.lcm_one_right, Nat.cast_one, one_pow, div_one,
    one_mul, mul_one, inner_zero_left, inner_zero_right, real_inner_self_eq_norm_sq,
    norm_one, mul_zero, sub_zero, add_zero] at h
  have hL : ((Nat.lcm (i+2) (j+2) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.lcm_pos (by omega : 0 < i+2) (by omega : 0 < j+2))
  apply (eq_div_iff (mul_ne_zero hi hj)).mpr
  convert h using 1
  · ring
  · field_simp
    ring

end RiemannResearch.RH.Pareto.Noor

namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.ShiftedLift
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk
open CoefficientStabilization

def finiteLiftFamily (N : ℕ) (i : Fin N) : Space :=
  hardyCoordinates (residueAtom i.val)

theorem finiteLiftFamily_linearIndependent (N : ℕ) :
    LinearIndependent ℝ (finiteLiftFamily N) := by
  exact (residueAtom_linearIndependent.map'
    hardyCoordinates.toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr hardyCoordinates.injective)).comp
      (fun i : Fin N => i.val) Fin.val_injective

theorem finiteLiftSpace_eq_synthesisSpan (N : ℕ) :
    finiteLiftSpace N = synthesisSpan (finiteLiftFamily N) := rfl

def finiteShiftedGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  gramMatrix (fun i => difference rightShiftLinear (finiteLiftFamily N i))

def finiteUnshiftedGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  gramMatrix (finiteLiftFamily N)

def finiteShiftedSource (N : ℕ) : Fin N → ℝ :=
  cross (fun i => difference rightShiftLinear (finiteLiftFamily N i)) (finiteTarget N)

def finiteRegularizedGram (N : ℕ) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  finiteShiftedGram N + t^2 • finiteUnshiftedGram N

theorem finiteRegularizedGram_posDef (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (finiteRegularizedGram N t).PosDef :=
  regularizedGram_posDef rightShiftLinear (finiteLiftFamily_linearIndependent N) t ht

theorem finiteMinimum_eq_inverseGram (N : ℕ) (t : ℝ) (ht : 0 < t) :
    finiteMinimum N t = energy N -
      dotProduct (finiteShiftedSource N) ((finiteRegularizedGram N t)⁻¹.mulVec (finiteShiftedSource N)) := by
  have h := regularizedInf_eq_inverseGram rightShiftLinear
    (finiteLiftFamily_linearIndependent N) (finiteTarget N) t ht
  rw [← finiteLiftSpace_eq_synthesisSpan] at h
  simpa only [finiteMinimum, finiteShiftedSource, finiteRegularizedGram, finiteShiftedGram,
    finiteUnshiftedGram, regularizedCoefficients, regularizedGram, finiteTarget,
    hardyCoordinates.norm_map, energy, walkError, projection, finiteSpace] using h

/-- The explicit inverse-matrix lift, rather than an arbitrary chosen minimizer. -/
def finiteMinimizer (N : ℕ) (t : ℝ) : Space :=
  Fintype.linearCombination ℝ (finiteLiftFamily N)
    ((finiteRegularizedGram N t)⁻¹.mulVec (finiteShiftedSource N))

theorem finiteMinimizer_mem (N : ℕ) (t : ℝ) :
    finiteMinimizer N t ∈ finiteLiftSpace N := by
  rw [finiteLiftSpace_eq_synthesisSpan]
  exact synthesis_mem _ _

theorem finiteMinimizer_normal (N : ℕ) (t : ℝ) (ht : 0 < t)
    (w : Space) (hw : w ∈ finiteLiftSpace N) :
    inner ℝ (difference rightShiftLinear (finiteMinimizer N t) - finiteTarget N)
      (difference rightShiftLinear w) + t^2 * inner ℝ (finiteMinimizer N t) w = 0 := by
  exact regularizedCoefficients_normal rightShiftLinear
    (finiteLiftFamily_linearIndependent N) (finiteTarget N) t ht w hw

theorem finiteMinimizer_energy (N : ℕ) (t : ℝ) (ht : 0 < t) :
    regularizedEnergy rightShiftLinear (finiteTarget N) t (finiteMinimizer N t) =
      finiteMinimum N t := by
  unfold finiteMinimum
  rw [regularizedInf_eq_norm_sq_sub_pairing rightShiftLinear (finiteTarget N) t
    (finiteLiftSpace N) (finiteMinimizer N t) (finiteMinimizer_mem N t)
    (finiteMinimizer_normal N t ht)]
  exact regularizedEnergy_eq_norm_sq_sub_pairing rightShiftLinear (finiteTarget N) t
    (finiteLiftSpace N) (finiteMinimizer N t) (finiteMinimizer_mem N t)
    (finiteMinimizer_normal N t ht)

theorem finiteMinimizer_unique (N : ℕ) (t : ℝ) (ht : 0 < t)
    (v : Space) (hv : v ∈ finiteLiftSpace N)
    (hmin : regularizedEnergy rightShiftLinear (finiteTarget N) t v = finiteMinimum N t) :
    v = finiteMinimizer N t := by
  have h := regularizedEnergy_completion rightShiftLinear (finiteTarget N) t
    (finiteLiftSpace N) (finiteMinimizer N t) v (finiteMinimizer_mem N t) hv
    (finiteMinimizer_normal N t ht)
  rw [finiteMinimizer_energy N t ht, hmin] at h
  have hz : t^2 * ‖v - finiteMinimizer N t‖^2 ≤ 0 := by
    linarith [sq_nonneg ‖difference rightShiftLinear (v - finiteMinimizer N t)‖]
  have hn : ‖v - finiteMinimizer N t‖^2 ≤ 0 := by
    by_contra hn
    have hp := mul_pos (sq_pos_of_pos ht) (lt_of_not_ge hn)
    linarith
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (v - finiteMinimizer N t)]

theorem finiteMinimizer_energy_tendsto_zero (t : ℕ → ℝ)
    (hpos : ∀ N, 0 < t N) (ht : Filter.Tendsto t Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => regularizedEnergy rightShiftLinear (finiteTarget N)
      (t N) (finiteMinimizer N (t N))) Filter.atTop (nhds 0) := by
  simpa only [finiteMinimizer_energy _ _ (hpos _)] using finiteMinimum_tendsto_zero t ht

/-- Exact finite obstruction to deriving the divided rate from positivity alone. -/
theorem finiteInverseGain_le (N : ℕ) (t : ℝ) (ht : 0 < t) :
    dotProduct (finiteShiftedSource N)
      ((finiteRegularizedGram N t)⁻¹.mulVec (finiteShiftedSource N)) ≤ energy N / (1+t) := by
  have hb := energy_div_le_finiteMinimum_div N t ht
  rw [finiteMinimum_eq_inverseGram N t ht] at hb
  have hm := (le_div_iff₀ ht).mp hb
  have he := div_mul_cancel₀ (energy N) (show (1+t) ≠ 0 by linarith)
  nlinarith

theorem finiteShiftedGram_entry (N : ℕ) (i j : Fin N) :
    finiteShiftedGram N i j =
      (Real.log (i.val+2 : ℕ) * Real.log (j.val+2 : ℕ) +
        (∑' n : ℕ, 1 / (n : ℝ)^2) *
          (1 - 1 / (i.val+2 : ℕ) - 1 / (j.val+2 : ℕ) +
            ((i.val+2 : ℕ) : ℝ) * (j.val+2 : ℕ) /
              (Nat.lcm (i.val+2) (j.val+2) : ℝ)^2)) /
      (((i.val+2 : ℕ) : ℝ) * (j.val+2 : ℕ)) :=
  shiftedResidue_inner i.val j.val

theorem riemannHypothesis_of_inverseGram_gap
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (t : ℕ → ℝ) (hpos : ∀ j, 0 < t j)
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (hrate : Filter.Tendsto (fun j =>
      (energy (N j) - dotProduct (finiteShiftedSource (N j))
        ((finiteRegularizedGram (N j) (t j))⁻¹.mulVec (finiteShiftedSource (N j)))) / t j)
      Filter.atTop (nhds 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_finiteMinimum_div_parameter_tendsto_zero N hN t hpos ht
  simpa only [finiteMinimum_eq_inverseGram _ _ (hpos _)] using hrate

end RiemannResearch.RH.Pareto.Noor
