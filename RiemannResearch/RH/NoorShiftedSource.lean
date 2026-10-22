import RiemannResearch.RH.NoorRegularizedGram

/-!
# Actual shifted sources, logarithmic moments, and Schur control

Source: elementary deductions from the user's
RH_Finite_Arithmetic_Shifted_Lifts_2026-09-24_Continuation handoff and
the repository's complete Hilbert projections and Noor logarithmic vectors.
NoorShiftedResidueDensity records the source of the existing shifted density
and logarithmic-family argument. No mathematical novelty is asserted.

This module retains the actual projection coefficients and every signed
mixed term. It proves h = b - B c, B + Bᵀ = K, the exact source-log-moment
formula, the moving-index source limit, and a Schur quadratic bound.
The source normalized by d/log d tends to the actual residual energy;
the theorem does not prove this energy is zero. The final RH reduction
keeps its substantive source-vanishing hypothesis explicit.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix
namespace RiemannResearch.RH.Pareto

theorem inner_hardyCoordinates_one (a : ThresholdHilbert) :
    inner ℝ a (hardyCoordinates hilbertOne) = -a 0 := by
  have ha := hardyCoordinates.apply_symm_apply a
  have hz := hardyCoordinates_zero (hardyCoordinates.symm a)
  have hi := hardyCoordinates.inner_map_map (hardyCoordinates.symm a) hilbertOne
  rw [ha, tailAverage_zero] at hz
  rw [ha] at hi
  linarith


namespace Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.Noor
open RiemannResearch.Analysis.ShiftedLift
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
open CoefficientStabilization

theorem finiteTarget_zero (N : ℕ) : finiteTarget N 0 = -energy N := by
  have ho : inner ℝ (hilbertOne - projection N) (projection N) = 0 := by
    rw [real_inner_comm]
    exact (Submodule.sub_starProjection_mem_orthogonal (K := finiteSpace N) hilbertOne)
      _ ((finiteSpace N).starProjection_apply_mem hilbertOne)
  have he : inner ℝ (hilbertOne - projection N) hilbertOne = energy N := by
    change inner ℝ (hilbertOne - projection N) hilbertOne =
      ‖hilbertOne - projection N‖^2
    rw [← real_inner_self_eq_norm_sq, inner_sub_right, ho, sub_zero]
  simp only [finiteTarget, hardyCoordinates_zero, tailAverage_zero, he]

/-- A complete logarithmic moment, equal to a sum over multiples. -/
def sourceLogMoment (N d : ℕ) : ℝ :=
  inner ℝ (finiteTarget N) (logVector d)

/-- Exact source identity; the positive logarithmic term uses T(1) = -e₀. -/
theorem finiteShiftedSource_eq_logMoments (N : ℕ) (i : Fin N) :
    ((i.val+2 : ℕ) : ℝ) * finiteShiftedSource N i =
      Real.log (i.val+2 : ℕ) * energy N +
        sourceLogMoment N 1 - sourceLogMoment N (i.val+2) := by
  have h := congrArg (fun x : Space => inner ℝ (finiteTarget N) x)
    (forward_residue_decomposition i.val)
  simp only [inner_smul_right, inner_add_right, inner_sub_right,
    lp.inner_single_right, finiteTarget_zero] at h
  simp at h
  change ((i.val+2 : ℕ) : ℝ) *
    inner ℝ (difference rightShiftLinear (finiteLiftFamily N i)) (finiteTarget N) = _
  rw [real_inner_comm]
  change ((i.val+2 : ℕ) : ℝ) *
    inner ℝ (finiteTarget N) (forwardDifference (hardyCoordinates (residueAtom i.val))) = _
  dsimp only [sourceLogMoment]
  push_cast at h ⊢
  nlinarith [h]

/-- Moving logarithmic moments vanish without an arithmetic rate assumption. -/
theorem sourceLogMoment_moving_tendsto_zero
    (N k : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hk : Tendsto k atTop atTop) :
    Tendsto (fun j => sourceLogMoment (N j) (k j+2)) atTop (𝓝 0) := by
  let a := hardyCoordinates limitResidual
  have ha : Tendsto (fun j => finiteTarget (N j) - a) atTop (𝓝 0) := by
    simpa only [a, Function.comp_def, sub_self] using (finiteTarget_tendsto.comp hN).sub_const a
  have he : Tendsto (fun j => ‖inner ℝ (finiteTarget (N j) - a)
      (logVector (k j+2))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by
      simpa only [norm_zero, zero_mul] using ha.norm.mul_const ‖logVector 1‖)
    intro j
    simpa only [logVector_norm (k j+2) (by omega)] using
      (norm_inner_le_norm (finiteTarget (N j) - a) (logVector (k j+2)))
  have hei := tendsto_zero_iff_norm_tendsto_zero.mpr he
  have hw := (logVector_weak_tendsto_zero a).comp hk
  have hs := hei.add hw
  simpa only [Function.comp_def, inner_sub_left, sub_add_cancel, zero_add,
    sourceLogMoment] using hs

theorem finiteShiftedSource_centered_tendsto
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (i : ∀ j, Fin (N j))
    (hi : Tendsto (fun j => (i j).val) atTop atTop) :
    Tendsto (fun j => ((i j).val+2 : ℕ) * finiteShiftedSource (N j) (i j) -
      Real.log ((i j).val+2 : ℕ) * energy (N j))
      atTop (𝓝 (inner ℝ (hardyCoordinates limitResidual) (logVector 1))) := by
  have h1 : Tendsto (fun j => inner ℝ (finiteTarget (N j)) (logVector 1))
      atTop (𝓝 (inner ℝ (hardyCoordinates limitResidual) (logVector 1))) :=
    (finiteTarget_tendsto.comp hN).inner tendsto_const_nhds
  have h2 := sourceLogMoment_moving_tendsto_zero N (fun j => (i j).val) hN hi
  have hs := h1.sub h2
  simp only [sub_zero] at hs
  convert hs using 1
  ext j
  rw [finiteShiftedSource_eq_logMoments]
  unfold sourceLogMoment
  ring

/-- The normalized growing source converges to the actual limiting energy. -/
theorem finiteShiftedSource_log_scaled_tendsto
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (i : ∀ j, Fin (N j))
    (hi : Tendsto (fun j => (i j).val) atTop atTop) :
    Tendsto (fun j => (((i j).val+2 : ℕ) : ℝ) *
      finiteShiftedSource (N j) (i j) / Real.log ((i j).val+2 : ℕ))
      atTop (𝓝 limitEnergy) := by
  have hlog : Tendsto (fun j => Real.log ((i j).val+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        ((tendsto_add_atTop_nat 2).comp hi))
  have hz := (finiteShiftedSource_centered_tendsto N hN i hi).mul
    (tendsto_inv_atTop_zero.comp hlog)
  simp only [mul_zero] at hz
  have hs := (energy_tendsto.comp hN).add hz
  simp only [add_zero] at hs
  convert hs using 1
  ext j
  have hn : Real.log ((i j).val+2 : ℕ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < (i j).val+2)))
  simp only [Function.comp_def]
  field_simp
  ring


/-- The zero value of the normalized moving source is exactly the zero-residual
obligation. The unconditional limit theorem does not establish this value. -/
theorem finiteShiftedSource_log_scaled_zero_iff
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (i : ∀ j, Fin (N j))
    (hi : Tendsto (fun j => (i j).val) atTop atTop) :
    Tendsto (fun j => (((i j).val+2 : ℕ) : ℝ) *
      finiteShiftedSource (N j) (i j) / Real.log ((i j).val+2 : ℕ))
      atTop (𝓝 0) ↔ limitResidual = 0 := by
  constructor
  · intro h
    apply limitResidual_zero_iff_energy_zero.mpr
    exact tendsto_nhds_unique (finiteShiftedSource_log_scaled_tendsto N hN i hi) h
  · intro h
    have he := limitResidual_zero_iff_energy_zero.mp h
    simpa only [he] using finiteShiftedSource_log_scaled_tendsto N hN i hi

/-- Conditional research reduction: hsource is the open zero-residual-sized
source assertion, not a consequence of source-log-moment convergence. -/
theorem riemannHypothesis_of_finiteShiftedSource_log_scaled_zero
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (i : ∀ j, Fin (N j))
    (hi : Tendsto (fun j => (i j).val) atTop atTop)
    (hsource : Tendsto (fun j => (((i j).val+2 : ℕ) : ℝ) *
      finiteShiftedSource (N j) (i j) / Real.log ((i j).val+2 : ℕ))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      ((finiteShiftedSource_log_scaled_zero_iff N hN i hi).mp hsource))

/-- The full mixed matrix, including its skew-symmetric part. -/
def finiteMixedShiftGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => inner ℝ (difference rightShiftLinear (finiteLiftFamily N i))
    (finiteLiftFamily N j)

/-- Coefficients of the original unshifted projection, distinct from lift coefficients. -/
def finiteProjectionCoefficients (N : ℕ) (i : Fin N) : ℝ :=
  coefficient N (i.val + 2)

/-- The constant target's shifted source. -/
def finiteOneSource (N : ℕ) (i : Fin N) : ℝ :=
  Real.log ((i.val+2 : ℕ) : ℝ) / ((i.val+2 : ℕ) : ℝ)

theorem finiteTarget_expansion (N : ℕ) :
    finiteTarget N = hardyCoordinates hilbertOne -
      ∑ j : Fin N, finiteProjectionCoefficients N j • finiteLiftFamily N j := by
  unfold finiteTarget
  rw [map_sub, projection_expansion, map_sum]
  simp only [map_smul, finiteLiftFamily, finiteProjectionCoefficients]

theorem finiteShiftedFamily_inner_one (N : ℕ) (i : Fin N) :
    inner ℝ (difference rightShiftLinear (finiteLiftFamily N i))
      (hardyCoordinates hilbertOne) = finiteOneSource N i := by
  rw [inner_hardyCoordinates_one]
  change -(forwardDifference (hardyCoordinates (residueAtom i.val)) 0) = _
  rw [forward_residue_zero, neg_neg]
  rfl

theorem finiteShiftedSource_eq_mixed (N : ℕ) :
    finiteShiftedSource N = finiteOneSource N -
      (finiteMixedShiftGram N).mulVec (finiteProjectionCoefficients N) := by
  classical
  funext i
  change inner ℝ (difference rightShiftLinear (finiteLiftFamily N i))
    (finiteTarget N) = finiteOneSource N i -
      ∑ j : Fin N, finiteMixedShiftGram N i j * finiteProjectionCoefficients N j
  rw [finiteTarget_expansion, inner_sub_right, finiteShiftedFamily_inner_one,
    inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_right]
  change finiteProjectionCoefficients N j * finiteMixedShiftGram N i j = _
  ring

theorem finiteMixedShiftGram_add_transpose (N : ℕ) :
    finiteMixedShiftGram N + (finiteMixedShiftGram N)ᵀ = finiteShiftedGram N := by
  have hS (u v : Space) :
      inner ℝ (rightShiftLinear u) (rightShiftLinear v) = inner ℝ u v := by
    have hv : leftShift (rightShift v) = v := by
      apply Subtype.ext
      funext n
      rfl
    change inner ℝ (rightShift u) (rightShift v) = _
    rw [shift_inner, hv]
  ext i j
  change inner ℝ (difference rightShiftLinear (finiteLiftFamily N i))
      (finiteLiftFamily N j) +
    inner ℝ (difference rightShiftLinear (finiteLiftFamily N j))
      (finiteLiftFamily N i) =
    inner ℝ (difference rightShiftLinear (finiteLiftFamily N i))
      (difference rightShiftLinear (finiteLiftFamily N j))
  simp only [difference_apply, inner_sub_left, inner_sub_right, hS]
  rw [real_inner_comm (finiteLiftFamily N j) (finiteLiftFamily N i),
    real_inner_comm (rightShiftLinear (finiteLiftFamily N j)) (finiteLiftFamily N i)]
  ring


/-- Source alignment after projecting shifted lifts off the original finite span.
The Schur quadratic is written in factored form; no inverse of it is assumed. -/
theorem finiteShiftedSource_schur_bound (N : ℕ) (x : Fin N → ℝ) :
    (dotProduct x (finiteShiftedSource N)) ^ 2 ≤ energy N *
      (dotProduct x ((finiteShiftedGram N).mulVec x) -
        dotProduct (((finiteMixedShiftGram N)ᵀ).mulVec x)
          ((finiteUnshiftedGram N)⁻¹.mulVec
            (((finiteMixedShiftGram N)ᵀ).mulVec x))) := by
  classical
  let w : Fin N → Space := fun i =>
    difference rightShiftLinear (finiteLiftFamily N i)
  let y : Space := Fintype.linearCombination ℝ w x
  have hyinner : inner ℝ y (finiteTarget N) =
      dotProduct x (finiteShiftedSource N) := by
    dsimp only [y]
    rw [inner_synthesis_left]
    rfl
  have hcross : cross (finiteLiftFamily N) y =
      ((finiteMixedShiftGram N)ᵀ).mulVec x := by
    funext i
    change inner ℝ (finiteLiftFamily N i)
      (Fintype.linearCombination ℝ w x) =
        ∑ j : Fin N, finiteMixedShiftGram N j i * x j
    rw [Fintype.linearCombination_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_smul_right]
    change x j * inner ℝ (finiteLiftFamily N i)
      (difference rightShiftLinear (finiteLiftFamily N j)) =
      inner ℝ (difference rightShiftLinear (finiteLiftFamily N j))
        (finiteLiftFamily N i) * x j
    rw [real_inner_comm (finiteLiftFamily N i)
      (difference rightShiftLinear (finiteLiftFamily N j))]
    ring
  have hnormy : ‖y‖ ^ 2 =
      dotProduct x ((finiteShiftedGram N).mulVec x) := by
    change ‖Fintype.linearCombination ℝ w x‖ ^ 2 =
      dotProduct x ((gramMatrix w).mulVec x)
    rw [gramMatrix_mulVec, gram_quadratic]
    rfl
  have hinv : inverseCoeff (finiteLiftFamily_linearIndependent N) y =
      (finiteUnshiftedGram N)⁻¹.mulVec (cross (finiteLiftFamily N) y) := by
    symm
    exact gramMatrix_inverseSource (finiteLiftFamily_linearIndependent N) _
  let p : Space := Fintype.linearCombination ℝ (finiteLiftFamily N)
    (inverseCoeff (finiteLiftFamily_linearIndependent N) y)
  have hp : p ∈ finiteLiftSpace N := by
    rw [finiteLiftSpace_eq_synthesisSpan]
    exact synthesis_mem _ _
  have hresnorm : ‖y - p‖ ^ 2 =
      dotProduct x ((finiteShiftedGram N).mulVec x) -
        dotProduct (((finiteMixedShiftGram N)ᵀ).mulVec x)
          ((finiteUnshiftedGram N)⁻¹.mulVec
            (((finiteMixedShiftGram N)ᵀ).mulVec x)) := by
    have hs := residual_schur_value (finiteLiftFamily_linearIndependent N) y
    rw [hnormy, hinv, hcross] at hs
    simpa only [p, hinv, hcross, dotProduct, mul_comm] using hs
  have hsource : inner ℝ (finiteTarget N)
      (y - p) =
      dotProduct x (finiteShiftedSource N) := by
    rw [inner_sub_right, finiteTarget_orthogonal N _ hp, sub_zero,
      real_inner_comm, hyinner]
  have he : ‖finiteTarget N‖ ^ 2 = energy N := by
    simp only [finiteTarget, hardyCoordinates.norm_map, energy,
      walkError, projection, finiteSpace]
  have hc : (inner ℝ (finiteTarget N)
      (y - p)) ^ 2 ≤
      ‖finiteTarget N‖ ^ 2 * ‖y - p‖ ^ 2 := by
    simpa only [pow_two, real_inner_self_eq_norm_sq] using
      real_inner_mul_inner_self_le (finiteTarget N)
        (y - p)
  rw [hsource, he, hresnorm] at hc
  exact hc

end Noor
end RiemannResearch.RH.Pareto
