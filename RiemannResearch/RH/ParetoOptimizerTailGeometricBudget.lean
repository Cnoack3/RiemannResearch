import RiemannResearch.RH.ParetoOptimizerTailSummability
import Mathlib.Tactic.FieldSimp

/-!
# A sharper geometric budget for the actual quartic optimizer tails

Source: elementary quartic-conductor refinement of the complete physical
tail bound in RH_Actual_Arithmetic_Advances_2026-10-07.pdf, Section 3.
The exact final projection defect is retained in every total budget.

For N₀=B≥2 and Nⱼ₊₁=Nⱼ⁴, use Nⱼ≥B(B³)ʲ rather than B2ʲ. The complete
old-stage leakage allowance sums to 16 ‖v‖² B²/(B³−1), improving 32 ‖v‖²/B.
All stage spans, orthogonal projections, physical cutoffs, and defect floors
are the literal Pareto objects. There is no density or RH premise.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionTailSummability

/-- Every quartic stage grows by at least the initial cubed conductor. -/
theorem quarticConductor_baseCube_mul_le (B j : ℕ) (hB : 2 ≤ B) :
    B^3 * quarticConductor B j ≤ quarticConductor B (j+1) := by
  have hp : B^3 ≤ quarticConductor B j ^ 3 :=
    pow_le_pow_left' (quarticConductor_ge_base B j hB) 3
  rw [quarticConductor_succ]
  calc
    _ ≤ quarticConductor B j ^ 3 * quarticConductor B j :=
      Nat.mul_le_mul_right _ hp
    _ = _ := by ring

/-- The actual quartic conductors dominate the sharper geometric sequence. -/
theorem quarticConductor_ge_baseCube_geometric (B j : ℕ) (hB : 2 ≤ B) :
    B * (B^3)^j ≤ quarticConductor B j := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        _ = B^3 * (B * (B^3)^j) := by rw [pow_succ]; ring
        _ ≤ B^3 * quarticConductor B j := Nat.mul_le_mul_left _ ih
        _ ≤ _ := quarticConductor_baseCube_mul_le B j hB

private theorem baseCube_real_lower (B : ℕ) (hB : 2 ≤ B) :
    (8 : ℝ) ≤ (B : ℝ)^3 := by
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hBR 3
  norm_num at hp
  exact hp

private theorem reciprocal_baseCube_abs_lt_one (B : ℕ) (hB : 2 ≤ B) :
    |1 / (B : ℝ)^3| < 1 := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (B : ℝ)^3)]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (B : ℝ)^3)).2
  nlinarith only [baseCube_real_lower B hB]

def quarticBaseCubeLeakageMajorant (B : ℕ) (v : ThresholdHilbert) (j : ℕ) : ℝ :=
  (16 * ‖v‖^2 / (B : ℝ)) * (1 / (B : ℝ)^3)^j

theorem quarticBaseCubeLeakageMajorant_summable (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) : Summable (quarticBaseCubeLeakageMajorant B v) :=
  (summable_geometric_of_abs_lt_one
    (reciprocal_baseCube_abs_lt_one B hB)).mul_left _

theorem quarticBaseCubeLeakageMajorant_tsum (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    (∑' j, quarticBaseCubeLeakageMajorant B v j) =
      16 * ‖v‖^2 * (B : ℝ)^2 / ((B : ℝ)^3 - 1) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hc : (0 : ℝ) < (B : ℝ)^3 - 1 := by
    linarith only [baseCube_real_lower B hB]
  have hr : (0 : ℝ) < 1 - 1 / (B : ℝ)^3 := by
    have h := (le_abs_self (1 / (B : ℝ)^3)).trans_lt
      (reciprocal_baseCube_abs_lt_one B hB)
    linarith
  unfold quarticBaseCubeLeakageMajorant
  rw [tsum_mul_left,
    tsum_geometric_of_abs_lt_one (reciprocal_baseCube_abs_lt_one B hB)]
  field_simp [ne_of_gt hBR, ne_of_gt hc, ne_of_gt hr]

/-- The actual arithmetic leakage provider satisfies the sharper summable
majorant. Neither tail tightness nor coefficient control is a hypothesis. -/
theorem quartic_oldOptimizer_tail_le_baseCube (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) (j : ℕ) :
    ‖(finiteSpace (quarticConductor B j-1)).starProjection v -
      compactHead (quarticConductor B (j+1))
        ((finiteSpace (quarticConductor B j-1)).starProjection v)‖^2 ≤
          quarticBaseCubeLeakageMajorant B v j := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hgeom : (B : ℝ) * ((B : ℝ)^3)^j ≤ (quarticConductor B j : ℝ) := by
    exact_mod_cast quarticConductor_ge_baseCube_geometric B j hB
  have hgeomeq : (16 * ‖v‖^2 / (B : ℝ)) * (1 / (B : ℝ)^3)^j =
      16 * ‖v‖^2 / ((B : ℝ) * ((B : ℝ)^3)^j) := by
    rw [div_pow, one_pow]
    field_simp [ne_of_gt hBR]
  calc
    _ ≤ 16 * ‖v‖^2 / (quarticConductor B j : ℝ) :=
      quartic_oldOptimizer_tail_le_reciprocal B hB v j
    _ ≤ 16 * ‖v‖^2 / ((B : ℝ) * ((B : ℝ)^3)^j) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hgeom
    _ = _ := by simpa only [quarticBaseCubeLeakageMajorant] using hgeomeq.symm

/-- A strictly smaller complete-tail budget with its entire cross contribution
retained in the square-root sum. The final residual defect may be positive. -/
theorem quarticOptimizerTail_tsum_le_baseCube (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    (∑' j, quarticOptimizerTail B v j) ≤
      (Real.sqrt (‖v - (finiteSpace (B-1)).starProjection v‖^2 -
          ‖v - closedSpace.starProjection v‖^2) +
        Real.sqrt (16 * ‖v‖^2 * (B : ℝ)^2 / ((B : ℝ)^3 - 1)))^2 := by
  let W := fun j => finiteSpace (quarticConductor B j-1)
  let T : ℕ → ThresholdHilbert →ₗ[ℝ] ThresholdHilbert :=
    fun j => LinearMap.id - compactHeadLinear (quarticConductor B (j+1))
  have hW : Monotone W := by
    intro i j hij
    exact walkSpan_mono residueAtom id
      (Nat.sub_le_sub_right (quarticConductor_mono B hB hij) 1)
  have hT : ∀ j z, ‖T j z‖ ≤ ‖z‖ := by
    intro j z
    exact compactHead_tail_norm_le (quarticConductor B (j+1)) z
  have hδ : ∀ j, ‖v - closedSpace.starProjection v‖^2 ≤
      ‖v - (W j).starProjection v‖^2 := by
    intro j
    have he := walkError_eq_limitingError_add residueAtom id v
      (quarticConductor B j-1)
    change ‖v - (W j).starProjection v‖^2 =
      ‖v - closedSpace.starProjection v‖^2 + _ at he
    linarith only [he, sq_nonneg ‖closedSpace.starProjection v - (W j).starProjection v‖]
  have hT_apply (j : ℕ) (z : ThresholdHilbert) :
      T j z = z - compactHead (quarticConductor B (j+1)) z := rfl
  have h := projection_tail_tsum_le W hW v T hT
    (quarticBaseCubeLeakageMajorant B v)
    (fun j => by unfold quarticBaseCubeLeakageMajorant; positivity)
    (quarticBaseCubeLeakageMajorant_summable B hB v)
    (quartic_oldOptimizer_tail_le_baseCube B hB v) _ hδ
  simpa only [hT_apply, W, quarticOptimizerTail, quarticConductor_zero,
    quarticBaseCubeLeakageMajorant_tsum B hB v] using h

/-- The sharp geometric allowance specializes to the actual compact source
with its exact full norm squared 134. -/
theorem compact_quarticOptimizerTail_tsum_le_baseCube (B : ℕ) (hB : 2 ≤ B) :
    (∑' j, quarticOptimizerTail B twoThreeDual j) ≤
      (Real.sqrt (‖twoThreeDualResidual (B-1)‖^2 - compactProjectionDefect) +
        Real.sqrt (2144 * (B : ℝ)^2 / ((B : ℝ)^3 - 1)))^2 := by
  simpa only [twoThreeDualResidual, compactProjectionDefect,
    twoThreeDual_norm_sq_eq_134, show (16 : ℝ)*134 = 2144 by norm_num] using
      quarticOptimizerTail_tsum_le_baseCube B hB twoThreeDual

/-- Comparison of the complete geometric allowances. This derives the coarse
base-two bound from the improved allowance without weakening its hypotheses. -/
theorem quartic_baseCube_allowance_le_baseTwo (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    16 * ‖v‖^2 * (B : ℝ)^2 / ((B : ℝ)^3 - 1) ≤
      32 * ‖v‖^2 / (B : ℝ) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hc : (0 : ℝ) < (B : ℝ)^3 - 1 := by
    linarith only [baseCube_real_lower B hB]
  apply (div_le_div_iff₀ hc hBR).2
  have hprod : 0 ≤ ‖v‖^2 * ((B : ℝ)^3 - 2) :=
    mul_nonneg (sq_nonneg ‖v‖) (by linarith only [baseCube_real_lower B hB])
  nlinarith only [hprod]

/-- Removing the first quartic stage restarts the same tower at B^4. -/
theorem quarticConductor_succ_base (B j : ℕ) :
    quarticConductor B (j+1) = quarticConductor (B^4) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change (quarticConductor B (j+1))^4 =
        (quarticConductor (B^4) j)^4
      rw [ih]

private theorem quarticBase_four_ge_two (B : ℕ) (hB : 2 ≤ B) :
    2 ≤ B^4 := by
  have h : B ≤ B^4 := by
    simpa only [pow_one] using
      pow_le_pow_right' (by omega : 1 ≤ B) (by decide : 1 ≤ 4)
  exact hB.trans h

def quarticFirstSplitLeakageMajorant (B : ℕ) (v : ThresholdHilbert) : ℕ → ℝ
  | 0 => 16 * ‖v‖^2 / (B : ℝ)
  | j+1 => quarticBaseCubeLeakageMajorant (B^4) v j

theorem quarticFirstSplitLeakageMajorant_summable (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) : Summable (quarticFirstSplitLeakageMajorant B v) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [quarticFirstSplitLeakageMajorant] using
    quarticBaseCubeLeakageMajorant_summable (B^4)
      (quarticBase_four_ge_two B hB) v

theorem quarticFirstSplitLeakageMajorant_tsum (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    (∑' j, quarticFirstSplitLeakageMajorant B v j) =
      16 * ‖v‖^2 * (1 / (B : ℝ) +
        (B : ℝ)^8 / ((B : ℝ)^12 - 1)) := by
  rw [(quarticFirstSplitLeakageMajorant_summable B hB v).tsum_eq_zero_add]
  simp only [quarticFirstSplitLeakageMajorant,
    quarticBaseCubeLeakageMajorant_tsum (B^4) (quarticBase_four_ge_two B hB) v,
    Nat.cast_pow, ← pow_mul]
  norm_num; ring

/-- The first stage uses its own reciprocal bound; later stages use the
internally supplied sharper geometric allowance from the restarted tower. -/
theorem quartic_oldOptimizer_tail_le_firstSplit (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) (j : ℕ) :
    ‖(finiteSpace (quarticConductor B j-1)).starProjection v -
      compactHead (quarticConductor B (j+1))
        ((finiteSpace (quarticConductor B j-1)).starProjection v)‖^2 ≤
          quarticFirstSplitLeakageMajorant B v j := by
  cases j with
  | zero =>
      simpa only [quarticFirstSplitLeakageMajorant, quarticConductor_zero] using
        quartic_oldOptimizer_tail_le_reciprocal B hB v 0
  | succ j =>
      simpa only [quarticConductor_succ_base,
        quarticFirstSplitLeakageMajorant] using
          quartic_oldOptimizer_tail_le_baseCube (B^4)
            (quarticBase_four_ge_two B hB) v j

/-- A further explicit improvement of the complete sparse physical-tail
budget, retaining the full projection-energy cross contribution. -/
theorem quarticOptimizerTail_tsum_le_firstSplit (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    (∑' j, quarticOptimizerTail B v j) ≤
      (Real.sqrt (‖v - (finiteSpace (B-1)).starProjection v‖^2 -
          ‖v - closedSpace.starProjection v‖^2) +
        Real.sqrt (16 * ‖v‖^2 *
          (1 / (B : ℝ) + (B : ℝ)^8 / ((B : ℝ)^12 - 1))))^2 := by
  let W := fun j => finiteSpace (quarticConductor B j-1)
  let T : ℕ → ThresholdHilbert →ₗ[ℝ] ThresholdHilbert :=
    fun j => LinearMap.id - compactHeadLinear (quarticConductor B (j+1))
  have hW : Monotone W := by
    intro i j hij
    exact walkSpan_mono residueAtom id
      (Nat.sub_le_sub_right (quarticConductor_mono B hB hij) 1)
  have hT : ∀ j z, ‖T j z‖ ≤ ‖z‖ := by
    intro j z
    exact compactHead_tail_norm_le (quarticConductor B (j+1)) z
  have hδ : ∀ j, ‖v - closedSpace.starProjection v‖^2 ≤
      ‖v - (W j).starProjection v‖^2 := by
    intro j
    have he := walkError_eq_limitingError_add residueAtom id v
      (quarticConductor B j-1)
    change ‖v - (W j).starProjection v‖^2 =
      ‖v - closedSpace.starProjection v‖^2 + _ at he
    linarith only [he,
      sq_nonneg ‖closedSpace.starProjection v - (W j).starProjection v‖]
  have hT_apply (j : ℕ) (z : ThresholdHilbert) :
      T j z = z - compactHead (quarticConductor B (j+1)) z := rfl
  have h := projection_tail_tsum_le W hW v T hT
    (quarticFirstSplitLeakageMajorant B v)
    (fun j => by
      cases j <;> simp only [quarticFirstSplitLeakageMajorant,
        quarticBaseCubeLeakageMajorant] <;> positivity)
    (quarticFirstSplitLeakageMajorant_summable B hB v)
    (quartic_oldOptimizer_tail_le_firstSplit B hB v) _ hδ
  simpa only [hT_apply, W, quarticOptimizerTail, quarticConductor_zero,
    quarticFirstSplitLeakageMajorant_tsum B hB v] using h

theorem compact_quarticOptimizerTail_tsum_le_firstSplit (B : ℕ)
    (hB : 2 ≤ B) :
    (∑' j, quarticOptimizerTail B twoThreeDual j) ≤
      (Real.sqrt (‖twoThreeDualResidual (B-1)‖^2 - compactProjectionDefect) +
        Real.sqrt (2144 *
          (1 / (B : ℝ) + (B : ℝ)^8 / ((B : ℝ)^12 - 1))))^2 := by
  simpa only [twoThreeDualResidual, compactProjectionDefect,
    twoThreeDual_norm_sq_eq_134, show (16 : ℝ)*134 = 2144 by norm_num] using
      quarticOptimizerTail_tsum_le_firstSplit B hB twoThreeDual

/-- Exact comparison identity, before taking any upper bound. -/
theorem quartic_firstSplit_allowance_difference (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    16 * ‖v‖^2 * (B : ℝ)^2 / ((B : ℝ)^3 - 1) -
      16 * ‖v‖^2 * (1 / (B : ℝ) +
        (B : ℝ)^8 / ((B : ℝ)^12 - 1)) =
      16 * ‖v‖^2 * ((B : ℝ)^9 - 1) /
        ((B : ℝ) * ((B : ℝ)^3 - 1) * ((B : ℝ)^12 - 1)) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hc3 : (0 : ℝ) < (B : ℝ)^3 - 1 := by
    linarith only [baseCube_real_lower B hB]
  have hc12 : (0 : ℝ) < (B : ℝ)^12 - 1 := by
    have h := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ B) :
      (1 : ℝ) ≤ B) (by decide : 3 ≤ 12)
    linarith only [h, baseCube_real_lower B hB]
  field_simp [ne_of_gt hBR, ne_of_gt hc3, ne_of_gt hc12]; ring

theorem quartic_firstSplit_allowance_le_baseCube (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) :
    16 * ‖v‖^2 * (1 / (B : ℝ) +
      (B : ℝ)^8 / ((B : ℝ)^12 - 1)) ≤
      16 * ‖v‖^2 * (B : ℝ)^2 / ((B : ℝ)^3 - 1) := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have h9 : (0 : ℝ) ≤ (B : ℝ)^9 - 1 := by
    have h := pow_le_pow_right₀ hB1 (by decide : 0 ≤ 9)
    simpa only [pow_zero, sub_nonneg] using h
  have hc3 : (0 : ℝ) ≤ (B : ℝ)^3 - 1 := by
    linarith only [baseCube_real_lower B hB]
  have hc12 : (0 : ℝ) ≤ (B : ℝ)^12 - 1 := by
    have h := pow_le_pow_right₀ hB1 (by decide : 3 ≤ 12)
    linarith only [h, baseCube_real_lower B hB]
  have hn : 0 ≤ 16 * ‖v‖^2 * ((B : ℝ)^9 - 1) /
      ((B : ℝ) * ((B : ℝ)^3 - 1) * ((B : ℝ)^12 - 1)) := by positivity
  rw [← quartic_firstSplit_allowance_difference B hB v] at hn
  linarith only [hn]

end RiemannResearch.RH.Pareto.CoefficientStabilization
