import RiemannResearch.Analysis.ProjectionTailSummability
import RiemannResearch.RH.ParetoCompactCutoffLimits
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.RH.ParetoActualSpectralMomentUpper
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Unconditional summability of actual optimizer tails

Source: user-provided complete physical tail argument,
RH_Actual_Arithmetic_Advances_2026-10-07.pdf, Section 3. The finite-stage
provider is finiteSpace_complete_tail_norm_sq_le_cubic.

For N_0=B>=2, N_(j+1)=N_j^4, the entire physical tail of the actual
projection at conductor N_(j+1) is summable. Its total is at most
(sqrt(initial residual energy - limit defect) + sqrt(32 norm(target)^2/B))^2.
No zero-defect or RH premise occurs.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionTailSummability

def quarticConductor (B : ℕ) : ℕ → ℕ
  | 0 => B
  | n+1 => quarticConductor B n ^ 4

@[simp] theorem quarticConductor_zero (B : ℕ) : quarticConductor B 0 = B := rfl
@[simp] theorem quarticConductor_succ (B n : ℕ) :
    quarticConductor B (n+1) = quarticConductor B n ^ 4 := rfl

theorem quarticConductor_ge_base (B n : ℕ) (hB : 2 ≤ B) :
    B ≤ quarticConductor B n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [quarticConductor_succ]
      have hN : 1 ≤ quarticConductor B n := by omega
      have hp : quarticConductor B n ≤ quarticConductor B n ^ 4 := by
        simpa only [pow_one] using
          pow_le_pow_right' hN (by decide : 1 ≤ 4)
      exact ih.trans hp

theorem quarticConductor_double_le (B n : ℕ) (hB : 2 ≤ B) :
    2 * quarticConductor B n ≤ quarticConductor B (n+1) := by
  have hN : 2 ≤ quarticConductor B n := hB.trans (quarticConductor_ge_base B n hB)
  rw [quarticConductor_succ]
  calc
    _ ≤ quarticConductor B n ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right (quarticConductor B n) hN
    _ ≤ _ := pow_le_pow_right' (by omega) (by decide : 2 ≤ 4)

theorem quarticConductor_mono (B : ℕ) (hB : 2 ≤ B) : Monotone (quarticConductor B) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := quarticConductor_double_le B n hB
  omega

theorem quarticConductor_ge_geometric (B n : ℕ) (hB : 2 ≤ B) :
    B * 2 ^ n ≤ quarticConductor B n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := quarticConductor_double_le B n hB
      calc
        _ = 2 * (B * 2 ^ n) := by rw [pow_succ]; ring
        _ ≤ 2 * quarticConductor B n := Nat.mul_le_mul_left 2 ih
        _ ≤ _ := hh

def quarticOptimizerTail (B : ℕ) (v : ThresholdHilbert) (j : ℕ) : ℝ :=
  ‖(finiteSpace (quarticConductor B (j+1)-1)).starProjection v -
    compactHead (quarticConductor B (j+1))
      ((finiteSpace (quarticConductor B (j+1)-1)).starProjection v)‖ ^ 2

def quarticLeakageMajorant (B : ℕ) (v : ThresholdHilbert) (j : ℕ) : ℝ :=
  (16 * ‖v‖^2 / (B : ℝ)) * (1/2 : ℝ)^j

theorem quarticLeakageMajorant_summable (B : ℕ) (v : ThresholdHilbert) :
    Summable (quarticLeakageMajorant B v) :=
  (summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).mul_left _

theorem quarticLeakageMajorant_tsum (B : ℕ) (v : ThresholdHilbert) :
    (∑' j, quarticLeakageMajorant B v j) = 32 * ‖v‖^2 / (B : ℝ) := by
  unfold quarticLeakageMajorant
  rw [tsum_mul_left,
    tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)]
  norm_num; ring

/-- Actual old-stage leakage at the next quartic conductor, before choosing
any geometric summation majorant. The complete physical tail is retained. -/
theorem quartic_oldOptimizer_tail_le_reciprocal (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) (j : ℕ) :
    ‖(finiteSpace (quarticConductor B j-1)).starProjection v -
      compactHead (quarticConductor B (j+1))
        ((finiteSpace (quarticConductor B j-1)).starProjection v)‖ ^ 2 ≤
          16 * ‖v‖^2 / (quarticConductor B j : ℝ) := by
  let M := quarticConductor B j
  let p := (finiteSpace (M-1)).starProjection v
  have hM : 2 ≤ M := hB.trans (quarticConductor_ge_base B j hB)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hp : p ∈ finiteSpace (M-1) := (finiteSpace (M-1)).starProjection_apply_mem v
  have hproj : ‖p‖^2 ≤ ‖v‖^2 := by
    apply (sq_le_sq₀ (norm_nonneg p) (norm_nonneg v)).mpr
    exact (finiteSpace (M-1)).norm_starProjection_apply_le v
  have hfinite := finiteSpace_complete_tail_norm_sq_le_cubic (M-1)
    (quarticConductor B (j+1)) p hp
  have hshift : M-1+1=M := by omega
  rw [hshift, quarticConductor_succ] at hfinite
  change ‖p - compactHead (M^4) p‖^2 ≤ _
  calc
    _ ≤ 16 * (M : ℝ)^3 * ‖p‖^2 / ((M : ℝ)^4+1) := by
      simpa only [M, Nat.cast_pow] using hfinite
    _ ≤ 16 * (M : ℝ)^3 * ‖v‖^2 / ((M : ℝ)^4+1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hproj (by positivity)) (by positivity)
    _ ≤ 16 * ‖v‖^2 / (M : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hMR).2
      nlinarith only [sq_nonneg ‖v‖]

/-- This actual arithmetic leakage provider chooses the simple base-two
majorant used by the first summability budget. All inputs are discharged. -/
theorem quartic_oldOptimizer_tail_le (B : ℕ) (hB : 2 ≤ B)
    (v : ThresholdHilbert) (j : ℕ) :
    ‖(finiteSpace (quarticConductor B j-1)).starProjection v -
      compactHead (quarticConductor B (j+1))
        ((finiteSpace (quarticConductor B j-1)).starProjection v)‖ ^ 2 ≤
          quarticLeakageMajorant B v j := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hgeom : (B : ℝ) * (2 : ℝ)^j ≤ (quarticConductor B j : ℝ) := by
    exact_mod_cast quarticConductor_ge_geometric B j hB
  have hgeomeq : (16 * ‖v‖^2 / (B : ℝ)) * (1/2 : ℝ)^j =
      16 * ‖v‖^2 / ((B : ℝ) * (2 : ℝ)^j) := by
    rw [div_pow, one_pow]
    field_simp [ne_of_gt hBR]
  calc
    _ ≤ 16 * ‖v‖^2 / (quarticConductor B j : ℝ) :=
      quartic_oldOptimizer_tail_le_reciprocal B hB v j
    _ ≤ 16 * ‖v‖^2 / ((B : ℝ) * (2 : ℝ)^j) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hgeom
    _ = _ := by simpa only [quarticLeakageMajorant] using hgeomeq.symm

/-- The complete actual physical tails have a summable total at literal
quartic conductors. Every leakage input is supplied internally. -/
theorem quarticOptimizerTail_summable (B : ℕ) (hB : 2 ≤ B) (v : ThresholdHilbert) :
    Summable (quarticOptimizerTail B v) := by
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
  exact projection_tail_summable W hW v T hT (quarticLeakageMajorant B v)
    (fun j => by unfold quarticLeakageMajorant; positivity)
    (quarticLeakageMajorant_summable B v) (quartic_oldOptimizer_tail_le B hB v)
    _ hδ

/-- The entire tail series obeys a sharp coefficient-one projection budget,
with an explicit vanishing leakage allowance as the initial conductor grows. -/
theorem quarticOptimizerTail_tsum_le (B : ℕ) (hB : 2 ≤ B) (v : ThresholdHilbert) :
    (∑' j, quarticOptimizerTail B v j) ≤
      (Real.sqrt (‖v - (finiteSpace (B-1)).starProjection v‖^2 -
          ‖v - closedSpace.starProjection v‖^2) +
        Real.sqrt (32 * ‖v‖^2 / (B : ℝ)))^2 := by
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
  have h := projection_tail_tsum_le W hW v T hT (quarticLeakageMajorant B v)
    (fun j => by unfold quarticLeakageMajorant; positivity)
    (quarticLeakageMajorant_summable B v) (quartic_oldOptimizer_tail_le B hB v)
    _ hδ
  simpa only [hT_apply, W, quarticOptimizerTail, quarticConductor_zero,
    quarticLeakageMajorant_tsum] using h

theorem compact_quarticOptimizerTail_summable (B : ℕ) (hB : 2 ≤ B) :
    Summable (quarticOptimizerTail B twoThreeDual) :=
  quarticOptimizerTail_summable B hB twoThreeDual

theorem compact_quarticOptimizerTail_tsum_le (B : ℕ) (hB : 2 ≤ B) :
    (∑' j, quarticOptimizerTail B twoThreeDual j) ≤
      (Real.sqrt (‖twoThreeDualResidual (B-1)‖^2 - compactProjectionDefect) +
        Real.sqrt (4288 / (B : ℝ)))^2 := by
  simpa only [twoThreeDualResidual, compactProjectionDefect,
    twoThreeDual_norm_sq_eq_134, show (32:ℝ)*134=4288 by norm_num] using
      quarticOptimizerTail_tsum_le B hB twoThreeDual

/-- Starting the tower farther out makes its whole future tail budget
vanish. This simultaneous control is unconditional for every target. -/
theorem quarticOptimizerTail_tsum_tendsto_zero (v : ThresholdHilbert) :
    Tendsto (fun n : ℕ => ∑' j, quarticOptimizerTail (n+2) v j)
      atTop (𝓝 0) := by
  let δ := ‖v - closedSpace.starProjection v‖^2
  have hd0 : Tendsto (fun n => ‖v - (finiteSpace n).starProjection v‖^2)
      atTop (𝓝 δ) :=
    walkError_tendsto residueAtom id Function.surjective_id v
  have hd : Tendsto (fun n => ‖v - (finiteSpace (n+1)).starProjection v‖^2)
      atTop (𝓝 δ) := (tendsto_add_atTop_iff_nat 1).mpr hd0
  have hgap := hd.sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ))
  have hden : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n : ℕ => show (n:ℝ) ≤ (n:ℝ)+2 by linarith)
      tendsto_natCast_atTop_atTop
  have hleak := hden.const_div_atTop (32 * ‖v‖^2)
  have hgsqrt : Tendsto (fun n => Real.sqrt
      (‖v - (finiteSpace (n+1)).starProjection v‖^2 - δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hgap
  have hlsqrt : Tendsto (fun n : ℕ => Real.sqrt
      (32 * ‖v‖^2 / ((n:ℝ)+2))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hleak
  have hmajor := (hgsqrt.add hlsqrt).pow 2
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    tsum_nonneg (fun j => by unfold quarticOptimizerTail; positivity))) _
    (by simpa only [zero_add, zero_pow (by decide : 2 ≠ 0)] using hmajor)
  apply Filter.Eventually.of_forall
  intro n
  simpa only [show n+2-1=n+1 by omega, Nat.cast_add, Nat.cast_ofNat, δ] using
    quarticOptimizerTail_tsum_le (n+2) (by omega) v

end RiemannResearch.RH.Pareto.CoefficientStabilization
