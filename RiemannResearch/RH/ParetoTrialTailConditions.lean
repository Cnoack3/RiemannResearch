import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.RH.CompensatedTwoCoefficientCriterion
import RiemannResearch.Analysis.HeadTailPairing
import RiemannResearch.Analysis.HeadTailConditions
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Signed physical trial-tail conditions for the actual Pareto model

All finite normal equations are discharged by the existing actual orthogonal
projection. The hypotheses left to the user are precisely legal trials,
cofinal head approximation and either a signed strict-fraction estimate or
smallness of the two complete tail-energy product. This file uses no head
inverse, reciprocal rank-one identification or exact head-lift provider.

The conclusions are sufficient conditions for RH, not an unconditional RH
proof. Source: user-provided Green-Pareto-Schur continuation, Section 18;
this supports the statements and exact signed proof strategy.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The actual compact target is fixed by every physical cutoff at site 3
or later. This proof uses only the already formalized compact Mobius duals. -/
theorem compactHead_twoThreeDual (N : ℕ) (hN : 3 ≤ N) :
    compactHead N twoThreeDual = twoThreeDual := by
  unfold twoThreeDual
  rw [compactHead_sub, compactHead_smul,
    compactHead_mobiusRiesz N 2 (by decide) (by omega),
    compactHead_mobiusRiesz N 3 (by decide) hN]

/-- The full optimizer's residual is orthogonal to every legal trial. -/
theorem twoThree_full_residual_normal (n : ℕ)
    (u : ThresholdHilbert) (hu : u ∈ finiteSpace n) :
    inner ℝ (twoThreeDual - (finiteSpace n).starProjection twoThreeDual) u = 0 := by
  rw [real_inner_comm]
  exact ((finiteSpace n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal twoThreeDual) u hu

/-- Exact signed identity for any legal trial. Approximate head matching is
permitted. Both full tails are kept before any absolute-value estimate. -/
theorem twoThree_actual_trial_signed_identity
    (N : ℕ) (hN : 3 ≤ N) (u : ThresholdHilbert)
    (hu : u ∈ finiteSpace (N-1)) :
    ‖twoThreeDualResidual (N-1)‖^2 =
      inner ℝ (compactHead N (twoThreeDualResidual (N-1)))
        (twoThreeDual - compactHead N u) +
      inner ℝ ((finiteSpace (N-1)).starProjection twoThreeDual -
        compactHead N ((finiteSpace (N-1)).starProjection twoThreeDual))
        (u - compactHead N u) := by
  apply RiemannResearch.Analysis.HeadTailPairing.projection_residual_eq_head_tail_pairing
    (compactHeadLinear N) twoThreeDual u
    ((finiteSpace (N-1)).starProjection twoThreeDual)
  · exact compactHead_twoThreeDual N hN
  · exact twoThree_full_residual_normal (N-1) u hu
  · exact twoThree_full_residual_normal (N-1) _
      ((finiteSpace (N-1)).starProjection_apply_mem twoThreeDual)
  · exact RiemannResearch.Analysis.HeadTailPairing.orthogonal_cutoff_inner_split
      (compactHeadLinear N) (compactHead_symmetric N)
      (compactHead_idempotent N) _ _

/-- Uniform residual bound is projection geometry, not an RH premise. -/
theorem twoThree_full_residual_norm_le (n : ℕ) :
    ‖twoThreeDualResidual n‖ ≤ ‖twoThreeDual‖ := by
  have ho := twoThree_full_residual_normal n
    ((finiteSpace n).starProjection twoThreeDual)
    ((finiteSpace n).starProjection_apply_mem twoThreeDual)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have he : ‖twoThreeDualResidual n‖^2 =
      ‖twoThreeDual‖^2 - ‖(finiteSpace n).starProjection twoThreeDual‖^2 := by
    unfold twoThreeDualResidual
    rw [norm_sub_sq_real]
    linarith
  nlinarith [sq_nonneg ‖(finiteSpace n).starProjection twoThreeDual‖,
    norm_nonneg (twoThreeDualResidual n), norm_nonneg twoThreeDual]

/-- Only the small head observation is estimated. The tail pairing stays signed. -/
theorem twoThree_actual_trial_head_pair_abs_le
    (N : ℕ) (u : ThresholdHilbert) :
    |inner ℝ (compactHead N (twoThreeDualResidual (N-1)))
        (twoThreeDual - compactHead N u)| ≤
      ‖twoThreeDual‖ * ‖twoThreeDual - compactHead N u‖ := by
  have hnorm : ‖compactHead N (twoThreeDualResidual (N-1))‖ ≤
      ‖twoThreeDual‖ :=
    (compactHead_norm_le N _).trans (twoThree_full_residual_norm_le (N-1))
  have habs : |inner ℝ (compactHead N (twoThreeDualResidual (N-1)))
      (twoThreeDual - compactHead N u)| ≤
      ‖compactHead N (twoThreeDualResidual (N-1))‖ *
        ‖twoThreeDual - compactHead N u‖ := by
    apply abs_le.mpr
    constructor
    · have h := real_inner_le_norm
        (-(compactHead N (twoThreeDualResidual (N-1))))
        (twoThreeDual - compactHead N u)
      rw [inner_neg_left, norm_neg] at h
      linarith
    · exact real_inner_le_norm _ _
  exact habs.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Complete signed trial/full-optimizer physical-tail pairing. -/
def twoThreeTrialTailPairing (N : ℕ) (u : ThresholdHilbert) : ℝ :=
  inner ℝ ((finiteSpace (N-1)).starProjection twoThreeDual -
    compactHead N ((finiteSpace (N-1)).starProjection twoThreeDual))
    (u - compactHead N u)

/-- Signed cancellation can replace all absolute trial-tail estimates.
Open arithmetic obligation: the eventual strict-fraction signed upper bound.
Trial head error must vanish only on the chosen cofinal sequence. -/
theorem riemannHypothesis_of_cofinal_signed_trial_fraction
    (u : ℕ → ThresholdHilbert) (k : ℕ → ℕ) (Z : ℕ → ℝ) (theta : ℝ)
    (hu : ∀ n, u n ∈ finiteSpace (n+2))
    (hk : Tendsto k atTop atTop) (htheta : theta < 1)
    (hhead : Tendsto (fun n =>
      ‖twoThreeDual - compactHead (k n+3) (u (k n))‖) atTop (𝓝 0))
    (hZ : Tendsto Z atTop (𝓝 0))
    (hsigned : ∀ᶠ n in atTop,
      twoThreeTrialTailPairing (k n+3) (u (k n)) ≤
        theta * ‖twoThreeDualResidual (k n+2)‖^2 + Z n) :
    RiemannHypothesis := by
  let D : ℕ → ℝ := fun n => ‖twoThreeDualResidual (n+2)‖^2
  let E : ℕ → ℝ := fun n => ‖twoThreeDual - compactHead (n+3) (u n)‖
  let H : ℕ → ℝ := fun n =>
    inner ℝ (compactHead (n+3) (twoThreeDualResidual (n+2)))
      (twoThreeDual - compactHead (n+3) (u n))
  let L : ℕ → ℝ := fun n => twoThreeTrialTailPairing (n+3) (u n)
  let delta : ℝ := ‖twoThreeDual - closedSpace.starProjection twoThreeDual‖^2
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2) atTop (𝓝 delta) :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkError_tendsto
      residueAtom id Function.surjective_id twoThreeDual
  have hd : Tendsto D atTop (𝓝 delta) :=
    (tendsto_add_atTop_iff_nat 2).mpr hd0
  have hid : ∀ n, D n = H n + L n := by
    intro n
    simpa only [D, H, L, twoThreeTrialTailPairing,
      show n+3-1=n+2 by omega] using
      twoThree_actual_trial_signed_identity (n+3) (by omega) (u n)
        (by simpa only [show n+3-1=n+2 by omega] using hu n)
  have hhb : ∀ᶠ n in atTop, |H (k n)| ≤ ‖twoThreeDual‖ * E (k n) := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [H, E, show k n+3-1=k n+2 by omega] using
      twoThree_actual_trial_head_pair_abs_le (k n+3) (u (k n))
  have hz : delta = 0 :=
    RiemannResearch.Analysis.HeadTailStrengthening.limit_eq_zero_of_signed_cofinal_fraction
      D H L E Z delta ‖twoThreeDual‖ theta k (sq_nonneg _) htheta hk hd
      hhead hZ hhb hid hsigned
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  have hd' : Tendsto (fun n => ‖twoThreeDualResidual n‖^2) atTop (𝓝 0) := by
    simpa only [hz] using hd0
  exact hd'

/-- The complete signed pairing obeys Cauchy with both entire physical
tails. No finite support or discarded composite conductor enters the bound. -/
theorem twoThreeTrialTailPairing_sq_le (N : ℕ) (u : ThresholdHilbert) :
    (twoThreeTrialTailPairing N u)^2 ≤
      ‖u - compactHead N u‖^2 *
      ‖(finiteSpace (N-1)).starProjection twoThreeDual -
        compactHead N ((finiteSpace (N-1)).starProjection twoThreeDual)‖^2 := by
  unfold twoThreeTrialTailPairing
  have h := real_inner_mul_inner_self_le
    ((finiteSpace (N-1)).starProjection twoThreeDual -
      compactHead N ((finiteSpace (N-1)).starProjection twoThreeDual))
    (u - compactHead N u)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  simpa only [pow_two, mul_comm] using h

/-- Approximate head matching is enough: a cofinal vanishing product of the
legal trial's full tail energy and the actual optimizer's full tail energy
implies RH. An exact rank-one head lift is unnecessary. -/
theorem riemannHypothesis_of_cofinal_approximate_head_tail_product
    (u : ℕ → ThresholdHilbert) (k : ℕ → ℕ)
    (hu : ∀ n, u n ∈ finiteSpace (n+2))
    (hk : Tendsto k atTop atTop)
    (hhead : Tendsto (fun n =>
      ‖twoThreeDual - compactHead (k n+3) (u (k n))‖) atTop (𝓝 0))
    (hprod : Tendsto (fun n =>
      ‖u (k n) - compactHead (k n+3) (u (k n))‖^2 *
      ‖(finiteSpace (k n+2)).starProjection twoThreeDual -
        compactHead (k n+3) ((finiteSpace (k n+2)).starProjection twoThreeDual)‖^2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  let D : ℕ → ℝ := fun n => ‖twoThreeDualResidual (n+2)‖^2
  let E : ℕ → ℝ := fun n => ‖twoThreeDual - compactHead (n+3) (u n)‖
  let H : ℕ → ℝ := fun n =>
    inner ℝ (compactHead (n+3) (twoThreeDualResidual (n+2)))
      (twoThreeDual - compactHead (n+3) (u n))
  let L : ℕ → ℝ := fun n => twoThreeTrialTailPairing (n+3) (u n)
  let delta : ℝ := ‖twoThreeDual - closedSpace.starProjection twoThreeDual‖^2
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2) atTop (𝓝 delta) :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkError_tendsto
      residueAtom id Function.surjective_id twoThreeDual
  have hd : Tendsto D atTop (𝓝 delta) :=
    (tendsto_add_atTop_iff_nat 2).mpr hd0
  have hid : ∀ n, D n = H n + L n := by
    intro n
    simpa only [D, H, L, twoThreeTrialTailPairing,
      show n+3-1=n+2 by omega] using
      twoThree_actual_trial_signed_identity (n+3) (by omega) (u n)
        (by simpa only [show n+3-1=n+2 by omega] using hu n)
  have hhb : ∀ᶠ n in atTop, |H (k n)| ≤ ‖twoThreeDual‖ * E (k n) := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [H, E, show k n+3-1=k n+2 by omega] using
      twoThree_actual_trial_head_pair_abs_le (k n+3) (u (k n))
  have hL : Tendsto (fun n => L (k n)) atTop (𝓝 delta) :=
    RiemannResearch.Analysis.HeadTailStrengthening.signed_tail_tendsto_of_head_error_bound
      (fun n => D (k n)) (fun n => H (k n))
      (fun n => L (k n)) (fun n => E (k n)) delta ‖twoThreeDual‖
      (hd.comp hk) hhead hhb (fun n => hid (k n))
  have hCauchy : ∀ᶠ n in atTop,
      (L (k n))^2 ≤
        ‖u (k n) - compactHead (k n+3) (u (k n))‖^2 *
        ‖(finiteSpace (k n+2)).starProjection twoThreeDual -
          compactHead (k n+3) ((finiteSpace (k n+2)).starProjection twoThreeDual)‖^2 := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [L, show k n+3-1=k n+2 by omega] using
      twoThreeTrialTailPairing_sq_le (k n+3) (u (k n))
  have hle : delta^2 ≤ 0 :=
    le_of_tendsto_of_tendsto (hL.pow 2) hprod hCauchy
  have hz : delta = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg delta))
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

end RiemannResearch.RH.Pareto.CoefficientStabilization
