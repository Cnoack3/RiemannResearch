import RiemannResearch.RH.QFloorDyadicEnergy
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoUnitSignal
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.Analysis.UnitSignalTwoScale
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual all-conductor unit-signal dilation and detector

Source: the user-provided unit-signal manuscript, Sections 4--6, and the
18 October 2026 continuation request, for the projection/dilation strategy.
The operator, legal closure, finite inverse-Gram candidates, unit-signal
normalization, and scalar algebra are reused from their owning modules.

The polynomial detector is unconditional. Finite and cofinal scalar lower
allowances remain explicit hypotheses. This module neither asserts their
arithmetic providers nor substitutes squarefree stages for unrestricted ones.
See UnitSignalDilationResearch20261018.md for exact identities and status.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoUnitSignalDilation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParitySignal ZetaTwoUnitSignal QFloorDilation
open RiemannResearch.Analysis.UnitSignalTwoScale
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The actual constant-projection residual in an orthogonally complemented space. -/
def residual (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] : QHilbert :=
  qOne - S.starProjection qOne

theorem residual_inner_mem (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (f : QHilbert) (hf : f ∈ S) : ⟪residual S, f⟫ = 0 := by
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal hf
    (Submodule.sub_starProjection_mem_orthogonal (K := S) qOne)

theorem residual_inner_qOne (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] :
    ⟪residual S, qOne⟫ = qUnitSignalDefect S := by
  have hz := residual_inner_mem S (S.starProjection qOne) (S.starProjection_apply_mem qOne)
  have hsum : qOne = residual S + S.starProjection qOne := by
    simp [residual]
  calc
    ⟪residual S, qOne⟫ = ⟪residual S, residual S + S.starProjection qOne⟫ := by
      conv_lhs => rw [hsum]
    _ = qUnitSignalDefect S := by
      rw [inner_add_right, hz, add_zero, real_inner_self_eq_norm_sq]
      rfl

theorem inner_qPoint_zero (f : QHilbert) :
    ⟪f, qPoint 0⟫ = qSequence f 1 / zetaTwo := by
  rw [real_inner_comm, qPoint_inner]
  norm_num [qWeight, positiveQWeight]
  ring

/-- Exact signed boundary identity, before any Cauchy--Schwarz estimate. -/
theorem two_space_head_identity (S R : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] [R.HasOrthogonalProjection]
    (hmap : ∀ f ∈ S, floorDilation 2 (by norm_num) f ∈ R) :
    ⟪residual R, floorDilation 2 (by norm_num) (residual S)⟫ =
      qUnitSignalDefect R - qSequence (residual R) 1 / zetaTwo := by
  have hz := residual_inner_mem R _ (hmap _ (S.starProjection_apply_mem qOne))
  change ⟪residual R, floorDilation 2 (by norm_num) (qOne - S.starProjection qOne)⟫ = _
  rw [map_sub, inner_sub_right, hz, sub_zero, floorDilation_two_qOne,
    inner_sub_right, residual_inner_qOne, inner_qPoint_zero]

/-- Two-space estimate from actual legality and the complete dyadic energy bound. -/
theorem two_space_dilation_bound (S R : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] [R.HasOrthogonalProjection]
    (hmap : ∀ f ∈ S, floorDilation 2 (by norm_num) f ∈ R) :
    (qUnitSignalDefect R - qSequence (residual R) 1 / zetaTwo) ^ 2 ≤
      qUnitSignalDefect R * qUnitSignalDefect S / 2 := by
  have hc := real_inner_mul_inner_self_le (residual R)
    (floorDilation 2 (by norm_num) (residual S))
  rw [← pow_two, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    two_space_head_identity S R hmap] at hc
  have hb := mul_le_mul_of_nonneg_left
    (floorDilation_two_norm_sq_le_half (residual S)) (sq_nonneg ‖residual R‖)
  change (qUnitSignalDefect R - qSequence (residual R) 1 / zetaTwo) ^ 2 ≤
    ‖residual R‖ ^ 2 * ‖residual S‖ ^ 2 / 2
  nlinarith

/-- The unit-signal closure is the already established full legal closure. -/
theorem allConductorSpace_eq_fullClosure :
    allConductorSpace = QFullResidueProjection.closure := rfl

theorem floorDilation_mem_allConductorSpace (m : ℕ) (hm : 0 < m)
    (f : QHilbert) (hf : f ∈ allConductorSpace) :
    floorDilation m hm f ∈ allConductorSpace := by
  exact floorDilation_mem_legalClosure m hm f hf

theorem allConductorStage_mem_residue (n d : ℕ) (hd : 2 ≤ d) (hN : d ≤ n + 3) :
    qResidue d ∈ allConductorStage n := by
  change qResidue d ∈ Submodule.span ℝ
    (Set.range (fun i : Fin (n + 2) => allConductorDictionary (i : ℕ)))
  apply Submodule.subset_span
  refine ⟨⟨d - 2, by omega⟩, ?_⟩
  change qResidue (d - 2 + 2) = qResidue d
  congr 1
  omega

/-- Cutoff N = n + 3 is sent to cutoff 2N, whose index is 2n + 3. -/
theorem floorDilation_two_mem_stage (n : ℕ) (f : QHilbert)
    (hf : f ∈ allConductorStage n) :
    floorDilation 2 (by norm_num) f ∈ allConductorStage (2 * n + 3) := by
  change f ∈ Submodule.span ℝ
    (Set.range (fun i : Fin (n + 2) => allConductorDictionary (i : ℕ))) at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩
    change floorDilation 2 (by norm_num) (qResidue (i.val + 2)) ∈ _
    rw [floorDilation_qResidue 2 (i.val + 2) (by norm_num) (by omega)]
    exact (allConductorStage (2 * n + 3)).sub_mem
      (allConductorStage_mem_residue _ _ (by omega) (by have hi := i.isLt; omega))
      ((allConductorStage (2 * n + 3)).smul_mem _ (allConductorStage_mem_two _))
  | zero => simpa only [map_zero] using (allConductorStage (2 * n + 3)).zero_mem
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact (allConductorStage (2 * n + 3)).add_mem ihx ihy
  | smul c x hx ihx =>
    rw [map_smul]
    exact (allConductorStage (2 * n + 3)).smul_mem c ihx

/-- Unconditional two-scale estimate for the actual finite projection residuals. -/
theorem allConductor_finite_two_scale (n : ℕ) :
    (qUnitSignalDefect (allConductorStage (2 * n + 3)) -
      qSequence (residual (allConductorStage (2 * n + 3))) 1 / zetaTwo) ^ 2 ≤
    qUnitSignalDefect (allConductorStage (2 * n + 3)) *
      qUnitSignalDefect (allConductorStage n) / 2 :=
  two_space_dilation_bound _ _ (floorDilation_two_mem_stage n)

/-- The precise positive normalization used by the unit-signal model. -/
theorem optimizer_eq_scaled_projection (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (h2 : qResidue 2 ∈ S) (h3 : qResidue 3 ∈ S) :
    qUnitSignalOptimizer S h2 h3 =
      (1 / (1 - 4 * qUnitSignalDefect S)) • S.starProjection qEven := by
  have he := (unitSignalModel S h2 h3).defect_eq
  rw [unitSignalModel_defect, unitSignalModel_mass] at he
  have he' : (unitSignalModel S h2 h3).energy = 1 / 4 - qUnitSignalDefect S := by
    linarith
  change ⟪S.starProjection qEven, S.starProjection qEven⟫ =
    1 / 4 - qUnitSignalDefect S at he'
  rw [qUnitSignalOptimizer_eq_projection, he']
  congr 1
  have ht := qUnitSignal_denominator_pos S h2 h3
  have hq : (1:ℝ) / 4 - qUnitSignalDefect S ≠ 0 := by linarith
  field_simp [hq, ne_of_gt ht]

/-- The physical first coordinate, including its sign and normalization denominator. -/
theorem optimizer_first_eq_residual (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (h2 : qResidue 2 ∈ S) (h3 : qResidue 3 ∈ S) :
    qSequence (qUnitSignalOptimizer S h2 h3) 1 =
      -qSequence (residual S) 1 / (1 - 4 * qUnitSignalDefect S) := by
  have hr : qSequence (residual S) 1 = -qSequence (S.starProjection qEven) 1 := by
    rw [residual, qOne_residual_eq_qEven_residual S h2]
    change qSequenceLinear (qEven - S.starProjection qEven) 1 = _
    rw [map_sub]
    change qSequence qEven 1 - qSequence (S.starProjection qEven) 1 = _
    rw [qEven_at_one]
    ring
  rw [optimizer_eq_scaled_projection, hr]
  change qSequenceLinear ((1 / (1 - 4 * qUnitSignalDefect S)) •
    S.starProjection qEven) 1 = _
  rw [map_smul]
  change (1 / (1 - 4 * qUnitSignalDefect S)) * qSequence (S.starProjection qEven) 1 = _
  ring

/-- The actual limiting detector, with no additional arithmetic hypothesis. -/
theorem allConductorLimit_polynomial_detector :
    2 * (zetaTwo * ‖allConductorLimit - qEven‖ ^ 2 +
      qSequence allConductorLimit 1) ^ 2 ≤
      (zetaTwo * ‖allConductorLimit - qEven‖ ^ 2) ^ 2 := by
  let δ := qUnitSignalDefect allConductorSpace
  let r := qSequence (residual allConductorSpace) 1
  let t := 1 - 4 * δ
  have ht : 0 < t := qUnitSignal_denominator_pos allConductorSpace
    allConductorSpace_mem_two allConductorSpace_mem_three
  have hd : (δ-r / zetaTwo) ^ 2 ≤ δ * δ / 2 :=
    two_space_dilation_bound allConductorSpace allConductorSpace
      (floorDilation_mem_allConductorSpace 2 (by norm_num))
  have he : ‖allConductorLimit - qEven‖ ^ 2 = δ / t := allConductorLimit_error
  have hl : qSequence allConductorLimit 1 = -r / t :=
    optimizer_first_eq_residual allConductorSpace
      allConductorSpace_mem_two allConductorSpace_mem_three
  rw [he, hl]
  have ha : zetaTwo * (δ / t) + -r / t = (zetaTwo / t) * (δ-r / zetaTwo) := by
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt ht]
    ring
  calc
    2 * (zetaTwo * (δ / t) + -r / t) ^ 2 =
        (zetaTwo / t) ^ 2 * (2 * (δ-r / zetaTwo) ^ 2) := by rw [ha]; ring
    _ ≤ (zetaTwo / t) ^ 2 * δ ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [hd]) (sq_nonneg _)
    _ = (zetaTwo * (δ / t)) ^ 2 := by ring

theorem allConductorLimit_first_nonpositive :
    qSequence allConductorLimit 1 ≤ 0 :=
  detector_nonpositive _ _ _ zetaTwo_pos (sq_nonneg _) allConductorLimit_polynomial_detector

theorem allConductorLimit_first_zero_iff_error_zero :
    qSequence allConductorLimit 1 = 0 ↔ ‖allConductorLimit - qEven‖ ^ 2 = 0 :=
  detector_zero_iff _ _ _ zetaTwo_pos allConductorLimit_polynomial_detector

/-- Hilbert convergence implies convergence of the physical first coordinate. -/
theorem allConductorFirst_tendsto :
    Tendsto (fun n => qSequence (allConductorOptimizer n) 1) atTop
      (𝓝 (qSequence allConductorLimit 1)) := by
  have h := (tendsto_const_nhds.inner allConductorOptimizer_tendsto :
    Tendsto (fun n => ⟪qPoint 0, allConductorOptimizer n⟫) atTop
      (𝓝 ⟪qPoint 0, allConductorLimit⟫))
  have h' := h.div_const (qWeight 0)
  simpa only [qPoint_inner, Nat.zero_add, mul_div_cancel_left₀ _ (ne_of_gt (qWeight_pos 0))]
    using h'

/-- Conditional reduction: the cofinal scalar allowance remains an explicit open input. -/
theorem allConductorLimit_error_zero_of_subsequence_allowance
    (index : ℕ → ℕ) (allowance : ℕ → ℝ)
    (hindex : Tendsto index atTop atTop)
    (hallowance : Tendsto allowance atTop (𝓝 0))
    (hlower : ∀ᶠ j in atTop,
      -(zetaTwo * ‖allConductorOptimizer (index j) - qEven‖ ^ 2) / 4 - allowance j ≤
        qSequence (allConductorOptimizer (index j)) 1) :
    ‖allConductorLimit - qEven‖ ^ 2 = 0 :=
  limit_zero_of_eventual_quarter_allowance _ _ _ _ _ _ zetaTwo_pos (sq_nonneg _)
    (allConductorError_tendsto.comp hindex) (allConductorFirst_tendsto.comp hindex)
    hallowance hlower allConductorLimit_polynomial_detector

/-- The finite two-scale estimate in the normalized optimizer's actual coordinates. -/
theorem allConductor_normalized_two_scale (n : ℕ) :
    (qUnitSignalDefect (allConductorStage (2 * n + 3)) +
      (1 - 4 * qUnitSignalDefect (allConductorStage (2 * n + 3))) *
        qSequence (allConductorOptimizer (2 * n + 3)) 1 / zetaTwo) ^ 2 ≤
      qUnitSignalDefect (allConductorStage (2 * n + 3)) *
        qUnitSignalDefect (allConductorStage n) / 2 := by
  have ht := qUnitSignal_denominator_pos (allConductorStage (2 * n + 3))
    (allConductorStage_mem_two _) (allConductorStage_mem_three _)
  have hf : (1 - 4 * qUnitSignalDefect (allConductorStage (2 * n + 3))) *
      qSequence (allConductorOptimizer (2 * n + 3)) 1 =
      -qSequence (residual (allConductorStage (2 * n + 3))) 1 := by
    change (1 - 4 * qUnitSignalDefect (allConductorStage (2 * n + 3))) *
      qSequence (qUnitSignalOptimizer _ _ _) 1 = _
    rw [optimizer_first_eq_residual]
    field_simp [ne_of_gt ht]
  rw [hf]
  convert allConductor_finite_two_scale n using 1
  ring

/-- Conditional finite estimate; no provider of the scalar allowance is asserted. -/
theorem allConductor_finite_quarter_allowance (n : ℕ) (ε : ℝ)
    (hlower :
      -(zetaTwo * ‖allConductorOptimizer (2 * n + 3) - qEven‖ ^ 2) / 4 - ε ≤
        qSequence (allConductorOptimizer (2 * n + 3)) 1) :
    qUnitSignalDefect (allConductorStage (2 * n + 3)) ≤
      (8 / 9 : ℝ) * qUnitSignalDefect (allConductorStage n) +
      (8 / 3 : ℝ) * ((1 - 4 * qUnitSignalDefect (allConductorStage (2 * n + 3))) * ε /
        zetaTwo) := by
  let x := qUnitSignalDefect (allConductorStage (2 * n + 3))
  let y := qUnitSignalDefect (allConductorStage n)
  let t := 1 - 4 * x
  let ell := qSequence (allConductorOptimizer (2 * n + 3)) 1
  have ht : 0 < t := qUnitSignal_denominator_pos (allConductorStage (2 * n + 3))
    (allConductorStage_mem_two _) (allConductorStage_mem_three _)
  have he : ‖allConductorOptimizer (2 * n + 3) - qEven‖ ^ 2 = x / t :=
    qUnitSignalOptimizer_error _ (allConductorStage_mem_two _) (allConductorStage_mem_three _)
  rw [he] at hlower
  have hm := mul_le_mul_of_nonneg_left hlower (le_of_lt (div_pos ht zetaTwo_pos))
  have hleft : (t / zetaTwo) * (-(zetaTwo * (x / t)) / 4 - ε) =
      -x / 4 - t * ε / zetaTwo := by
    field_simp [ne_of_gt ht, ne_of_gt zetaTwo_pos]
  have hz : -x / 4 - t * ε / zetaTwo ≤ t * ell / zetaTwo := by
    rw [hleft] at hm
    calc
      _ ≤ (t / zetaTwo) * ell := hm
      _ = t * ell / zetaTwo := by ring
  exact two_scale_quarter_relaxed x y (t * ell / zetaTwo) (t * ε / zetaTwo)
    (qUnitSignalDefect_nonneg _) (qUnitSignalDefect_nonneg _)
    (allConductor_normalized_two_scale n) hz

/-- First coordinate in terms of the actual inverse-Gram projection coefficients. -/
theorem allConductor_residual_first_inverseGram (n : ℕ) :
    qSequence (residual (allConductorStage n)) 1 =
      1 - ∑ i : Fin (n + 2),
        QFullResidueProjection.coefficients (n + 2) i / ((i.val : ℝ) + 2) := by
  have hp : (allConductorStage n).starProjection qOne =
      QFullResidueProjection.candidate (n + 2) :=
    (QFullResidueProjection.candidate_eq_projection (n + 2)).symm
  have hc : qSequence (QFullResidueProjection.candidate (n + 2)) 1 =
      ∑ i : Fin (n + 2),
        QFullResidueProjection.coefficients (n + 2) i / ((i.val : ℝ) + 2) := by
    change qSequenceLinear
      (∑ i : Fin (n + 2), QFullResidueProjection.coefficients (n + 2) i •
        qResidue (i.val + 2)) 1 = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ i : Fin (n + 2), QFullResidueProjection.coefficients (n + 2) i *
      qSequence (qResidue (i.val + 2)) 1) = _
    apply Finset.sum_congr rfl
    intro i hi
    rw [qSequence_qResidue]
    simp only [ArithmeticCumulative.residueFraction,
      Nat.mod_eq_of_lt (show 1 < i.val + 2 by omega), Nat.cast_one,
      Nat.cast_add, Nat.cast_ofNat]
    ring
  change qSequenceLinear (qOne - (allConductorStage n).starProjection qOne) 1 = _
  rw [map_sub]
  change qSequence qOne 1 - qSequence ((allConductorStage n).starProjection qOne) 1 = _
  rw [hp, hc, qSequence_qOne]
  norm_num [qOneSequence]

/-- The projection coefficients and the unit-signal coefficients are not identified. -/
theorem allConductor_optimizer_first_inverseGram (n : ℕ) :
    qSequence (allConductorOptimizer n) 1 =
      ((∑ i : Fin (n + 2),
        QFullResidueProjection.coefficients (n + 2) i / ((i.val : ℝ) + 2)) - 1) /
          (1 - 4 * qUnitSignalDefect (allConductorStage n)) := by
  change qSequence (qUnitSignalOptimizer _ _ _) 1 = _
  rw [optimizer_first_eq_residual, allConductor_residual_first_inverseGram]
  ring

/-- The vanishing error is exactly the all-conductor constant-closure obligation. -/
theorem allConductorLimit_error_zero_iff_constant_mem :
    ‖allConductorLimit - qEven‖ ^ 2 = 0 ↔ qOne ∈ allConductorSpace := by
  constructor
  · intro he
    have hn : ‖allConductorLimit - qEven‖ = 0 := by
      nlinarith [norm_nonneg (allConductorLimit - qEven)]
    have hEq : allConductorLimit = qEven := sub_eq_zero.mp (norm_eq_zero.mp hn)
    apply (qOne_mem_iff_qEven_mem allConductorSpace allConductorSpace_mem_two).mpr
    have hm : allConductorLimit ∈ allConductorSpace :=
      (qUnitSignalOptimizer_admissible allConductorSpace
        allConductorSpace_mem_two allConductorSpace_mem_three).1
    rwa [hEq] at hm
  · intro hm
    rw [allConductorLimit_error, qUnitSignalDefect,
      Submodule.starProjection_eq_self_iff.mpr hm]
    simp

theorem allConductorLimit_error_zero_of_quarter_lower_bound
    (hlower : -(zetaTwo * ‖allConductorLimit - qEven‖ ^ 2) / 4 ≤
      qSequence allConductorLimit 1) :
    ‖allConductorLimit - qEven‖ ^ 2 = 0 :=
  detector_zero_of_quarter_lower_bound _ _ _ zetaTwo_pos (sq_nonneg _)
    allConductorLimit_polynomial_detector hlower

/-- The remaining scalar lower bound has the full strength of vanishing error. -/
theorem allConductorLimit_error_zero_iff_quarter_lower_bound :
    ‖allConductorLimit - qEven‖ ^ 2 = 0 ↔
      -(zetaTwo * ‖allConductorLimit - qEven‖ ^ 2) / 4 ≤
        qSequence allConductorLimit 1 := by
  constructor
  · intro he
    have hl := allConductorLimit_first_zero_iff_error_zero.mpr he
    rw [he, hl]
    norm_num
  · exact allConductorLimit_error_zero_of_quarter_lower_bound


/-- Exact decomposition of the two-scale slack into dilation and Cauchy--Schwarz losses. -/
theorem two_space_slack_identity (S R : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] [R.HasOrthogonalProjection]
    (hmap : ∀ f ∈ S, floorDilation 2 (by norm_num) f ∈ R) :
    qUnitSignalDefect R * qUnitSignalDefect S / 2 -
        (qUnitSignalDefect R - qSequence (residual R) 1 / zetaTwo) ^ 2 =
      qUnitSignalDefect R *
        (qUnitSignalDefect S / 2 - ‖floorDilation 2 (by norm_num) (residual S)‖ ^ 2) +
      (qUnitSignalDefect R * ‖floorDilation 2 (by norm_num) (residual S)‖ ^ 2 -
        ⟪residual R, floorDilation 2 (by norm_num) (residual S)⟫ ^ 2) := by
  rw [two_space_head_identity S R hmap]
  ring

/-- Literal inverse-Gram form of the remaining finite scalar allowance. -/
theorem allConductor_quarter_allowance_iff_inverseGram (n : ℕ) (ε : ℝ) :
    (-(zetaTwo * ‖allConductorOptimizer n - qEven‖ ^ 2) / 4 - ε ≤
        qSequence (allConductorOptimizer n) 1) ↔
      1 - zetaTwo * qUnitSignalDefect (allConductorStage n) / 4 -
        (1 - 4 * qUnitSignalDefect (allConductorStage n)) * ε ≤
          ∑ i : Fin (n + 2),
            QFullResidueProjection.coefficients (n + 2) i / ((i.val : ℝ) + 2) := by
  let δ := qUnitSignalDefect (allConductorStage n)
  let t := 1 - 4 * δ
  have ht : 0 < t := qUnitSignal_denominator_pos (allConductorStage n)
    (allConductorStage_mem_two n) (allConductorStage_mem_three n)
  have he : ‖allConductorOptimizer n - qEven‖ ^ 2 = δ / t :=
    qUnitSignalOptimizer_error _ (allConductorStage_mem_two n) (allConductorStage_mem_three n)
  have hleft : -(zetaTwo * (δ / t)) / 4 - ε = (-zetaTwo * δ / 4 - t * ε) / t := by
    field_simp [ne_of_gt ht]
  rw [he, allConductor_optimizer_first_inverseGram, hleft]
  change ((-zetaTwo * δ / 4 - t * ε) / t ≤
    ((∑ i : Fin (n + 2), QFullResidueProjection.coefficients (n + 2) i /
      ((i.val : ℝ) + 2)) - 1) / t) ↔ _
  rw [div_le_div_iff_of_pos_right ht]
  dsimp only [t, δ]
  constructor <;> intro h <;> linarith

end RiemannResearch.RH.ZetaTwoUnitSignalDilation
