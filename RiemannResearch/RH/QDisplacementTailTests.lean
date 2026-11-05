/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.RH.QPhysicalTailEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The displacement tested against legal vectors supported on a tail

The matched projection equations supply an extra inverse power on a test
vanishing through a prescribed physical site. Bounded physical tests gain
a further inverse square root. The signed identity retains the complete
tail of the actual Pareto residual.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRegularity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open QShiftedReciprocal QAnnihilatorTailEscape QFiniteSupportDualCriterion

private theorem coord_zero_of_head (v : QHilbert) (N : ℕ)
    (hz : ∀ n ≤ N, qSequence v n = 0) {j : ℕ} (hj : j < N) : v j = 0 := by
  have h := hz (j + 1) (by omega)
  rw [qSequence_succ, div_eq_zero_iff] at h
  exact h.resolve_right (Real.sqrt_pos.mpr (qWeight_pos j)).ne'

/-- A vector vanishing through the physical cutoff equals its tail. -/
theorem tail_eq_self_of_head (v : QHilbert) (N : ℕ)
    (hz : ∀ n ≤ N, qSequence v n = 0) : tail N v = v := by
  have h0 : finiteHead N v = 0 := by
    apply Subtype.ext
    funext j
    change finiteHead N v j = 0
    by_cases hj : j < N
    · rw [finiteHead_apply_of_lt _ _ _ hj]
      exact coord_zero_of_head v N hz hj
    · exact finiteHead_apply_eq_zero _ _ _ (by omega)
  rw [tail, h0, sub_zero]

/-- Restricted to physical sites strictly above N, the denominator of B is at least N+2. -/
theorem scaled_B_norm_le_of_head (v : QHilbert) (N : ℕ)
    (hz : ∀ n ≤ N, qSequence v n = 0) : ((N : ℝ) + 2) * ‖B v‖ ≤ ‖v‖ := by
  have hs : ‖((N : ℝ) + 2) • B v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _) (qCoordinate_square_summable _)
    intro j
    change (((N : ℝ) + 2) * (v j / ((j : ℝ) + 2))) ^ 2 ≤ (v j) ^ 2
    by_cases hj : j < N
    · simp [coord_zero_of_head v N hz hj]
    · have hNj : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast (le_of_not_gt hj)
      have hq : ((N : ℝ) + 2) / ((j : ℝ) + 2) ≤ 1 :=
        (div_le_iff₀ (by positivity)).mpr (by linarith)
      have hq0 : (0 : ℝ) ≤ ((N : ℝ) + 2) / ((j : ℝ) + 2) := by positivity
      have hq2 := (sq_le_sq₀ hq0 zero_le_one).mpr hq
      rw [show ((N : ℝ) + 2) * (v j / ((j : ℝ) + 2)) =
        (((N : ℝ) + 2) / ((j : ℝ) + 2)) * v j by ring, mul_pow]
      simpa using mul_le_mul_of_nonneg_right hq2 (sq_nonneg (v j))
  have hnorm := le_of_sq_le_sq hs (norm_nonneg v)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 2)]
    using hnorm

/-- The signed pairing with a legal test sees only the Pareto residual on the same tail. -/
theorem inner_displacement_eq_tail_of_head (v : QHilbert) (N : ℕ)
    (hv : v ∈ closure) (hz : ∀ n ≤ N, qSequence v n = 0) :
    inner ℝ v displacement = inner ℝ (B v) (tail N pResidual) := by
  have h0 : inner ℝ (B v) (finiteHead N pResidual) = 0 := by
    rw [inner_finiteHead_eq_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [B_apply, coord_zero_of_head v N hz (Finset.mem_range.mp hj), zero_div, mul_zero]
  rw [displacement_normal_equation _ hv, ← B_symmetric, tail, inner_sub_right, h0, sub_zero]

/-- The extra inverse power, with the actual residual tail retained. -/
theorem scaled_inner_displacement_le_of_head (v : QHilbert) (N : ℕ)
    (hv : v ∈ closure) (hz : ∀ n ≤ N, qSequence v n = 0) :
    ((N : ℝ) + 2) * |inner ℝ v displacement| ≤ ‖v‖ * ‖tail N pResidual‖ := by
  rw [inner_displacement_eq_tail_of_head v N hv hz]
  calc
    _ ≤ ((N : ℝ) + 2) * (‖B v‖ * ‖tail N pResidual‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (scaled_B_norm_le_of_head v N hz) (norm_nonneg _)

/-- Uniformly bounded, tail-supported, legal physical tests have displacement pairing
o(N^(-3/2)); the cutoff may run through any cofinal sequence. -/
theorem scaled_inner_displacement_tendsto_zero
    (v : ℕ → QHilbert) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hv : ∀ j, v j ∈ closure) (hz : ∀ j n, n ≤ N j → qSequence (v j) n = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ j n, |qSequence (v j) n| ≤ C) :
    Tendsto (fun j => Real.sqrt ((N j : ℝ) + 1) * ((N j : ℝ) + 2) *
      |inner ℝ (v j) displacement|) atTop (𝓝 0) := by
  let K := Real.sqrt (2 * C^2 / zetaTwo)
  have ht : Tendsto (fun j => K * ‖tail (N j) pResidual‖) atTop (𝓝 0) := by
    simpa using (((tail_tendsto_zero pResidual).comp hN).norm.const_mul K)
  apply squeeze_zero (fun j => by positivity) _ ht
  intro j
  have h := zeta_mul_tail_energy_le_of_bounded (v j) (N j) C hC (hb j)
  rw [tail_eq_self_of_head _ _ (hz j)] at h
  have hpos : 0 < (N j : ℝ) + 1 := by positivity
  have hnorm : Real.sqrt ((N j : ℝ) + 1) * ‖v j‖ ≤ K := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [mul_pow, Real.sq_sqrt hpos.le, show K ^ 2 = 2 * C^2 / zetaTwo from
      Real.sq_sqrt (div_nonneg (by positivity) zetaTwo_pos.le)]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    nlinarith only [(le_div_iff₀ hpos).mp h]
  calc
    _ = Real.sqrt ((N j : ℝ) + 1) * (((N j : ℝ) + 2) * |inner ℝ (v j) displacement|) := by ring
    _ ≤ Real.sqrt ((N j : ℝ) + 1) * (‖v j‖ * ‖tail (N j) pResidual‖) :=
      mul_le_mul_of_nonneg_left (scaled_inner_displacement_le_of_head _ _ (hv j) (hz j))
        (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

end RiemannResearch.RH.QSquarefreeDisplacementRegularity
