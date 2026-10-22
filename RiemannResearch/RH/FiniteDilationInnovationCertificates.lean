/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.FiniteDilationReciprocalCharge
import RiemannResearch.RH.ReciprocalChargeInnovations
/-!
# Finite signed dilation bounds for actual innovations

Source: Sections 4--5 of the user-provided power-damping and all-dilation
continuation, 24 September 2026. The previously proved finite physical norm
limit is combined with exact biorthogonality and Cauchy--Schwarz.
The arithmetic limiting energy is retained explicitly; no assertion that
optimal certificate energy tends to one or that RH holds is assumed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem finiteDilationReciprocalCharge_mem_finiteSpace_orthogonal
    (S : Finset ℕ) (w : ℕ → ℝ) (Q M : ℕ) (hQ : 0 < Q)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) :
    finiteDilationReciprocalCharge S w Q (M + 1) ∈ (finiteSpace M)ᗮ := by
  apply Submodule.sum_mem
  intro h hh
  apply Submodule.smul_mem
  apply reciprocalChargeRiesz_mem_finiteSpace_orthogonal
  have hle : h ≤ Q := Nat.le_of_dvd hQ (hSQ h hh)
  have hdiv : 1 ≤ Q / h := Nat.div_pos hle (hS h hh)
  nlinarith

theorem finiteDilationReciprocalCharge_inner_consecutive
    (S : Finset ℕ) (w : ℕ → ℝ) (Q M : ℕ) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) (hQS : Q ∈ S) :
    inner ℝ (finiteDilationReciprocalCharge S w Q (M + 1))
      (consecutiveResidueHilbert M) = w Q := by
  unfold finiteDilationReciprocalCharge
  rw [sum_inner]
  have he (h : ℕ) (hh : h ∈ S) :
      (Q / h) * (M + 1) = M + 1 ↔ h = Q := by
    constructor
    · intro heq
      have hdiv : Q / h = 1 := by nlinarith
      have hc := Nat.div_mul_cancel (hSQ h hh)
      simpa [hdiv] using hc
    · rintro rfl
      rw [Nat.div_self hQ, one_mul]
  have hterm (h : ℕ) (hh : h ∈ S) :
      inner ℝ (w h • reciprocalChargeRiesz ((Q / h) * (M + 1)))
        (consecutiveResidueHilbert M) = if h = Q then w Q else 0 := by
    rw [inner_smul_left]
    have hdiv : 0 < Q / h := Nat.div_pos (Nat.le_of_dvd hQ (hSQ h hh)) (hS h hh)
    rw [reciprocalChargeRiesz_consecutive_biorthogonal _ M (by positivity) hM]
    simp only [he h hh, RCLike.conj_to_real]
    split_ifs with hhQ
    · simp [hhQ]
    · simp
  rw [Finset.sum_congr rfl hterm]
  simp [hQS]

theorem finiteDilationReciprocalCharge_innovation_bound
    (S : Finset ℕ) (w : ℕ → ℝ) (Q M : ℕ) (hQ : 0 < Q) (hM : 1 ≤ M)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) (hQS : Q ∈ S) :
    w Q ^ 2 ≤ ‖finiteDilationReciprocalCharge S w Q (M + 1)‖ ^ 2 *
      ‖consecutiveResidueHilbert M -
        (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 := by
  let A := finiteDilationReciprocalCharge S w Q (M + 1)
  let z := consecutiveResidueHilbert M -
    (finiteSpace M).starProjection (consecutiveResidueHilbert M)
  have ho : inner ℝ A
      ((finiteSpace M).starProjection (consecutiveResidueHilbert M)) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace M).mem_orthogonal _).mp
      (finiteDilationReciprocalCharge_mem_finiteSpace_orthogonal S w Q M hQ hS hSQ) _
      ((finiteSpace M).starProjection_apply_mem _)
  have he : inner ℝ A z = w Q := by
    dsimp [z]
    rw [inner_sub_right, ho, sub_zero]
    exact finiteDilationReciprocalCharge_inner_consecutive S w Q M hQ hM hS hSQ hQS
  have hc := real_inner_mul_inner_self_le A z
  rw [he, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  simpa only [pow_two] using hc

theorem finiteDilationReciprocalCharge_eventually_innovation_gt
    (S : Finset ℕ) (w : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hS : ∀ h ∈ S, 0 < h) (hSQ : ∀ h ∈ S, h ∣ Q) (hQS : Q ∈ S)
    (c : ℝ)
    (he : c * (∑' n, finiteDilationMobiusCoefficient S w n ^ 2) < w Q ^ 2) :
    ∀ᶠ M : ℕ in atTop, c <
      ‖consecutiveResidueHilbert M -
        (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 := by
  have hs : Tendsto (fun M : ℕ => M + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop K] with M hM
    omega
  have ht := (finiteDilationReciprocalCharge_norm_sq_tendsto S w Q hQ hS hSQ).comp hs
  have hm := ht.const_mul c
  have hev : ∀ᶠ M : ℕ in atTop,
      c * ‖finiteDilationReciprocalCharge S w Q (M + 1)‖ ^ 2 < w Q ^ 2 :=
    hm.eventually (gt_mem_nhds he)
  filter_upwards [hev, eventually_ge_atTop 1] with M hlt hM
  have hb := finiteDilationReciprocalCharge_innovation_bound S w Q M hQ hM hS hSQ hQS
  have hn := sq_nonneg ‖finiteDilationReciprocalCharge S w Q (M + 1)‖
  by_contra h
  have hle := le_of_not_gt h
  have hh := mul_le_mul_of_nonneg_left hle hn
  nlinarith
end RiemannResearch.RH.Pareto.CoefficientStabilization
