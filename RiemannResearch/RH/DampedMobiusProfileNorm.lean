/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusHalfHilbertRate

/-!
# General profile transfer for half-endpoint Hilbert errors

A conductor-uniform coordinate estimate `K sqrt(n) exp(-a φ(n))` and a
finite-head energy estimate `D exp(-a φ(M))` imply a norm estimate with
coefficient `a/2`. The analytic inputs are monotonicity of the profile
at positive indices and summability of its physical kernel. Neither
nonnegativity of the profile nor any particular formula for it is needed.

Arithmetic applications must discharge the coordinate and head premises.
These statements do not establish energy at a fixed subhalf damping.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

def halfProfileKernel (a : ℝ) (φ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * Real.exp (-a * φ n)

theorem halfProfileKernel_nonneg (a : ℝ) (φ : ℕ → ℝ) (n : ℕ) :
    0 ≤ halfProfileKernel a φ n := by
  unfold halfProfileKernel
  positivity

/-- Algebraic physical-energy comparison for an arbitrary profile. -/
theorem positiveWeight_sq_le_profile
    {x K a : ℝ} {φ : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hx : |x| ≤ K * Real.sqrt (n : ℝ) * Real.exp (-a * φ n)) :
    positiveWeight n * x ^ 2 ≤
      K ^ 2 * Real.exp (-a * φ n) * halfProfileKernel a φ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := mul_self_le_mul_self (abs_nonneg x) hx
  have hsq : x ^ 2 ≤ K ^ 2 * (n : ℝ) * (Real.exp (-a * φ n)) ^ 2 := by
    simpa only [← pow_two, sq_abs, mul_pow, Real.sq_sqrt hn0.le] using hs
  have hnplus : 0 < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ positiveWeight n * (K ^ 2 * (n : ℝ) * (Real.exp (-a * φ n)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)
    _ = (K ^ 2 * (Real.exp (-a * φ n)) ^ 2) / ((n : ℝ) + 1) := by
      unfold positiveWeight
      field_simp [hn0.ne', hnplus.ne']
    _ ≤ (K ^ 2 * (Real.exp (-a * φ n)) ^ 2) / (n : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hn0
      linarith
    _ = _ := by unfold halfProfileKernel; ring

/-- Every monotone summable physical profile propagates through the
finite physical-head and infinite physical-tail norm decomposition. -/
theorem dampedMobius_half_cutoffs_eventual_profile_rate_of_coordinate_and_head
    {a K D : ℝ} (φ : ℕ → ℝ) (ha : 0 < a) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → φ m ≤ φ n)
    (hsumm : Summable (halfProfileKernel a φ))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |hilbertSequence
        (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n| ≤
      K * Real.sqrt (n : ℝ) * Real.exp (-a * φ n))
    (hhead : ∀ᶠ M : ℕ in atTop,
      (∑ n ∈ Finset.range M, positiveWeight n *
        (hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
            dampedMobiusHalfRangeLimit (1 / 2) le_rfl) n) ^ 2) ≤
      D * Real.exp (-a * φ M)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
      C * Real.exp (-(a / 2) * φ M) := by
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  obtain ⟨hcoord, _hconv⟩ := dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hfb (n : ℕ) (hn : N ≤ n) :
      |hilbertSequence f n| ≤ K * Real.sqrt (n : ℝ) * Real.exp (-a * φ n) := by
    have ht : Tendsto (fun M =>
        hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n)
        atTop (𝓝 (hilbertSequence f n)) := by
      rw [show hilbertSequence f n = dampedMobiusPrefix (1 / 2) n -
        (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re from hcoord n]
      exact dampedMobius_partial_coordinate_tendsto (by norm_num) n
    exact le_of_tendsto ht.abs (Eventually.of_forall (hN n hn))
  let S : ℝ := ∑' n : ℕ, halfProfileKernel a φ n
  have hS : 0 ≤ S := tsum_nonneg (halfProfileKernel_nonneg a φ)
  have hconstant : 0 ≤ D + 4 * K ^ 2 * S := by positivity
  refine ⟨Real.sqrt (D + 4 * K ^ 2 * S), Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hhead, eventually_ge_atTop N, eventually_ge_atTop (1 : ℕ)]
    with M hh hMN hM
  let v := arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M - f
  let b : ℕ → ℝ := fun k => (2 * K) ^ 2 * Real.exp (-a * φ M) *
    halfProfileKernel a φ (k + M)
  have hb : Summable b := ((summable_nat_add_iff M).mpr hsumm).mul_left _
  have henv (k : ℕ) :
      positiveWeight (k + M) * (hilbertSequence v (k + M)) ^ 2 ≤ b k := by
    have hnk : 0 < k + M := by omega
    have hnN : N ≤ k + M := by omega
    have he : Real.exp (-a * φ (k + M)) ≤ Real.exp (-a * φ M) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hmono M (k + M) hM (by omega)) (by linarith)
    have hcoordbound : |hilbertSequence v (k + M)| ≤
        (2 * K) * Real.sqrt ((k + M : ℕ) : ℝ) * Real.exp (-a * φ (k + M)) := by
      change |hilbertSequence
        (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M - f) (k + M)| ≤ _
      rw [hilbertSequence_sub, Pi.sub_apply]
      calc
        _ ≤ |hilbertSequence
            (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) (k + M)| +
            |hilbertSequence f (k + M)| := abs_sub _ _
        _ ≤ K * Real.sqrt ((k + M : ℕ) : ℝ) * Real.exp (-a * φ (k + M)) +
            K * Real.sqrt ((k + M : ℕ) : ℝ) * Real.exp (-a * φ (k + M)) :=
          add_le_add (hN (k + M) hnN M) (hfb (k + M) hnN)
        _ = _ := by ring
    apply (positiveWeight_sq_le_profile hnk hcoordbound).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (sq_nonneg (2 * K)))
      (halfProfileKernel_nonneg a φ (k + M))
  have htail : (∑' k : ℕ, halfProfileKernel a φ (k + M)) ≤ S := by
    have hsplit := hsumm.sum_add_tsum_nat_add M
    have hprefix : 0 ≤ ∑ k ∈ Finset.range M, halfProfileKernel a φ k :=
      Finset.sum_nonneg (fun k _ => halfProfileKernel_nonneg a φ k)
    dsimp [S]
    linarith
  have ht : (∑' k, b k) ≤ (4 * K ^ 2 * S) * Real.exp (-a * φ M) := by
    dsimp [b]
    rw [tsum_mul_left]
    calc
      _ ≤ ((2 * K) ^ 2 * Real.exp (-a * φ M)) * S :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have hs := pareto_norm_sq_le_head_add_tail v M b
    (D * Real.exp (-a * φ M)) ((4 * K ^ 2 * S) * Real.exp (-a * φ M))
    hb hh henv ht
  have hs' : ‖v‖ ^ 2 ≤ (D + 4 * K ^ 2 * S) * Real.exp (-a * φ M) := by
    calc
      _ ≤ _ := hs
      _ = _ := by ring
  have hp : (Real.exp (-(a / 2) * φ M)) ^ 2 = Real.exp (-a * φ M) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt hconstant, hp] using hs'

/-- A positive profile absorbs finitely many exceptional indices into
one constant. The eventual constant need not initially be nonnegative. -/
theorem exists_global_majorant_of_eventual_positive_profile
    (E R : ℕ → ℝ) (hE : ∀ M, 0 ≤ E M) (hR : ∀ M, 0 < R M)
    {C : ℝ} (h : ∀ᶠ M : ℕ in atTop, E M ≤ C * R M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℕ, E M ≤ D * R M := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let S : ℝ := ∑ k ∈ Finset.range N, E k / R k
  have hS : 0 ≤ S :=
    Finset.sum_nonneg (fun k _ => div_nonneg (hE k) (hR k).le)
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  refine ⟨max C 0 + S, by positivity, fun M => ?_⟩
  by_cases hMN : M < N
  · have hsingle : E M / R M ≤ S :=
      Finset.single_le_sum (fun k _ => div_nonneg (hE k) (hR k).le)
        (Finset.mem_range.mpr hMN)
    have hratio : E M / R M ≤ max C 0 + S := hsingle.trans (by linarith)
    exact (div_le_iff₀ (hR M)).mp hratio
  · apply (hN M (by omega)).trans
    apply mul_le_mul_of_nonneg_right _ (hR M).le
    exact (le_max_left C 0).trans (by linarith)

end RiemannResearch.RH.Pareto
