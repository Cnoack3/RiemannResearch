/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeSchurOperator
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreePrimeProductCriterion
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.NormNum
/-!
# CRT regularity and bounded approximants for the displacement

The compact space is the actual product of the finite prime residue rings.
A continuous extension of the physical displacement implies boundedness.
Conversely a zero residual gives the zero extension. Thus existence of the
extension is an Open arithmetic condition, not a consequence of compactness.

Source for compact products and finite-coordinate uniform approximation:
T. Tao, An Epsilon of Room, I (AMS, 2010), Theorem 1.10.18 and
Exercise 1.10.28, https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf.
Only compactness and boundedness of continuous functions are used in the Lean
extension proof. No Stone-Weierstrass density assertion about the legal
linear span is made. The pointwise bounded-limit argument is standard.

The centered resolvent converges in Q norm unconditionally. Its uniform
physical bound remains Open and is kept as an explicit hypothesis.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeCRTRegularity
open ZetaTwoHilbert ZetaTwoOptimizerStage
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementResolvent
open QSquarefreePrimeProductCriterion QSquarefreeSchurOperator
open QSquarefreeFiniteDisplacement
abbrev PrimeResidueSpace := (p : Nat.Primes) → ZMod p.val
instance : CompactSpace PrimeResidueSpace := by
  letI (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩
  infer_instance
def physicalPoint (n : ℕ) : PrimeResidueSpace := fun _ => n
def HasContinuousCRTExtension (f : QHilbert) : Prop :=
  ∃ F : C(PrimeResidueSpace, ℝ), ∀ n : ℕ, 1 ≤ n →
    F (physicalPoint n) = qSequence f n
theorem physically_bounded_of_crt_extension {f : QHilbert}
    (h : HasContinuousCRTExtension f) :
    ∃ C : ℝ, ∀ n, |qSequence f n| ≤ C := by
  obtain ⟨F, hF⟩ := h
  refine ⟨‖F‖, ?_⟩
  intro n
  cases n with
  | zero => simpa only [qSequence_zero, abs_zero] using norm_nonneg F
  | succ n =>
      rw [← hF (n+1) (Nat.succ_le_succ (Nat.zero_le n)), ← Real.norm_eq_abs]
      exact F.norm_coe_le_norm _
theorem residual_zero_iff_crt_extension :
    limitingResidual = 0 ↔ HasContinuousCRTExtension displacement := by
  constructor
  · intro hr
    have hd := displacement_eq_zero_of_residual_eq_zero hr
    refine ⟨0, ?_⟩
    intro n hn
    rw [hd]
    simp only [ContinuousMap.zero_apply, ← qEvalCLM_apply, map_zero]
  · intro h
    obtain ⟨C, hC⟩ := physically_bounded_of_crt_extension h
    exact residual_eq_zero_of_displacement_physically_bounded C hC
theorem prime_products_of_crt_extension
    (h : HasContinuousCRTExtension displacement) : DisplacementPrimeProductsLegal :=
  residual_zero_iff_displacement_prime_products.mp (residual_zero_iff_crt_extension.mpr h)
theorem riemannHypothesis_of_crt_extension
    (h : HasContinuousCRTExtension displacement) : RiemannHypothesis :=
  riemannHypothesis_of_displacement_prime_products (prime_products_of_crt_extension h)
theorem prime_products_of_schur_crt_extension
    (h : HasContinuousCRTExtension (schurOperator limitingResidual)) :
    DisplacementPrimeProductsLegal := by
  obtain ⟨C, hC⟩ := physically_bounded_of_crt_extension h
  exact prime_products_of_schur_physically_bounded C hC
theorem residual_zero_of_bounded_pointwise_approximants
    (u : ℕ → ℕ → ℝ) (C : ℝ)
    (hb : ∀ j n, |u j n| ≤ C)
    (hc : ∀ n, Tendsto (fun j => u j n) atTop (𝓝 (qSequence displacement n))) :
    limitingResidual = 0 := by
  apply residual_eq_zero_of_displacement_physically_bounded C
  intro n
  exact le_of_tendsto (hc n).abs (Filter.Eventually.of_forall (fun j => hb j n))
theorem residual_zero_of_bounded_hilbert_approximants
    (u : ℕ → QHilbert) (C : ℝ)
    (hb : ∀ j n, |qSequence (u j) n| ≤ C)
    (hc : Tendsto u atTop (𝓝 displacement)) : limitingResidual = 0 :=
  residual_zero_of_bounded_pointwise_approximants (fun j n => qSequence (u j) n)
    C hb (qSequence_tendsto_of_tendsto hc)
theorem centered_resolvent_tendsto :
    Tendsto resolventApprox atTop (𝓝 displacement) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hpow : Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n * ‖displacement‖)
      atTop (𝓝 0) := by simpa using hpow.mul_const ‖displacement‖
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  rw [norm_sub_rev]
  exact resolvent_error_norm_le n
theorem prime_products_of_bounded_centered_resolvent
    (C : ℝ) (hb : ∀ j n, |qSequence (resolventApprox j) n| ≤ C) :
    DisplacementPrimeProductsLegal :=
  residual_zero_iff_displacement_prime_products.mp
    (residual_zero_of_bounded_hilbert_approximants resolventApprox C hb
      centered_resolvent_tendsto)
theorem residual_zero_of_cofinal_head_bounds (u : ℕ → QHilbert)
    (hc : Tendsto u atTop (𝓝 displacement)) (H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (C : ℝ)
    (hb : ∀ j n, n ≤ H j → |qSequence (u j) n| ≤ C) :
    limitingResidual = 0 := by
  apply residual_eq_zero_of_displacement_physically_bounded C
  intro n
  apply le_of_tendsto (qSequence_tendsto_of_tendsto hc n).abs
  filter_upwards [(tendsto_atTop.1 hH) n] with j hj
  exact hb j n hj
theorem prime_products_of_cofinal_finite_heads (J H : ℕ → ℕ)
    (hJ : Tendsto J atTop atTop) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hb : ∀ j n, n ≤ H j →
      |qSequence (finiteDisplacement (J j)) n| ≤ C) :
    DisplacementPrimeProductsLegal := by
  apply residual_zero_iff_displacement_prime_products.mp
  exact residual_zero_of_cofinal_head_bounds
    (fun j => finiteDisplacement (J j)) (finiteDisplacement_tendsto.comp hJ) H hH C hb
theorem riemannHypothesis_of_cofinal_finite_heads (J H : ℕ → ℕ)
    (hJ : Tendsto J atTop atTop) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hb : ∀ j n, n ≤ H j →
      |qSequence (finiteDisplacement (J j)) n| ≤ C) : RiemannHypothesis :=
  riemannHypothesis_of_displacement_prime_products
    (prime_products_of_cofinal_finite_heads J H hJ hH C hb)
end RiemannResearch.RH.QSquarefreeCRTRegularity
