/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTriangular
import RiemannResearch.Analysis.FiniteGramAffineMinimum
import RiemannResearch.RH.ParetoAffineHeadTrials
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Actual complete canonical residual Gram inverse and unique affine optimum

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The finite canonical residual family is proved independent. Its Gram inverse
is consequently constructed without an invertibility or stationarity
provider. Every norm and mixed interaction is the full infinite Pareto norm.
The asymptotic optimized-energy upper bound remains open.
-/

noncomputable section
open Filter
open scoped BigOperators
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.ArithmeticCumulative

/-- The complete finite canonical family is a basis of the actual legal
space, since it spans and has exactly the legal dimension. -/
theorem canonicalMobiusHilbert_finite_linearIndependent (M : ℕ) :
    LinearIndependent ℝ (fun i : Fin M => canonicalMobiusHilbert (i.val + 1)) := by
  have hres : LinearIndependent ℝ (fun i : Fin M => residueAtom i.val) :=
    residueAtom_linearIndependent.comp Fin.val Fin.val_injective
  have hrank := (linearIndependent_iff_card_eq_finrank_span).mp hres
  change Fintype.card (Fin M) = Module.finrank ℝ (finiteSpace M) at hrank
  apply (linearIndependent_iff_card_eq_finrank_span).mpr
  change Fintype.card (Fin M) = Module.finrank ℝ (canonicalMobiusSpan M)
  rw [canonicalMobiusSpan_eq_finiteSpace]
  exact hrank

/-- No finite legal vector equals the constant target: all its legal atoms
vanish at their common factorial multiple. This uses an actual physical
coordinate, not a truncated norm. -/
theorem hilbertOne_not_mem_finiteSpace (M : ℕ) : hilbertOne ∉ finiteSpace M := by
  intro hx
  obtain ⟨c, hc⟩ := finiteSpace_expansion M hilbertOne hx
  have hseq := congrArg (fun x : ThresholdHilbert =>
    hilbertSequenceLinear x (M + 1).factorial) hc
  rw [map_sum] at hseq
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hseq
  have hatom (i : Fin M) :
      hilbertSequence (residueAtom i.val) (M + 1).factorial = 0 := by
    rw [residueAtom, normalizedResidueHilbert_sequence]
    have hdvd : i.val + 2 ∣ (M + 1).factorial :=
      Nat.dvd_factorial (by omega) (by have := i.isLt; omega)
    simp only [residueFraction, Nat.mod_eq_zero_of_dvd hdvd, Nat.cast_zero, zero_div]
  change hilbertSequence hilbertOne (M + 1).factorial =
    ∑ i : Fin M, c i * hilbertSequence (residueAtom i.val) (M + 1).factorial at hseq
  rw [hilbertOne_sequence] at hseq
  simp only [hatom, mul_zero, Finset.sum_const_zero] at hseq
  have hpos := Nat.factorial_pos (M + 1)
  simp [zeroAnchor, ne_of_gt hpos] at hseq

/-- Any positive-cutoff subwindow of the canonical basis stays independent. -/
theorem canonicalMobiusHilbert_window_linearIndependent
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    LinearIndependent ℝ
      (fun i : Fin (M - N + 1) => canonicalMobiusHilbert (N + i.val)) := by
  let e : Fin (M - N + 1) → Fin M :=
    fun i => ⟨N + i.val - 1, by have := i.isLt; omega⟩
  have he : Function.Injective e := by
    intro i j hij
    have hvals := congrArg Fin.val hij
    apply Fin.ext
    dsimp [e] at hvals
    omega
  have hind := (canonicalMobiusHilbert_finite_linearIndependent M).comp e he
  convert hind using 1
  funext i
  dsimp [e]
  congr 1
  omega

private theorem independent_residual_family
    {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
    (v : ι → H) (f : H) (hv : LinearIndependent ℝ v)
    (hf : f ∉ Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ (fun i => f - v i) := by
  apply (linearIndependent_iff_injective_fintypeLinearCombination).mpr
  intro c d hcd
  let a : ι → ℝ := c - d
  have ha : Fintype.linearCombination ℝ (fun i => f - v i) a = 0 := by
    dsimp [a]
    rw [map_sub, hcd, sub_self]
  have he : (∑ i, a i) • f = Fintype.linearCombination ℝ v a := by
    simp only [Fintype.linearCombination_apply, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul] at ha
    exact sub_eq_zero.mp ha
  have hmem : Fintype.linearCombination ℝ v a ∈ Submodule.span ℝ (Set.range v) := by
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  have hsum : (∑ i, a i) = 0 := by
    by_contra hn
    apply hf
    rw [← he] at hmem
    have hi := (Submodule.span ℝ (Set.range v)).smul_mem (∑ i, a i)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hi
  have hzero : Fintype.linearCombination ℝ v a = 0 := by rw [← he, hsum, zero_smul]
  have ha0 : a = 0 := hv.fintypeLinearCombination_injective (by simpa using hzero)
  exact sub_eq_zero.mp ha0

/-- Complete residual family of the actual canonical window. -/
def canonicalWindowResidual (N M : ℕ) (i : Fin (M - N + 1)) : ThresholdHilbert :=
  hilbertOne - canonicalMobiusHilbert (N + i.val)

/-- The residual Gram is strictly positive definite because the residual
vectors themselves are independent. No Gram-inverse provider is assumed. -/
theorem canonicalWindowResidual_linearIndependent
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    LinearIndependent ℝ (canonicalWindowResidual N M) := by
  apply independent_residual_family
    (fun i : Fin (M - N + 1) => canonicalMobiusHilbert (N + i.val)) hilbertOne
    (canonicalMobiusHilbert_window_linearIndependent N M hN hNM)
  intro hx
  apply hilbertOne_not_mem_finiteSpace M
  apply (show Submodule.span ℝ
    (Set.range (fun i : Fin (M - N + 1) => canonicalMobiusHilbert (N + i.val))) ≤
      finiteSpace M from ?_) hx
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
    (by have := i.isLt; omega)
    (canonicalMobiusHilbert_mem_finiteSpace (N + i.val))

/-- Literal inverse-Gram normal solution `R⁻¹ 1` for the actual complete
residual Gram. The inverse exists by the theorem above. -/
def canonicalWindowNormal (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    Fin (M - N + 1) → ℝ :=
  (gramEquiv (canonicalWindowResidual_linearIndependent N M hN hNM)).symm (fun _ => 1)

theorem canonicalWindowNormal_normal (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    gram (canonicalWindowResidual N M) (canonicalWindowNormal N M hN hNM) =
      fun _ => 1 :=
  (gramEquiv (canonicalWindowResidual_linearIndependent N M hN hNM)).apply_symm_apply _

def canonicalWindowMass (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : ℝ :=
  ∑ i, canonicalWindowNormal N M hN hNM i

theorem canonicalWindowMass_pos (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 < canonicalWindowMass N M hN hNM :=
  normal_mass_pos _ _ (canonicalWindowNormal_normal N M hN hNM)

def canonicalWindowOptimum (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    Fin (M - N + 1) → ℝ :=
  affineCoefficients (canonicalWindowNormal N M hN hNM)

theorem canonicalWindowOptimum_sum (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    (∑ i, canonicalWindowOptimum N M hN hNM i) = 1 :=
  affineCoefficients_sum _ _ (canonicalWindowNormal_normal N M hN hNM)

def canonicalWindowTrial (N M : ℕ) (a : Fin (M - N + 1) → ℝ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ
    (fun i : Fin (M - N + 1) => canonicalMobiusHilbert (N + i.val)) a

theorem canonicalWindow_residual_eq_synthesis
    (N M : ℕ) (a : Fin (M - N + 1) → ℝ) (ha : (∑ i, a i) = 1) :
    hilbertOne - canonicalWindowTrial N M a =
      Fintype.linearCombination ℝ (canonicalWindowResidual N M) a := by
  simp only [canonicalWindowResidual, canonicalWindowTrial,
    Fintype.linearCombination_apply, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, ha, one_smul]

/-- Exact complete energy and signed correction for every affine weight
vector. The only scalar is the explicit actual inverse-Gram normal mass. -/
theorem canonicalWindow_residual_completion
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (a : Fin (M - N + 1) → ℝ) (ha : (∑ i, a i) = 1) :
    ‖hilbertOne - canonicalWindowTrial N M a‖ ^ 2 =
      (canonicalWindowMass N M hN hNM)⁻¹ +
        ‖Fintype.linearCombination ℝ (canonicalWindowResidual N M)
          (a - canonicalWindowOptimum N M hN hNM)‖ ^ 2 := by
  rw [canonicalWindow_residual_eq_synthesis N M a ha]
  exact affineCoefficients_completion _ _ _
    (canonicalWindowNormal_normal N M hN hNM) ha

theorem canonicalWindow_optimal_energy
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖hilbertOne - canonicalWindowTrial N M (canonicalWindowOptimum N M hN hNM)‖ ^ 2 =
      (canonicalWindowMass N M hN hNM)⁻¹ := by
  rw [canonicalWindow_residual_eq_synthesis N M _
    (canonicalWindowOptimum_sum N M hN hNM)]
  exact affineCoefficients_energy _ _ (canonicalWindowNormal_normal N M hN hNM)

/-- Uniqueness of actual weights follows from residual independence; it is
stronger than uniqueness of the synthesized minimizing vector. -/
theorem canonicalWindow_optimal_iff
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (a : Fin (M - N + 1) → ℝ) (ha : (∑ i, a i) = 1) :
    ‖hilbertOne - canonicalWindowTrial N M a‖ ^ 2 =
      (canonicalWindowMass N M hN hNM)⁻¹ ↔
        a = canonicalWindowOptimum N M hN hNM := by
  rw [canonicalWindow_residual_eq_synthesis N M a ha]
  constructor
  · intro h
    have he := (affineCoefficients_minimum_iff _ _ _
      (canonicalWindowNormal_normal N M hN hNM) ha).mp h
    exact (canonicalWindowResidual_linearIndependent N M hN hNM).fintypeLinearCombination_injective he
  · intro h
    rw [h]
    exact affineCoefficients_energy _ _ (canonicalWindowNormal_normal N M hN hNM)

/-- Enlarging the conductor budget increases the actual inverse-Gram mass,
equivalently decreasing the optimized complete residual energy. -/
theorem canonicalWindowMass_mono_conductor
    (N M K : ℕ) (hN : 0 < N) (hNM : N ≤ M) (hMK : M ≤ K) :
    canonicalWindowMass N M hN hNM ≤
      canonicalWindowMass N K hN (hNM.trans hMK) := by
  let e : Fin (M - N + 1) → Fin (K - N + 1) :=
    fun i => ⟨i.val, by have := i.isLt; omega⟩
  exact normal_mass_mono_of_family_map
    (canonicalWindowResidual N M) (canonicalWindowResidual N K)
    (canonicalWindowNormal N M hN hNM)
    (canonicalWindowNormal N K hN (hNM.trans hMK))
    (canonicalWindowNormal_normal N M hN hNM)
    (canonicalWindowNormal_normal N K hN (hNM.trans hMK))
    e (fun i => rfl)

/-- Increasing the required head while keeping the same conductor budget
decreases the actual inverse-Gram mass. No RH assumption is used. -/
theorem canonicalWindowMass_antitone_head
    (N L M : ℕ) (hN : 0 < N) (hNL : N ≤ L) (hLM : L ≤ M) :
    canonicalWindowMass L M (hN.trans_le hNL) hLM ≤
      canonicalWindowMass N M hN (hNL.trans hLM) := by
  let e : Fin (M - L + 1) → Fin (M - N + 1) :=
    fun i => ⟨L - N + i.val, by have := i.isLt; omega⟩
  apply normal_mass_mono_of_family_map
    (canonicalWindowResidual L M) (canonicalWindowResidual N M)
    (canonicalWindowNormal L M (hN.trans_le hNL) hLM)
    (canonicalWindowNormal N M hN (hNL.trans hLM))
    (canonicalWindowNormal_normal L M (hN.trans_le hNL) hLM)
    (canonicalWindowNormal_normal N M hN (hNL.trans hLM)) e
  intro i
  simp only [canonicalWindowResidual]
  congr 2
  dsimp [e]
  omega

/-- The explicit inverse-Gram optimizer minimizes over the whole finite
legal exact-head interpolation space, not merely a restricted trial family. -/
theorem canonicalWindow_minimizes_legal_exact_head
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (x : ThresholdHilbert) (hx : x ∈ finiteSpace M)
    (hhead : ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) :
    ‖hilbertOne - canonicalWindowTrial N M (canonicalWindowOptimum N M hN hNM)‖ ^ 2 ≤
      ‖hilbertOne - x‖ ^ 2 := by
  obtain ⟨a, ha, hxa⟩ :=
    exists_canonicalMobius_affine_expansion_of_exact_head N M hNM x hx hhead
  have hxtrial : x = canonicalWindowTrial N M a := hxa
  rw [hxtrial, canonicalWindow_optimal_energy,
    canonicalWindow_residual_completion N M hN hNM a ha]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem canonicalWindowTrial_mem_legalClosure
    (N M : ℕ) (a : Fin (M - N + 1) → ℝ) :
    canonicalWindowTrial N M a ∈ hilbertLegalClosure (Set.Ici 1) := by
  rw [canonicalWindowTrial, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
    (BalancedSquarefree.trialHilbert_mem_legalClosure (N + i.val)))

theorem canonicalWindowTrial_exact_head
    (N M : ℕ) (a : Fin (M - N + 1) → ℝ) (ha : (∑ i, a i) = 1) :
    ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence (canonicalWindowTrial N M a) j = 1 := by
  intro j hj hjN
  change hilbertSequenceLinear
    (∑ i : Fin (M - N + 1), a i • canonicalMobiusHilbert (N + i.val)) j = 1
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i : Fin (M - N + 1), a i *
      hilbertSequence (canonicalMobiusHilbert (N + i.val)) j) = ∑ i, a i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [canonicalMobiusHilbert_exact (N + i.val) j hj (by omega), mul_one]
    _ = 1 := ha

/-- Actual optimized-scalar RH consumer. Every finite algebraic, arithmetic,
legality and head-interpolation premise has been discharged. Only the
explicit cofinal subpolynomial bound on the inverse normal mass remains. -/
theorem riemannHypothesis_of_canonicalWindowMass_subpolynomial
    (N M : ℕ → ℕ) (hN : ∀ p, 0 < N p) (hNM : ∀ p, N p ≤ M p)
    (hcofinal : Tendsto (fun p => ((N p + 1 : ℕ) : ℝ)) atTop atTop)
    (hsub : Tendsto (fun p =>
      Real.log (1 + (canonicalWindowMass (N p) (M p) (hN p) (hNM p))⁻¹) /
        Real.log ((N p + 1 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_legal_exact_head_subpolynomial (Set.Ici 1)
    (fun d hd => lt_of_lt_of_le Nat.zero_lt_one hd)
    (fun p => canonicalWindowTrial (N p) (M p)
      (canonicalWindowOptimum (N p) (M p) (hN p) (hNM p)))
    (fun p => N p + 1)
    (fun p => (canonicalWindowMass (N p) (M p) (hN p) (hNM p))⁻¹) hcofinal
  · intro p
    exact canonicalWindowTrial_mem_legalClosure _ _ _
  · intro p j hj hjN
    exact canonicalWindowTrial_exact_head _ _ _
      (canonicalWindowOptimum_sum _ _ _ _) j hj (by omega)
  · intro p
    exact inv_nonneg.mpr (canonicalWindowMass_pos _ _ _ _).le
  · intro p
    rw [canonicalWindow_optimal_energy]
    exact le_add_of_nonneg_right zero_le_one
  · exact hsub

end RiemannResearch.RH.Pareto.CoefficientStabilization
