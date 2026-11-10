/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueCriticalNormalLimit
import RiemannResearch.RH.ParetoResidueAtomTests
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.Analysis.AffineObservationProjection
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Zero certificates for the full running LCM dictionary

The scale `log L = psi M` is exact and the repository prime number theorem
also gives `psi M ~ M`. The actual Pareto projection onto divisor atoms
has the compulsory multiples error, the zero-certificate energy, and its
remaining square. The vanishing of this remaining square is a conditional
research reduction to the full Pareto approximation problem.

The classical comparison uses Báez-Duarte, *A strengthening of the
Nyman–Beurling criterion for the Riemann Hypothesis*, Theorem 1.1,
https://arxiv.org/abs/math/0202141, for the natural approximation
property. The Lean transfer uses the existing checked index-one correction.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_ne_one)
open ParetoBeurlingMellinObstruction
open RiemannResearch.Analysis.SingleObservationProjection (affine_target_error_split)

variable {ι : Type*} [Fintype ι]

/-- The fixed-family certificate law on any cofinal running LCM tower, with
the exact summatory von Mangoldt scale. -/
theorem lcm_critical_certificate_psi_tendsto (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (γ : ι → ℝ) (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (fun j => Chebyshev.psi (M j : ℝ) *
      certificateEnergy (lcmResidueIndex (M j)) (fun i => criticalPoint (γ i))) atTop
      (𝓝 (2 * ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2)) := by
  simpa only [Function.comp_def, lcm_log_eq_psi] using
    (critical_certificate_log_tendsto γ hγ hpos hz).comp (lcmResidueIndex_tendsto.comp hM)

/-- The proved prime number theorem also gives the same limit with the
ordinary integer cutoff as scale. -/
theorem lcm_critical_certificate_cutoff_tendsto (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (γ : ι → ℝ) (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (fun j => (M j : ℝ) *
      certificateEnergy (lcmResidueIndex (M j)) (fun i => criticalPoint (γ i))) atTop
      (𝓝 (2 * ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2)) := by
  have hsets (m : ℕ) : Finset.Icc 0 m = Finset.Iic m := by
    ext k
    simp
  have hP : Tendsto (fun m : ℕ => Chebyshev.psi (m : ℝ) / m) atTop (𝓝 1) := by
    simpa only [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, hsets] using
      RiemannResearch.NumberTheory.PrimeNumberTheorem.WeakPNT'
  have hinv : Tendsto (fun j => (M j : ℝ) / Chebyshev.psi (M j : ℝ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, inv_div, inv_one] using
      (hP.comp hM).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hh := hinv.mul (lcm_critical_certificate_psi_tendsto M hM γ hγ hpos hz)
  rw [one_mul] at hh
  refine hh.congr' ?_
  filter_upwards [hM.eventually (eventually_ge_atTop (2 : ℕ))] with j hj
  have hjR : (2 : ℝ) ≤ (M j : ℝ) := by exact_mod_cast hj
  have hpsi : Chebyshev.psi (M j : ℝ) ≠ 0 :=
    (Chebyshev.psi_eq_zero_iff.not.mpr (not_lt.mpr hjR))
  change (M j : ℝ) / Chebyshev.psi (M j : ℝ) *
    (Chebyshev.psi (M j : ℝ) *
      certificateEnergy (lcmResidueIndex (M j)) (fun i => criticalPoint (γ i))) = _
  field_simp

/-- The same positive lower floor applies uniformly to every legal LCM trial. -/
theorem lcm_critical_certificate_legal_error_floor
    (γ : ι → ℝ) (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ f ∈ trialSpace (Nat.lcmUpto M),
      2 * (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) - ε ≤
        Chebyshev.psi (M : ℝ) * ‖hilbertOne - f‖ ^ 2 := by
  have h := lcmResidueIndex_tendsto.eventually
    (critical_certificate_legal_error_floor γ hγ hpos hz ε hε)
  filter_upwards [h] with M hM
  simpa only [lcmResidueIndex_succ, lcm_log_eq_psi] using hM

omit [Fintype ι] in
private theorem trialSpace_le_full (L : ℕ) : trialSpace L ≤ normalizedResidueSpan := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  have hd := Nat.pos_of_mem_divisors d.property
  by_cases hd1 : d.val = 1
  · have hzero : normalizedResidueHilbert d.val hd = 0 := by
      apply hilbertSequence_injective
      funext n
      rw [normalizedResidueHilbert_sequence]
      change ArithmeticCumulative.residueFraction d.val n =
        hilbertSequenceLinear (0 : ThresholdHilbert) n
      rw [map_zero]
      simp [ArithmeticCumulative.residueFraction, hd1, Nat.mod_one]
    change normalizedResidueHilbert d.val hd ∈ normalizedResidueSpan
    rw [hzero]
    exact normalizedResidueSpan.zero_mem
  · exact Submodule.subset_span ⟨⟨d.val, by omega⟩, rfl⟩

omit [Fintype ι] in
private theorem full_trial_eventually {f : ThresholdHilbert} (hf : f ∈ normalizedResidueSpan) :
    ∀ᶠ M : ℕ in atTop, f ∈ trialSpace (Nat.lcmUpto M) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, rfl⟩
    filter_upwards [eventually_ge_atTop d.val] with M hM
    have hd : 0 < d.val := by have := d.property; omega
    exact atom_mem_trial _ _ (Nat.lcmUpto_pos M) hd
      (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hd, hM⟩))
  | zero => exact Eventually.of_forall (fun _ => Submodule.zero_mem _)
  | add f g hf hg ihf ihg =>
    filter_upwards [ihf, ihg] with M hM hM'
    exact Submodule.add_mem _ hM hM'
  | smul c f hf ih =>
    filter_upwards [ih] with M hM
    exact Submodule.smul_mem _ c hM

instance (L : ℕ) : FiniteDimensional ℝ (trialSpace L) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The actual optimum over all divisor conductors in the physical Pareto norm. -/
def lcmBest (M : ℕ) : ThresholdHilbert :=
  (trialSpace (Nat.lcmUpto M)).starProjection hilbertOne

theorem lcmBest_mem (M : ℕ) : lcmBest M ∈ trialSpace (Nat.lcmUpto M) :=
  (trialSpace (Nat.lcmUpto M)).starProjection_apply_mem _

open BaezDuarte (finiteResidueSum residueVector centeredError_eq_hilbert_norm_sq
  centeredError_le_two_naturalError naturalError correctedCoefficient corrected_naturalError_eq
  NaturalApproximation naturalApproximation_iff_one_mem)

omit [Fintype ι] in
/-- The complete classical trial error controls the actual LCM optimum.
Every trial supported on `1, …, M` qualifies, since its indices divide the running LCM. -/
theorem lcm_best_error_le_two_naturalError (M : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (hdiv : ∀ d ∈ s, d ∣ Nat.lcmUpto M) :
    ENNReal.ofReal (‖hilbertOne - lcmBest M‖ ^ 2) ≤ 2 * naturalError s a := by
  have hf : finiteResidueSum s a ∈ trialSpace (Nat.lcmUpto M) := by
    apply Submodule.sum_mem
    intro d hd
    rw [residueVector, dif_pos (hs d hd)]
    exact Submodule.smul_mem _ _ (atom_mem_trial _ d (Nat.lcmUpto_pos M) (hs d hd) (hdiv d hd))
  have he := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne
    (finiteResidueSum s a) hf
  change ‖hilbertOne - finiteResidueSum s a‖ ^ 2 =
    ‖hilbertOne - lcmBest M‖ ^ 2 + ‖finiteResidueSum s a - lcmBest M‖ ^ 2 at he
  have hle : ‖hilbertOne - lcmBest M‖ ^ 2 ≤ ‖hilbertOne - finiteResidueSum s a‖ ^ 2 := by
    linarith [sq_nonneg ‖finiteResidueSum s a - lcmBest M‖]
  calc
    _ ≤ ENNReal.ofReal (‖hilbertOne - finiteResidueSum s a‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hle
    _ = BaezDuarte.centeredError s a := (centeredError_eq_hilbert_norm_sq s a hs).symm
    _ ≤ _ := centeredError_le_two_naturalError s a hs

omit [Fintype ι] in
/-- The exact optimum is also the error of a classical trial using only
divisor conductors, after the index-one charge correction. -/
theorem lcm_best_error_as_naturalError (M : ℕ) :
    ∃ s : Finset ℕ, ∃ a : ℕ → ℝ, (∀ d ∈ s, 0 < d ∧ d ∣ Nat.lcmUpto M) ∧
      naturalError s a = ENNReal.ofReal (‖hilbertOne - lcmBest M‖ ^ 2) := by
  classical
  let L := Nat.lcmUpto M
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (lcmBest_mem M)
  let s := c.support.map (Function.Embedding.subtype fun d : ℕ => d ∈ L.divisors)
  let a (d : ℕ) : ℝ := if hd : d ∈ L.divisors then c ⟨d, hd⟩ else 0
  have hmem (d : ℕ) (hd : d ∈ s) : d ∈ L.divisors := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hd
    exact i.property
  have hs (d : ℕ) (hd : d ∈ s) : 0 < d := Nat.pos_of_mem_divisors (hmem d hd)
  have he : finiteResidueSum s a = lcmBest M := by
    rw [← hc]
    unfold finiteResidueSum s Finsupp.sum
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro d _
    change a d.val • residueVector d.val =
      c d • normalizedResidueHilbert d.val (Nat.pos_of_mem_divisors d.property)
    dsimp only [a]
    rw [dif_pos d.property, residueVector, dif_pos (Nat.pos_of_mem_divisors d.property)]
  refine ⟨insert 1 s, correctedCoefficient s a, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · exact ⟨hs d hd, Nat.dvd_of_mem_divisors (hmem d hd)⟩
  · rw [corrected_naturalError_eq s a hs, centeredError_eq_hilbert_norm_sq s a hs, he]

/-- The remaining square for the actual best legal trial. -/
def lcmRemainder (z : ι → ℂ) (M : ℕ) : ℝ :=
  ‖errorVector (lcmResidueIndex M) (lcmBest M) - certificateVector (lcmResidueIndex M) z‖ ^ 2

/-- The complete error keeps the zero-certificate square and the independent
displacement from the actual best legal vector. -/
theorem lcm_error_four_terms (M : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (Nat.lcmUpto M)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    ‖hilbertOne - f‖ ^ 2 =
      classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
      certificateEnergy (lcmResidueIndex M) z + lcmRemainder z M + ‖f - lcmBest M‖ ^ 2 := by
  have hb : lcmBest M ∈ trialSpace (lcmResidueIndex M + 1) := by
    rw [lcmResidueIndex_succ]
    exact lcmBest_mem M
  have hsplit := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne f hf
  change ‖hilbertOne - f‖ ^ 2 = ‖hilbertOne - lcmBest M‖ ^ 2 + ‖f - lcmBest M‖ ^ 2 at hsplit
  rw [legal_error_completion_canonical hb z hs hs1 hz] at hsplit
  exact hsplit

omit [Fintype ι] in
theorem lcm_best_error_tendsto_zero_iff :
    Tendsto (fun M => ‖hilbertOne - lcmBest M‖ ^ 2) atTop (𝓝 0) ↔
      hilbertOne ∈ normalizedResidueClosure := by
  constructor
  · intro h
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨M, hM⟩ := (h.eventually (gt_mem_nhds (sq_pos_of_pos hε))).exists
    refine ⟨lcmBest M, trialSpace_le_full _ (lcmBest_mem M), ?_⟩
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hM
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall (fun M => ha.trans_le (sq_nonneg _))
    · intro b hb
      obtain ⟨f, hf, he⟩ := Metric.mem_closure_iff.mp h (Real.sqrt b) (Real.sqrt_pos.mpr hb)
      have he' : ‖hilbertOne - f‖ ^ 2 < b := by
        rw [dist_eq_norm] at he
        simpa only [Real.sq_sqrt hb.le] using
          (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg b)).mpr he
      filter_upwards [full_trial_eventually hf] with M hM
      have hp := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne f hM
      change ‖hilbertOne - f‖ ^ 2 = ‖hilbertOne - lcmBest M‖ ^ 2 + ‖f - lcmBest M‖ ^ 2 at hp
      linarith [sq_nonneg ‖f - lcmBest M‖]

omit [Fintype ι] in
theorem multiples_mass_tendsto_zero :
    Tendsto (fun N => classWeight N (Fin.last N)) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hzero := tendsto_inv_atTop_zero.comp hN
  apply squeeze_zero (fun N => (classWeight_pos N (Fin.last N)).le) ?_
    (show Tendsto (fun N : ℕ => 2 * ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) by
      simpa using hzero.const_mul (2 : ℝ))
  intro N
  apply (multiples_mass_bounds N).2.trans
  simp only [Nat.cast_add, Nat.cast_one, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The finite optimum with its exact remaining square and both certificate terms. -/
theorem lcm_best_error_eq (M : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    ‖hilbertOne - lcmBest M‖ ^ 2 =
      classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
      certificateEnergy (lcmResidueIndex M) z + lcmRemainder z M := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
    lcm_error_four_terms M (lcmBest_mem M) z hs hs1 hz

private theorem lcm_certificate_terms_tendsto_zero (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (fun M => classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
      certificateEnergy (lcmResidueIndex M) (fun i => criticalPoint (γ i))) atTop (𝓝 0) := by
  have hmass := multiples_mass_tendsto_zero.comp lcmResidueIndex_tendsto
  simpa only [zero_add, Function.comp_def] using hmass.add
    ((critical_certificate_tendsto_zero γ hγ hpos hz).comp lcmResidueIndex_tendsto)

/-- An actual right-half-strip zero forces a positive floor in the optimized
remainder after the fixed critical tests have been accounted for. -/
theorem lcm_remainder_eventually_ge_of_right_zero (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    ∀ᶠ M : ℕ in atTop,
      ((2 * s.re - 1) / ‖s‖ ^ 2) / 2 ≤ lcmRemainder (fun i => criticalPoint (γ i)) M := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < (2 * s.re - 1) / ‖s‖ ^ 2 / 2 :=
    div_pos (div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hs0))) (by norm_num)
  filter_upwards [(lcm_certificate_terms_tendsto_zero γ hγ hpos hz).eventually
    (gt_mem_nhds hc)] with M hM
  have hmem : lcmBest M ∈ normalizedResidueClosure :=
    subset_closure (trialSpace_le_full _ (lcmBest_mem M))
  have hlow := normalizedResidue_error_sq_lower_bound_of_zeta_zero s hs hs1 hzero (lcmBest M) hmem
  rw [lcm_best_error_eq M (fun i => criticalPoint (γ i)) (fun i => by simp)
    (fun i => criticalPoint_ne_one (γ i)) hz] at hlow
  linarith

/-- For fixed critical tests the remaining square contains precisely the open
vanishing condition for the actual full legal closure. -/
theorem lcm_remainder_tendsto_zero_iff (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (lcmRemainder (fun i => criticalPoint (γ i))) atTop (𝓝 0) ↔
      hilbertOne ∈ normalizedResidueClosure := by
  let z := fun i => criticalPoint (γ i)
  have he (M : ℕ) : ‖hilbertOne - lcmBest M‖ ^ 2 =
      classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
      certificateEnergy (lcmResidueIndex M) z + lcmRemainder z M := by
    exact lcm_best_error_eq M z (fun i => by simp [z])
      (fun i => criticalPoint_ne_one (γ i)) hz
  have hzero := lcm_certificate_terms_tendsto_zero γ hγ hpos hz
  rw [← lcm_best_error_tendsto_zero_iff]
  constructor
  · intro h
    have hh := hzero.add h
    rw [zero_add] at hh
    exact hh.congr (fun M => (he M).symm)
  · intro h
    have hh := h.sub hzero
    rw [sub_zero] at hh
    refine hh.congr (fun M => ?_)
    change ‖hilbertOne - lcmBest M‖ ^ 2 -
      (classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
        certificateEnergy (lcmResidueIndex M) z) = lcmRemainder z M
    rw [he M]
    ring

/-- The remaining square vanishes exactly under the natural-dilation
approximation property from Báez-Duarte's Theorem 1.1. -/
theorem lcm_remainder_tendsto_zero_iff_naturalApproximation (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (lcmRemainder (fun i => criticalPoint (γ i))) atTop (𝓝 0) ↔
      NaturalApproximation := by
  have hAtoms : normalizedResidueAtoms = Set.range CoefficientStabilization.residueAtom := by
    ext f
    constructor
    · rintro ⟨⟨d, hd⟩, rfl⟩
      refine ⟨d - 2, ?_⟩
      simp only [CoefficientStabilization.residueAtom, Nat.sub_add_cancel hd]
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i + 2, by omega⟩, rfl⟩
  have hClosure :
      normalizedResidueClosure = (CoefficientStabilization.closedSpace : Set ThresholdHilbert) := by
    change closure (Submodule.span ℝ normalizedResidueAtoms : Set ThresholdHilbert) =
      closure (Submodule.span ℝ (Set.range CoefficientStabilization.residueAtom) : Set ThresholdHilbert)
    rw [hAtoms]
  rw [lcm_remainder_tendsto_zero_iff γ hγ hpos hz, hClosure]
  exact naturalApproximation_iff_one_mem.symm

/-- A vanishing optimized remainder suffices for Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_lcm_remainder (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (hrem : Tendsto (lcmRemainder (fun i => criticalPoint (γ i))) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hmem := (lcm_remainder_tendsto_zero_iff γ hγ hpos hz).mp hrem
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  exact zeta_ne_zero_of_hilbertOne_mem_normalizedResidueClosure hmem s hs hs1

section RemainderAsymptotics

/-- The optimized complete physical squared error at a running LCM cutoff. -/
def lcmError (M : ℕ) : ℝ := ‖hilbertOne - lcmBest M‖ ^ 2

theorem lcmError_le_one (M : ℕ) : lcmError M ≤ 1 := by
  have h := affine_target_error_split (trialSpace (Nat.lcmUpto M)) hilbertOne
    0 ((trialSpace (Nat.lcmUpto M)).zero_mem)
  change ‖hilbertOne - 0‖ ^ 2 = lcmError M + ‖0 - lcmBest M‖ ^ 2 at h
  rw [sub_zero, hilbertOne_norm_sq] at h
  linarith [sq_nonneg ‖(0 : ThresholdHilbert) - lcmBest M‖]

theorem lcm_trial_mono : Monotone (fun M => trialSpace (Nat.lcmUpto M)) := by
  intro M K hMK
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  have hLK : Nat.lcmUpto M ∣ Nat.lcmUpto K :=
    Finset.lcm_dvd (fun k hk =>
      Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hMK⟩))
  exact atom_mem_trial _ d.val (Nat.lcmUpto_pos K) (Nat.pos_of_mem_divisors d.property)
    ((Nat.dvd_of_mem_divisors d.property).trans hLK)

theorem lcm_trial_iSup_eq : (⨆ M, trialSpace (Nat.lcmUpto M)) = normalizedResidueSpan := by
  apply le_antisymm
  · exact iSup_le (fun M => trialSpace_le_full (Nat.lcmUpto M))
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply (le_iSup (fun M => trialSpace (Nat.lcmUpto M)) d.val)
    have hd : 0 < d.val := by have := d.property; omega
    exact atom_mem_trial _ d.val (Nat.lcmUpto_pos d.val) hd
      (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hd, le_rfl⟩))

/-- All divisor stages converge to the projection on the full legal closure. -/
theorem lcmBest_tendsto :
    Tendsto lcmBest atTop
      (𝓝 (normalizedResidueSpan.topologicalClosure.starProjection hilbertOne)) := by
  change Tendsto (fun M => (trialSpace (Nat.lcmUpto M)).starProjection hilbertOne) atTop _
  simpa only [lcm_trial_iSup_eq] using
    Submodule.starProjection_tendsto_closure_iSup
      (fun M => trialSpace (Nat.lcmUpto M)) lcm_trial_mono hilbertOne

theorem lcmError_tendsto :
    Tendsto lcmError atTop
      (𝓝 (‖hilbertOne -
        normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2)) :=
  (tendsto_const_nhds.sub lcmBest_tendsto).norm.pow 2

variable {κ : Type*} [Fintype κ]

theorem lcmRemainder_le_error (M : ℕ) (z : κ → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    lcmRemainder z M ≤ lcmError M := by
  have h := lcm_best_error_eq M z hs hs1 hz
  unfold lcmError
  linarith [classWeight_pos (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)),
    certificateEnergy_nonneg (lcmResidueIndex M) z]

/-- Fixed critical tests remove a vanishing amount from the actual projection error. -/
theorem lcmRemainder_tendsto_limit (γ : κ → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (lcmRemainder (fun i => criticalPoint (γ i))) atTop
      (𝓝 (‖hilbertOne -
        normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2)) := by
  have h := lcmError_tendsto.sub (lcm_certificate_terms_tendsto_zero γ hγ hpos hz)
  rw [sub_zero] at h
  refine h.congr (fun M => ?_)
  unfold lcmError
  rw [lcm_best_error_eq M (fun i => criticalPoint (γ i)) (fun i => by simp)
    (fun i => criticalPoint_ne_one (γ i)) hz]
  ring

private theorem lcm_psi_mul_multiples_mass_tendsto :
    Tendsto (fun M : ℕ => Chebyshev.psi (M : ℝ) *
      classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M))) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hlim := (tendsto_inv_atTop_zero.comp (hN.comp lcmResidueIndex_tendsto)).const_mul (2 : ℝ)
  rw [mul_zero] at hlim
  apply squeeze_zero (fun M => mul_nonneg (Chebyshev.psi_nonneg _) (classWeight_pos _ _).le) ?_ hlim
  intro M
  rw [← lcm_log_eq_psi]
  let L := (lcmResidueIndex M : ℝ) + 1
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Nat.cast_nonneg (α := ℝ) (lcmResidueIndex M)]
  have hp : 0 < L := zero_lt_one.trans_le hL
  have hw := (multiples_mass_bounds (lcmResidueIndex M)).2
  simp only [Nat.cast_add, Nat.cast_one] at hw
  change classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) ≤ 2 / (L * (L + 1)) at hw
  change Real.log L * classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) ≤ 2 * L⁻¹
  calc
    _ ≤ Real.log L * (2 / (L * (L + 1))) :=
      mul_le_mul_of_nonneg_left hw (Real.log_nonneg hL)
    _ ≤ (L + 1) * (2 / (L * (L + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.log_le_sub_one_of_pos hp]) (by positivity)
    _ = _ := by field_simp [hp.ne']

/-- The moving certificate is the entire first-order correction, apart from
the compulsory multiples mass. No uniform size or spacing premise is needed for this transfer. -/
theorem lcmError_sub_moving_remainder_psi_tendsto (κ : ℕ → Type*) [∀ j, Fintype (κ j)]
    (z : ∀ j, κ j → ℂ) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hs : ∀ j i, 0 < (z j i).re) (hs1 : ∀ j i, z j i ≠ 1)
    (hz : ∀ j i, riemannZeta (z j i) = 0) :
    Tendsto (fun j => Chebyshev.psi (M j : ℝ) *
      (lcmError (M j) - lcmRemainder (z j) (M j)) -
        Chebyshev.psi (M j : ℝ) * certificateEnergy (lcmResidueIndex (M j)) (z j))
      atTop (𝓝 0) := by
  refine (lcm_psi_mul_multiples_mass_tendsto.comp hM).congr (fun j => ?_)
  have he := lcm_best_error_eq (M j) (z j) (hs j) (hs1 j) (hz j)
  change lcmError (M j) = _ at he
  dsimp only [Function.comp_def]
  rw [he]
  ring

/-- Vanishing moving certificate energy leaves the full optimized projection limit. -/
theorem lcm_moving_remainder_tendsto_limit (κ : ℕ → Type*) [∀ j, Fintype (κ j)]
    (z : ∀ j, κ j → ℂ) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hs : ∀ j i, 0 < (z j i).re) (hs1 : ∀ j i, z j i ≠ 1)
    (hz : ∀ j i, riemannZeta (z j i) = 0)
    (hC : Tendsto (fun j => certificateEnergy (lcmResidueIndex (M j)) (z j)) atTop (𝓝 0)) :
    Tendsto (fun j => lcmRemainder (z j) (M j)) atTop
      (𝓝 (‖hilbertOne -
        normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2)) := by
  have hm := multiples_mass_tendsto_zero.comp (lcmResidueIndex_tendsto.comp hM)
  have h := ((lcmError_tendsto.comp hM).sub hm).sub hC
  simp only [sub_zero] at h
  refine h.congr (fun j => ?_)
  have he := lcm_best_error_eq (M j) (z j) (hs j) (hs1 j) (hz j)
  change lcmError (M j) = _ at he
  dsimp only [Function.comp_def]
  rw [he]
  ring

private theorem cutoff_mul_multiples_mass_tendsto :
    Tendsto (fun M : ℕ => (M : ℝ) * classWeight (lcmResidueIndex M)
      (Fin.last (lcmResidueIndex M))) atTop (𝓝 0) := by
  have hM : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun M => by linarith) tendsto_natCast_atTop_atTop
  have hlim := (tendsto_inv_atTop_zero.comp hM).const_mul (2 : ℝ)
  rw [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun M =>
    mul_nonneg (Nat.cast_nonneg _) (classWeight_pos _ _).le)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hL := Nat.lcmUpto_pos M
  have hd : M ∣ Nat.lcmUpto M :=
    Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hM, le_rfl⟩)
  have hle : (M : ℝ) ≤ (Nat.lcmUpto M : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hL hd
  have hpos : 0 < (Nat.lcmUpto M : ℝ) := by exact_mod_cast hL
  have hu := (multiples_mass_bounds (lcmResidueIndex M)).2
  rw [lcmResidueIndex_succ] at hu
  calc
    _ ≤ (M : ℝ) * (2 / ((Nat.lcmUpto M : ℝ) * ((Nat.lcmUpto M : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _)
    _ ≤ (Nat.lcmUpto M : ℝ) *
        (2 / ((Nat.lcmUpto M : ℝ) * ((Nat.lcmUpto M : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 2 / ((Nat.lcmUpto M : ℝ) + 1) := by field_simp
    _ ≤ 2 * ((M : ℝ) + 1)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- The certificate is exactly the first-order correction to the remainder.
This applies even if the limiting squared error is positive. -/
theorem lcmError_sub_remainder_cutoff_tendsto (γ : κ → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (fun M : ℕ => (M : ℝ) * (lcmError M -
      lcmRemainder (fun i => criticalPoint (γ i)) M)) atTop
      (𝓝 (2 * ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2)) := by
  have h := cutoff_mul_multiples_mass_tendsto.add
    (lcm_critical_certificate_cutoff_tendsto id tendsto_id γ hγ hpos hz)
  rw [zero_add] at h
  refine h.congr (fun M => ?_)
  dsimp only [id, lcmError]
  rw [lcm_best_error_eq M (fun i => criticalPoint (γ i)) (fun i => by simp)
    (fun i => criticalPoint_ne_one (γ i)) hz]
  ring

/-- Any cofinal family of upper budgets tending to zero yields RH. -/
theorem riemannHypothesis_of_cofinal_remainder_upper (γ : κ → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (B : ℕ → ℝ)
    (hB : Tendsto B atTop (𝓝 0))
    (hub : ∀ᶠ j in atTop, lcmRemainder (fun i => criticalPoint (γ i)) (M j) ≤ B j) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt hzero
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hp : 0 < ((2 * s.re - 1) / ‖s‖ ^ 2) / 2 :=
    div_pos (div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hs0))) (by norm_num)
  obtain ⟨j, hlow, hup, hsmall⟩ :=
    ((hM.eventually (lcm_remainder_eventually_ge_of_right_zero γ hγ hpos hz s hs hs1 hzero)).and
      (hub.and (hB.eventually (gt_mem_nhds hp)))).exists
  exact (not_lt_of_ge (hlow.trans hup)) hsmall

/-- A single finite upper certificate gives an effective zero-free region. -/
theorem right_zero_re_le_of_lcmError_bound (M : ℕ) (B T : ℝ)
    (hB : lcmError M ≤ B) (hT : 0 ≤ T) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs' : s.re < 1)
    (ht : |s.im| ≤ T) (hz : riemannZeta s = 0) :
    s.re ≤ 1 / 2 + (1 + T ^ 2) * B / 2 := by
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hs'
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hp : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs0)
  have hm : lcmBest M ∈ normalizedResidueClosure :=
    subset_closure (trialSpace_le_full _ (lcmBest_mem M))
  have hlow := (div_le_iff₀ hp).mp
    ((normalizedResidue_error_sq_lower_bound_of_zeta_zero s hs hs1 hz _ hm).trans hB)
  have hB0 : 0 ≤ B := (sq_nonneg _).trans hB
  have hre : s.re ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - s.re by linarith) (show 0 ≤ 1 + s.re by linarith)]
  have him : s.im ^ 2 ≤ T ^ 2 := by
    simpa only [sq_abs] using ((sq_le_sq₀ (abs_nonneg _) hT).mpr ht)
  have hnorm : ‖s‖ ^ 2 ≤ 1 + T ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  linarith [mul_le_mul_of_nonneg_left hnorm hB0]

end RemainderAsymptotics

end RiemannResearch.RH.Pareto.ResidueMellin
