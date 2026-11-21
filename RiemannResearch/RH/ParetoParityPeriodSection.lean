import RiemannResearch.RH.MixedConductorMetricLifting
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.ParetoParityAdjointHeads
import RiemannResearch.RH.ParetoParityMobiusLifts
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.RH.ParetoParityAdjointCriterion
import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.RH.ParetoParityNormBounds
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith

/-!
# A finite-period criterion for a physical section of norm one

The GCD head of the adjoint parity packet has values `k / (2*k+1)`.
Finite legal fits are periodic; the target has no positive period. Measure the
energy of each fit on a complete period of the legal dictionary, then apply the
bounded-head criterion to the full Hilbert error.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.RH.ExactHeadGcdAtoms

/-- With all divisor classes present, the cumulative synthesis sums the signed
coefficient at the actual GCD of each positive site. -/
theorem synthesis_divisors_eq_sum_gcd (P : ℕ) (hP : P ≠ 0) (c : ℕ → ℝ) (n : ℕ) :
    synthesis P P.divisors c n = ∑ k ∈ Finset.Icc 1 n, c (k.gcd P) := by
  classical
  unfold synthesis atom
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hm : k.gcd P ∈ P.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hP⟩
  simp [mul_ite, hm]

end RiemannResearch.RH.ExactHeadGcdAtoms

namespace RiemannResearch.RH.Pareto

/-- Physical Pareto energy of the positive representatives of one period. -/
def firstPeriodEnergy (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ r : Fin L, positiveWeight (r.val + 1) * (f (r.val + 1)) ^ 2

/-- Folding all subsequent periods costs at most a factor of two for the physical
Pareto square norm. The constant is independent of the period and the profile. -/
theorem periodic_paretoInner_firstPeriod_bounds (L : ℕ) (hL : 0 < L) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hp : ∀ k, f (k + L) = f k) :
    firstPeriodEnergy L f ≤ paretoInner f f ∧
      paretoInner f f ≤ 2 * firstPeriodEnergy L f := by
  rw [periodic_paretoInner L hL f hf hp]
  unfold firstPeriodEnergy
  constructor
  · exact Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_right (positiveWeight_le_progressionWeight L (r.val + 1) hL)
        (sq_nonneg _)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    let j := r.val + 1
    have hj : 0 < j := Nat.succ_pos _
    have hjL : (j : ℝ) ≤ L := by exact_mod_cast (show j ≤ L from r.isLt)
    have hrec : 1 / ((L : ℝ) * ((j : ℝ) + 1)) ≤ positiveWeight j := by
      unfold positiveWeight
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right hjL (by positivity))
    have hweight := (progressionWeight_upper_one L j hL).trans (add_le_add le_rfl hrec)
    calc
      progressionWeight L j * (f j) ^ 2 ≤ (positiveWeight j + positiveWeight j) * (f j) ^ 2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ = 2 * (positiveWeight j * (f j) ^ 2) := by ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The normalized physical residues at stage `m`, with their signed coefficients. -/
def finiteResidueProfile {m : ℕ} (a : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin m, a j * ArithmeticCumulative.residueFraction (j.val + 2) k

theorem hilbertSequence_sum_residueAtom {m : ℕ} (a : Fin m → ℝ) :
    hilbertSequence (∑ j : Fin m, a j • residueAtom j.val) = finiteResidueProfile a := by
  funext k
  rw [← anchoredEvaluationCLM_apply]
  simp only [map_sum, map_smul, smul_eq_mul, anchoredEvaluationCLM_apply, residueAtom,
    normalizedResidueHilbert_sequence, finiteResidueProfile]

/-- The canonical common period for the legal atoms of a finite stage. -/
theorem finiteSpace_lcmUpto_period (m : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace m)
    (k : ℕ) : hilbertSequence v (k + Nat.lcmUpto (m + 1)) = hilbertSequence v k := by
  obtain ⟨a, rfl⟩ := finiteSpace_expansion m v hv
  rw [hilbertSequence_sum_residueAtom]
  apply Finset.sum_congr rfl
  intro j _
  have hd : j.val + 2 ∣ Nat.lcmUpto (m + 1) := by
    unfold Nat.lcmUpto
    exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩)
  simp [ArithmeticCumulative.residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]

/-- The norm of any finite legal fit is controlled by a finite sum at physical sites. -/
theorem finiteSpace_firstPeriod_bounds (m : ℕ) {v : ThresholdHilbert} (hv : v ∈ finiteSpace m) :
    firstPeriodEnergy (Nat.lcmUpto (m + 1)) (hilbertSequence v) ≤ ‖v‖ ^ 2 ∧
      ‖v‖ ^ 2 ≤ 2 * firstPeriodEnergy (Nat.lcmUpto (m + 1)) (hilbertSequence v) := by
  rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted]
  exact periodic_paretoInner_firstPeriod_bounds _ (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _))
    _ (finiteSpace_sequence_abs_le m v hv) (finiteSpace_lcmUpto_period m hv)

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Extend the literal positive GCD head formula to every positive site at fixed modulus. -/
def rawParityGcdProfile (P n : ℕ) : ℝ :=
  ExactHeadGcdAtoms.synthesis P P.divisors
    (fun d => 1 / ((2 * (d : ℝ) - 1) * (2 * (d : ℝ) + 1))) n

/-- The literal GCD extension accumulates positive jumps and grows at least linearly. -/
theorem rawParityGcdProfile_linear_lower (P : ℕ) (hP : 0 < P) (n : ℕ) :
    (n : ℝ) / (4 * (P : ℝ) ^ 2 - 1) ≤ rawParityGcdProfile P n := by
  rw [rawParityGcdProfile, ExactHeadGcdAtoms.synthesis_divisors_eq_sum_gcd P hP.ne']
  calc
    _ = ∑ _k ∈ Finset.Icc 1 n, 1 / (4 * (P : ℝ) ^ 2 - 1) := by
      simp [Nat.card_Icc, div_eq_mul_inv]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      have hd : (1 : ℝ) ≤ k.gcd P := by exact_mod_cast Nat.gcd_pos_of_pos_right k hP
      have hle : (k.gcd P : ℝ) ≤ P := by
        exact_mod_cast Nat.le_of_dvd hP (Nat.gcd_dvd_right k P)
      have hsq := (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) (k.gcd P)) (Nat.cast_nonneg P)).mpr hle
      apply one_div_le_one_div_of_le (mul_pos (by linarith) (by positivity))
      nlinarith only [hsq]

/-- No fixed positive modulus gives a square-summable extension of the raw GCD head. -/
theorem rawParityGcdProfile_not_summable (P : ℕ) (hP : 0 < P) :
    ¬ Summable (fun n => positiveWeight n * (rawParityGcdProfile P n) ^ 2) := by
  let D : ℝ := 4 * (P : ℝ) ^ 2 - 1
  have hp : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg ((P : ℝ) - 1)]
  have hc : 0 < (1 / 2 : ℝ) / D ^ 2 := by positivity
  intro hs
  have hsmall := hs.tendsto_atTop_zero.eventually_lt_const hc
  obtain ⟨n, hn, hlt⟩ := ((Filter.eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ positiveWeight n * (n : ℝ) ^ 2 := by
    have he : positiveWeight n * (n : ℝ) ^ 2 = (n : ℝ) / ((n : ℝ) + 1) := by
      unfold positiveWeight
      field_simp <;> ring
    rw [he, le_div_iff₀ (by positivity)]
    linarith
  have hlin : (n : ℝ) / D ≤ rawParityGcdProfile P n := rawParityGcdProfile_linear_lower P hP n
  have hnon : 0 ≤ (n : ℝ) / D := by positivity
  apply (not_lt_of_ge ?_) hlt
  calc
    (1 / 2 : ℝ) / D ^ 2 ≤ (positiveWeight n * (n : ℝ) ^ 2) / D ^ 2 :=
      div_le_div_of_nonneg_right hhalf (sq_nonneg _)
    _ = positiveWeight n * ((n : ℝ) / D) ^ 2 := by rw [div_pow, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hnon (hnon.trans hlin)).mpr hlin) (positiveWeight_nonneg _)

private theorem sub_norm_sq_bound (x y : ThresholdHilbert) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
    (norm_sub_le x y)
  nlinarith only [h, sq_nonneg (‖x‖ - ‖y‖)]

private theorem compactHead_eq_adjointParity_iff (N : ℕ) (v : ThresholdHilbert) :
    compactHead N v = compactHead N parityAdjointPacket ↔
      ∀ k ≤ N, hilbertSequence v k = (k : ℝ) / (2 * (k : ℝ) + 1) := by
  constructor
  · intro h k hk
    have hcoord := congrArg (fun x => hilbertSequence x k) h
    simpa only [compactHead_sequence, if_pos hk, parityAdjointPacket_coordinate] using hcoord
  · intro h
    apply hilbertSequence_injective
    funext k
    rw [compactHead_sequence, compactHead_sequence, parityAdjointPacket_coordinate]
    by_cases hk : k ≤ N <;> simp [hk, h]

/-- The right side uses only finite arithmetic. A single energy budget must work
for legal coefficient arrays fitting the adjoint parity profile on arbitrarily long heads. -/
theorem exists_contractive_legalMeanSection_iff_bounded_parity_periods :
    (∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∃ m : ℕ, ∃ a : Fin m → ℝ,
        (∀ k ≤ N, finiteResidueProfile a k = (k : ℝ) / (2 * (k : ℝ) + 1)) ∧
        firstPeriodEnergy (Nat.lcmUpto (m + 1)) (finiteResidueProfile a) ≤ C := by
  rw [exists_contractive_legalMeanSection_iff_limitEnergy_zero,
    ← normalizedParityCapture_eq_upper_iff,
    normalizedParityCapture_eq_upper_iff_bounded_finite_adjoint_heads]
  constructor
  · rintro ⟨C, h⟩
    refine ⟨2 * ‖parityAdjointPacket‖ ^ 2 + 2 * C, fun N => ?_⟩
    obtain ⟨m, v, hv, hhead, herror⟩ := h N
    obtain ⟨a, ha⟩ := finiteSpace_expansion m v hv
    have hprofile : hilbertSequence v = finiteResidueProfile a := ha ▸ hilbertSequence_sum_residueAtom a
    refine ⟨m, a, hprofile ▸ (compactHead_eq_adjointParity_iff N v).mp hhead, ?_⟩
    rw [← hprofile]
    apply (finiteSpace_firstPeriod_bounds m hv).1.trans
    have hnorm := sub_norm_sq_bound parityAdjointPacket (parityAdjointPacket - v)
    rw [sub_sub_cancel] at hnorm
    linarith only [hnorm, herror]
  · rintro ⟨C, h⟩
    refine ⟨2 * ‖parityAdjointPacket‖ ^ 2 + 4 * C, fun N => ?_⟩
    obtain ⟨m, a, hhead, hperiod⟩ := h N
    let v := ∑ j : Fin m, a j • residueAtom j.val
    have hv : v ∈ finiteSpace m := (finiteSpace m).sum_mem fun j _ =>
      (finiteSpace m).smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    have hprofile : hilbertSequence v = finiteResidueProfile a := hilbertSequence_sum_residueAtom a
    refine ⟨m, v, hv, (compactHead_eq_adjointParity_iff N v).mpr (hprofile.symm ▸ hhead), ?_⟩
    rw [← hprofile] at hperiod
    linarith only [sub_norm_sq_bound parityAdjointPacket v,
      (finiteSpace_firstPeriod_bounds m hv).2, hperiod]

/-- A bounded subsequence of finite-period energies of the explicit Möbius parity
lifts is sufficient for a physical contractive section. -/
theorem exists_contractive_legalMeanSection_of_parityMobiusLift_periods (C : ℝ)
    (hC : ∃ᶠ N : ℕ in Filter.atTop,
      firstPeriodEnergy (Nat.lcmUpto (N * (N + 1) + 1)) (hilbertSequence (parityMobiusLift N)) ≤ C) :
    ∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1 := by
  apply exists_contractive_legalMeanSection_iff_limitEnergy_zero.mpr
  apply normalizedParityCapture_eq_upper_iff.mp
  apply normalizedParityCapture_eq_upper_of_bounded_adjoint_heads parityMobiusLift
    (fun N => RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace _ (parityMobiusLift_mem N))
    parityMobiusLift_exact (2 * ‖parityAdjointPacket‖ ^ 2 + 4 * C)
  apply hC.mono
  intro N hN
  linarith only [sub_norm_sq_bound parityAdjointPacket (parityMobiusLift N),
    (finiteSpace_firstPeriod_bounds _ (parityMobiusLift_mem N)).2, hN]

end RiemannResearch.RH.Pareto.PrimePowerSchur
