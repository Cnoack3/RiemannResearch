import RiemannResearch.RH.QFiniteForcingData
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.Analysis.PositiveCompressionCertificate
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Quantitative means for the actual joint arithmetic annihilator

No symmetry of P and Q is assumed. A common annihilator at conductor m
annihilates the physical ratio (n mod m)/n. This gives the finite K bound,
and the all-prime limit gives Pareto mean zero. The Q mean is a different
pairing, bounded by approximation of D1 by known annihilators.
-/
noncomputable section
namespace RiemannResearch.RH.QJointAnnihilatorMeans
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QSquarefreeFiniteDisplacement QShiftedReciprocal QParetoMetric QParetoEquivalence
open RiemannResearch.Analysis.PositiveCompressionCertificate

theorem ratio_pair_eq_zero (m : ℕ) (hm : 0 < m) (k : QHilbert)
    (hq : inner ℝ (qResidue m) k = 0)
    (hp : inner ℝ (toPareto (qResidue m)) (toPareto k) = 0) :
    inner ℝ (ratioVector m) (toPareto k) = 0 := by
  have h := pareto_inner_identity (qResidue m) k
  rw [hp, hq, zero_sub] at h
  have hb : inner ℝ (qResidue m) (B k) = 0 := by
    have hz := (mul_eq_zero.mp h.symm).resolve_left zetaTwo_pos.ne'
    exact neg_eq_zero.mp hz
  rw [← ratioVector_pair_shifted m hm, hb, mul_zero]

theorem pareto_mean_sq_le (m : ℕ) (hm : 0 < m) (k : QHilbert)
    (hq : inner ℝ (qResidue m) k = 0)
    (hp : inner ℝ (toPareto (qResidue m)) (toPareto k) = 0) :
    (inner ℝ hilbertOne (toPareto k))^2 ≤ (1/(m:ℝ))*‖toPareto k‖^2 := by
  have hratio := ratio_pair_eq_zero m hm k hq hp
  have he : inner ℝ (hilbertOne-ratioVector m) (toPareto k) =
      inner ℝ hilbertOne (toPareto k) := by rw [inner_sub_left, hratio, sub_zero]
  have hc := real_inner_mul_inner_self_le (hilbertOne-ratioVector m) (toPareto k)
  rw [he, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  calc
    _ ≤ ‖hilbertOne-ratioVector m‖^2*‖toPareto k‖^2 := by nlinarith only [hc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (ratioVector_error_norm_sq_le m hm) (sq_nonneg _)

/-- This strengthens the uniform mean bound by retaining only the actual tail. -/
theorem pareto_mean_tail_bound (m : ℕ) (hm : 0 < m) (k : QHilbert)
    (hq : inner ℝ (qResidue m) k = 0)
    (hp : inner ℝ (toPareto (qResidue m)) (toPareto k) = 0) :
    |inner ℝ hilbertOne (toPareto k)| ≤ Real.sqrt (1/(m:ℝ)) *
      ‖toPareto (QAnnihilatorTailEscape.tail (m-1) k)‖ := by
  have hratio := ratio_pair_eq_zero m hm k hq hp
  have he : inner ℝ hilbertOne (toPareto k) =
      inner ℝ (hilbertOne-ratioVector m) (toPareto k) := by
    rw [inner_sub_left, hratio, sub_zero]
  rw [he, defect_tail_pair]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (ratioVector_error_norm_sq_le m hm))
      (norm_nonneg _))

/-- Any closed K annihilating this one ratio obeys the finite-stage bound. -/
theorem finite_joint_projection_sq (K : Submodule ℝ ThresholdHilbert)
    [K.HasOrthogonalProjection] (m : ℕ) (hm : 0 < m)
    (hK : ∀ k ∈ K, inner ℝ (ratioVector m) k = 0) :
    ‖K.starProjection hilbertOne‖^2 ≤ 1/(m:ℝ) := by
  have hz : K.starProjection (ratioVector m) = 0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero K.zero_mem
    intro k hk
    simpa only [sub_zero] using hK k hk
  have he : K.starProjection hilbertOne =
      K.starProjection (hilbertOne-ratioVector m) := by rw [map_sub, hz, sub_zero]
  rw [he]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (projection_norm_le K _)).trans (ratioVector_error_norm_sq_le m hm)

/-- The joint orthogonality hypotheses alone suffice; no legal-space
membership is needed for the Pareto mean-zero consequence. -/
theorem pareto_mean_zero_of_all_primes (k : QHilbert)
    (hq : ∀ p : ℕ, p.Prime → inner ℝ (qResidue p) k = 0)
    (hp : ∀ p : ℕ, p.Prime →
      inner ℝ (toPareto (qResidue p)) (toPareto k) = 0) :
    inner ℝ hilbertOne (toPareto k) = 0 := by
  by_contra hzero
  have hs : 0 < (inner ℝ hilbertOne (toPareto k))^2 := sq_pos_of_ne_zero hzero
  obtain ⟨N, hN⟩ := exists_nat_gt (‖toPareto k‖^2/(inner ℝ hilbertOne (toPareto k))^2)
  obtain ⟨p, hNp, hprime⟩ := Nat.exists_infinite_primes N
  have hb := pareto_mean_sq_le p hprime.pos k (hq p hprime) (hp p hprime)
  have hpR : (0:ℝ)<p := by exact_mod_cast hprime.pos
  have hNpR : (N:ℝ) ≤ p := by exact_mod_cast hNp
  have hlarge : ‖toPareto k‖^2 < (p:ℝ)*(inner ℝ hilbertOne (toPareto k))^2 :=
    ((div_lt_iff₀ hs).mp hN).trans_le (mul_le_mul_of_nonneg_right hNpR hs.le)
  have hsmall : (inner ℝ hilbertOne (toPareto k))^2 * (p:ℝ) ≤ ‖toPareto k‖^2 := by
    apply (le_div_iff₀ hpR).mp
    simpa only [one_div_mul_eq_div] using hb
  nlinarith only [hlarge, hsmall]

/-- Exact remaining Q-mean obstruction, after the Pareto mean is known zero. -/
theorem q_mean_exact (k : QHilbert) (hp : inner ℝ hilbertOne (toPareto k) = 0) :
    zetaTwo*inner ℝ qOne k = inner ℝ (reciprocalD hilbertOne) (toPareto k) := by
  have h := inner_identity qOne k
  rw [toPareto_qOne, hp, zero_add] at h
  simpa only [metricPairing, toPareto_qOne, ← reciprocalD_symmetric] using h

/-- Quantitative K-block certificate from any verified annihilating trial.
The approximation error is the complete Pareto norm. -/
theorem q_mean_approximation_bound (k : QHilbert) (a : ThresholdHilbert)
    (hp : inner ℝ hilbertOne (toPareto k) = 0)
    (ha : inner ℝ a (toPareto k) = 0) :
    |zetaTwo*inner ℝ qOne k| ≤ ‖reciprocalD hilbertOne-a‖*‖toPareto k‖ := by
  rw [q_mean_exact k hp]
  have he : inner ℝ (reciprocalD hilbertOne) (toPareto k) =
      inner ℝ (reciprocalD hilbertOne-a) (toPareto k) := by
    rw [inner_sub_left, ha, sub_zero]
  rw [he]
  exact abs_real_inner_le_norm _ _


/-- Direct finite K criterion in the two physical metrics. -/
theorem finite_joint_projection_sq_of_pq (K : Submodule ℝ ThresholdHilbert)
    [K.HasOrthogonalProjection] (m : ℕ) (hm : 0 < m)
    (hQ : ∀ k ∈ K, inner ℝ (qResidue m) (toQ k) = 0)
    (hP : ∀ k ∈ K, inner ℝ (toPareto (qResidue m)) k = 0) :
    ‖K.starProjection hilbertOne‖ ^ 2 ≤ 1/(m:ℝ) := by
  apply finite_joint_projection_sq K m hm
  intro k hk
  simpa only [toPareto_toQ] using
    ratio_pair_eq_zero m hm (toQ k) (hQ k hk)
      (by simpa only [toPareto_toQ] using hP k hk)

/-- Centering D1 gives an unconditional quantitative bound on the Q mean
for every actual common prime annihilator, without assuming Q mean zero. -/
theorem joint_q_mean_centered_bound (k : QHilbert) (c : ℝ)
    (hq : ∀ p : ℕ, p.Prime → inner ℝ (qResidue p) k = 0)
    (hp : ∀ p : ℕ, p.Prime →
      inner ℝ (toPareto (qResidue p)) (toPareto k) = 0) :
    |zetaTwo * inner ℝ qOne k| ≤
      ‖reciprocalD hilbertOne-c • hilbertOne‖ * ‖toPareto k‖ := by
  have hm := pareto_mean_zero_of_all_primes k hq hp
  exact q_mean_approximation_bound k (c • hilbertOne) hm
    (by rw [real_inner_smul_left, hm, mul_zero])

end RiemannResearch.RH.QJointAnnihilatorMeans
