import RiemannResearch.RH.QReciprocalSieveRate
import RiemannResearch.RH.QParetoCostTransfer
import RiemannResearch.RH.QParetoJointBlock

/-!
# Signed factorial-sieve pairing certificates

The actual finite factorial sieve gives quantitative pairing control. For the joint annihilator, prime contributions vanish, but composite contributions remain. No inference from prime tests to squarefree tests is made.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSievePairingCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QReciprocalMetric QReciprocalFullDensity QReciprocalSieveRate
open QParetoCostTransfer QParetoEquivalence QParetoJointAnnihilator

def mobiusPairing (h : ThresholdHilbert) (N : ℕ) : ℝ :=
  -(∑ d ∈ N.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) *
      inner ℝ h (toPareto (D (qResidue d))))

theorem sieve_pairing_identity (h : ThresholdHilbert)
    (hmean : inner ℝ h hilbertOne = 0) (N : ℕ) :
    inner ℝ h (toPareto (factorialSieve N 1)) = mobiusPairing h N := by
  change inner ℝ h (toParetoLinear (factorialSieve N 1)) = _
  simp only [factorialSieve, one_mul, floorAtom, map_sum, map_smul, map_sub,
    inner_sum, inner_smul_right, inner_sub_right]
  change (∑ d ∈ N.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) *
    ((1/(d : ℝ))*inner ℝ h (toPareto qOne) -
      inner ℝ h (toPareto (D (qResidue d))))) = _
  simp only [toPareto_qOne, hmean, mul_zero, zero_sub, mul_neg, Finset.sum_neg_distrib,
    mobiusPairing]

theorem pairing_error_sq (h : ThresholdHilbert)
    (hmean : inner ℝ h hilbertOne = 0) (N : ℕ) :
    |inner ℝ h (toPareto (D qOne)) - mobiusPairing h N|^2 ≤
      ‖h‖^2 / ((N : ℝ)+1) := by
  have he := factorialSieve_pareto_error_sq_le N 1 (by omega)
  simp only [Nat.cast_one, one_pow, one_mul, tailVector_one_eq_D_one] at he
  change ‖toParetoLinear (factorialSieve N 1-D qOne)‖^2 ≤ _ at he
  rw [map_sub, norm_sub_rev] at he
  have hi : inner ℝ h (toPareto (D qOne))-mobiusPairing h N =
      inner ℝ h (toPareto (D qOne)-toPareto (factorialSieve N 1)) := by
    rw [inner_sub_right, sieve_pairing_identity h hmean]
  rw [hi]
  have hb := pow_le_pow_left₀ (abs_nonneg _)
    (abs_real_inner_le_norm h (toPareto (D qOne)-toPareto (factorialSieve N 1))) 2
  rw [mul_pow] at hb
  calc
    _ ≤ ‖h‖^2 * ‖toPareto (D qOne)-toPareto (factorialSieve N 1)‖^2 := hb
    _ ≤ ‖h‖^2 * (1/((N : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring

theorem mobiusPairing_tendsto (h : ThresholdHilbert)
    (hmean : inner ℝ h hilbertOne = 0) :
    Tendsto (mobiusPairing h) atTop (𝓝 (inner ℝ h (toPareto (D qOne)))) := by
  have hs := factorialSieve_tendsto 1 (by omega)
  rw [tailVector_one_eq_D_one] at hs
  have hp := toParetoCLM.continuous.continuousAt.tendsto.comp hs
  have hi : Tendsto (fun N => inner ℝ h (toParetoCLM (factorialSieve N 1)))
      atTop (𝓝 (inner ℝ h (toParetoCLM (D qOne)))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => h) atTop (𝓝 h)).inner hp
  simpa only [toParetoCLM_apply, sieve_pairing_identity h hmean] using hi

theorem reciprocal_pairing_zero_iff (h : ThresholdHilbert)
    (hmean : inner ℝ h hilbertOne = 0) :
    inner ℝ h (toPareto (D qOne)) = 0 ↔
      Tendsto (mobiusPairing h) atTop (𝓝 0) := by
  constructor
  · intro hz
    simpa only [hz] using mobiusPairing_tendsto h hmean
  · intro ht
    exact tendsto_nhds_unique (mobiusPairing_tendsto h hmean) ht

variable (V : Submodule ℝ ThresholdHilbert) (W : Submodule ℝ QHilbert)
variable (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
variable (h : ThresholdHilbert) (hh : h ∈ jointAnnihilator V W)
include hW hh

theorem joint_qMean_sieve_error_sq (N : ℕ) :
    |zetaTwo*inner ℝ qOne (toQ h)-mobiusPairing h N|^2 ≤ ‖h‖^2/((N : ℝ)+1) := by
  have hm : inner ℝ h hilbertOne = 0 := by
    simpa only [real_inner_comm] using joint_mean_zero_of_all_primes V W hW h hh
  have hq := joint_qMean_identity V W hW h hh
  rw [hq]
  have ht : inner ℝ (reciprocalD hilbertOne) h =
      inner ℝ h (toPareto (D qOne)) := by
    rw [toPareto_D, toPareto_qOne, real_inner_comm]
  rw [ht]
  exact pairing_error_sq h hm N

theorem joint_qMean_zero_iff :
    inner ℝ qOne (toQ h) = 0 ↔ Tendsto (mobiusPairing h) atTop (𝓝 0) := by
  have hm : inner ℝ h hilbertOne = 0 := by
    simpa only [real_inner_comm] using joint_mean_zero_of_all_primes V W hW h hh
  have hq := joint_qMean_identity V W hW h hh
  have hi : zetaTwo*inner ℝ qOne (toQ h) = inner ℝ h (toPareto (D qOne)) := by
    rw [hq, toPareto_D, toPareto_qOne, real_inner_comm]
  rw [← reciprocal_pairing_zero_iff h hm, ← hi]
  simp [ne_of_gt zetaTwo_pos]

theorem mobiusPairing_eq_nonprime
    [(jointAnnihilator V W).HasOrthogonalProjection] (N : ℕ) :
    mobiusPairing h N =
      -(∑ d ∈ N.factorial.divisors.filter (fun d => d ≠ 1 ∧ ¬ d.Prime),
        (ArithmeticFunction.moebius d : ℝ)*inner ℝ h (toPareto (D (qResidue d)))) := by
  classical
  unfold mobiusPairing
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hn : ¬(d ≠ 1 ∧ ¬d.Prime) := by
    simpa only [Finset.mem_filter, hd, true_and] using hnot
  by_cases hd1 : d = 1
  · have hz0 : toPareto (0 : QHilbert) = 0 := toParetoLinear.map_zero
    simp [hd1, qResidue_one, map_zero, hz0]
  · have hp : d.Prime := by tauto
    have hz := QParetoJointBlock.reciprocal_cross_zero V W
      (qResidue d) (hW d hp) h hh
    rw [toPareto_D]
    rw [hz, mul_zero]

end RiemannResearch.RH.QSievePairingCertificates
