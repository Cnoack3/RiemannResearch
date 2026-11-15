import RiemannResearch.RH.PrimorialDensityLowerBound
import RiemannResearch.RH.PrimorialSieveLift
import RiemannResearch.RH.QuantitativeSieve
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Intervals
/-!
# Every single-cutoff primorial lift has divergent complete source norm

Source: the user's P/Q augmented-density continuation, Priority B, specifies
v_(N,K) = density(N) * K * g_K - sum_(d | primorial N) mu(d) * g_d.
The present argument extends the diagonal obstruction to every positive
cutoff choice K_N, with no growth assumption on K_N.

First retain the exact physical count and complete norm identities. Two
finite blocks then force large source energy: covered-head drift for small
cutoffs, and the first jump for large cutoffs. The elementary prime-product
lemma discharges the arithmetic growth input without RH. For cofinal K_N,
the damped images still converge to D1. Any additional correction that makes
the sources bounded must itself have divergent norm.

This does not exclude signed multiscale constructions. The provider application
is in PrimorialCutoffLeakage. No mathematical novelty beyond the checked
repository extension is asserted.
-/

noncomputable section
open Filter
open scoped Topology
open scoped BigOperators
namespace RiemannResearch.RH.PrimorialCutoff
open ZetaTwoHilbert ZetaTwoProbability QPrimeSieve QMobiusPrimePacket
open ArithmeticCumulative QuantitativeSieve QReciprocalMetric QFullResidueProjection
open PrimorialSieveLift
def cutoffLift (L K : ℕ) : QHilbert :=
  (divisorDensity L * (K : ℝ)) • qResidue K -
    ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue d
theorem cutoffLift_mem (L K : ℕ) (hK : 0 < K) :
    cutoffLift L K ∈ legalSpan := by
  apply legalSpan.sub_mem (legalSpan.smul_mem _ (residue_mem_legalSpan K hK))
  apply legalSpan.sum_mem
  intro d hd
  exact legalSpan.smul_mem _ (residue_mem_legalSpan d (Nat.pos_of_mem_divisors hd))
theorem cutoffLift_sequence (L K n : ℕ) (hL : 0 < L) (hK : 0 < K) :
    qSequence (cutoffLift L K) n = coprimeCount L n -
      divisorDensity L * (K : ℝ) * ((n/K : ℕ) : ℝ) := by
  have hr : qSequence (cutoffLift L K) n =
      divisorDensity L * (K : ℝ) * residueFraction K n + divisorSieve L n := by
    change qSequenceLinear (_ - _) n = _
    rw [map_sub, map_smul, map_sum]
    simp only [Pi.sub_apply, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change divisorDensity L * (K : ℝ) * qSequence (qResidue K) n -
      ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) * qSequence (qResidue d) n = _
    simp only [qSequence_qResidue, divisorSieve, sub_eq_add_neg]
  rw [hr, Pareto.residueFraction_eq_div_sub_floor K n hK,
    divisorSieve_eq_count_sub_linear L n (by omega)]
  have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  field_simp
  ring
theorem damped_cutoffLift_eq (L K : ℕ) :
    D (cutoffLift L K) = finiteApprox L 1 K := by
  rw [cutoffLift, map_sub, map_smul, map_sum, finiteApprox, coefficient,
    QDensityMetric.approximation]
  simp only [Nat.cast_one, div_one, one_mul, map_smul, smul_smul]

theorem cutoff_norm_sq_exact (L K : ℕ) (hL : 0 < L) (hK : 0 < K) :
    ‖cutoffLift L K‖^2 = ∑' n : ℕ, positiveQWeight n *
      (coprimeCount L n - divisorDensity L*(K : ℝ)*((n/K : ℕ) : ℝ))^2 := by
  rw [qNorm_weighted_sq]
  congr 1
  funext n
  rw [cutoffLift_sequence L K n hL hK]

theorem coprimeCount_step_le (L n : ℕ) :
    coprimeCount L (n+1) ≤ coprimeCount L n + 1 := by
  simp only [coprimeCount, cumulative, Finset.sum_range_succ]
  split_ifs <;> linarith
theorem coprimeCount_add_le (L n h : ℕ) :
    coprimeCount L (n+h) ≤ coprimeCount L n + (h : ℝ) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hs := coprimeCount_step_le L (n+h)
    push_cast
    simpa only [Nat.add_assoc] using (show coprimeCount L (n+h+1) ≤
      coprimeCount L n + ((h : ℝ)+1) by linarith)

theorem interval_sq_le_norm (f : QHilbert) (a b : ℕ) (ha : 0 < a) :
    (∑ n ∈ Finset.Ico a b, (qSequence f n)^2) ≤
      (zetaTwo * (b : ℝ)^2) * ‖f‖^2 := by
  have hZ := zetaTwo_pos
  rw [qNorm_weighted_sq]
  have hb : 0 ≤ zetaTwo * (b : ℝ)^2 := by positivity
  calc
    _ ≤ ∑ n ∈ Finset.Ico a b,
        (zetaTwo * (b : ℝ)^2) * (positiveQWeight n * (qSequence f n)^2) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨han, hnb⟩ := Finset.mem_Ico.mp hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hnR : (n : ℝ) ≤ b := by exact_mod_cast hnb.le
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hs : (n : ℝ)^2 ≤ (b : ℝ)^2 :=
        (sq_le_sq₀ hnpos.le (Nat.cast_nonneg b)).mpr hnR
      calc
        _ = (zetaTwo * (n : ℝ)^2) * (positiveQWeight n * (qSequence f n)^2) := by
          unfold positiveQWeight
          field_simp [hn0, ne_of_gt zetaTwo_pos]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs zetaTwo_pos.le)
          (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        ((qSequence_square_summable f).sum_le_tsum _
          (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))) hb

theorem cutoff_jump_pair (L K H i : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hHK : H < K) (hi : i < H)
    (hsize : 2 * (H : ℝ) ≤ divisorDensity L * (K : ℝ)) :
    (divisorDensity L * (K : ℝ))^2 / 8 ≤
      (qSequence (cutoffLift L K) (K-H+i))^2 +
      (qSequence (cutoffLift L K) (K+i))^2 := by
  have h0 : (K-H+i)/K = 0 := Nat.div_eq_of_lt (by omega)
  have h1 : (K+i)/K = 1 := by
    rw [Nat.add_div_left _ hK, Nat.div_eq_of_lt (by omega)]
  have hcount := coprimeCount_add_le L (K-H+i) H
  have he : K-H+i+H = K+i := by omega
  rw [he] at hcount
  rw [cutoffLift_sequence L K _ hL hK, cutoffLift_sequence L K _ hL hK, h0, h1]
  norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, sub_zero, mul_one]
  nlinarith [sq_nonneg (coprimeCount L (K-H+i) +
    (coprimeCount L (K+i) - divisorDensity L * (K : ℝ))),
    sq_nonneg (divisorDensity L * (K : ℝ) - 2*(H : ℝ))]

theorem cutoff_jump_energy (L K H : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hHK : H < K)
    (hsize : 2 * (H : ℝ) ≤ divisorDensity L * (K : ℝ)) :
    (H : ℝ) * divisorDensity L ^ 2 / (32 * zetaTwo) ≤ ‖cutoffLift L K‖^2 := by
  have hZ := zetaTwo_pos
  have hsum :
      (H : ℝ) * (divisorDensity L * (K : ℝ))^2 / 8 ≤
      ∑ n ∈ Finset.Ico (K-H) (K+H), (qSequence (cutoffLift L K) n)^2 := by
    rw [← Finset.sum_Ico_consecutive _ (show K-H ≤ K by omega) (show K ≤ K+H by omega),
      Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show K-(K-H) = H by omega, show K+H-K = H by omega,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range H, (divisorDensity L * (K : ℝ))^2 / 8 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        cutoff_jump_pair L K H i hL hK hHK (Finset.mem_range.mp hi) hsize)
  have hnorm := interval_sq_le_norm (cutoffLift L K) (K-H) (K+H) (by omega)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hHR : (H : ℝ) ≤ K := by exact_mod_cast hHK.le
  have hs : ((K+H : ℕ) : ℝ)^2 ≤ 4*(K : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg ((K : ℝ)-(H : ℝ))]
  have hupper : zetaTwo * ((K+H : ℕ) : ℝ)^2 * ‖cutoffLift L K‖^2 ≤
      4*zetaTwo*(K : ℝ)^2 * ‖cutoffLift L K‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs zetaTwo_pos.le)
      (sq_nonneg ‖cutoffLift L K‖)]
  have hall := hsum.trans (hnorm.trans hupper)
  apply (div_le_iff₀ (by positivity : 0 < 32*zetaTwo)).mpr
  nlinarith [sq_pos_of_pos hKR]

theorem cutoff_small_energy (L K M : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hM : 0 < M) (hKM : K ≤ M) (hc : Covers L (3 * M))
    (hsize : 2 ≤ divisorDensity L * (M : ℝ)) :
    (M : ℝ) * divisorDensity L ^ 2 / (36*zetaTwo) ≤ ‖cutoffLift L K‖^2 := by
  have hZ := zetaTwo_pos
  have ha : 0 ≤ divisorDensity L := by
    simpa [coefficient] using (coefficient_bounds L 1 (by omega) (by omega)).1
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ico (2*M) (3*M)) :
      (divisorDensity L * (M : ℝ))^2 / 4 ≤ (qSequence (cutoffLift L K) n)^2 := by
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hn
    have hq : M ≤ K*(n/K) := by
      have := Nat.mod_add_div n K
      have := Nat.mod_lt n hK
      omega
    have hqr : (M : ℝ) ≤ (K : ℝ)*((n/K : ℕ) : ℝ) := by exact_mod_cast hq
    have ham := mul_le_mul_of_nonneg_left hqr ha
    rw [cutoffLift_sequence L K n hL hK,
      coprimeCount_head L (3*M) n (by omega) hnhi.le hc]
    nlinarith [sq_nonneg (1-divisorDensity L*(K : ℝ)*((n/K : ℕ) : ℝ) +
      divisorDensity L*(M : ℝ)/2)]
  have hlo : (M : ℝ) * (divisorDensity L * (M : ℝ))^2 / 4 ≤
      ∑ n ∈ Finset.Ico (2*M) (3*M), (qSequence (cutoffLift L K) n)^2 := by
    calc
      _ = ∑ _n ∈ Finset.Ico (2*M) (3*M), (divisorDensity L * (M : ℝ))^2 / 4 := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show 3*M-2*M=M by omega]
        ring
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hnorm := hlo.trans (interval_sq_le_norm (cutoffLift L K) (2*M) (3*M) (by omega))
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast at hnorm
  apply (div_le_iff₀ (by positivity : 0 < 36*zetaTwo)).mpr
  nlinarith [sq_pos_of_pos hMR]

theorem cutoff_uniform_energy (L K M : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hM : 0 < M) (hc : Covers L (3 * M))
    (hsize : 4 ≤ divisorDensity L * (M : ℝ)) :
    (M : ℝ) * divisorDensity L ^ 3 / (128*zetaTwo) ≤ ‖cutoffLift L K‖^2 := by
  have hZ := zetaTwo_pos
  have ha := coefficient_bounds L 1 (by omega) (by omega)
  simp only [coefficient, Nat.cast_one, div_one] at ha
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases hKM : K ≤ M
  · have h := cutoff_small_energy L K M hL hK hM hKM hc (by linarith)
    apply le_trans _ h
    apply (div_le_div_iff₀ (by positivity : 0 < 128*zetaTwo)
      (by positivity : 0 < 36*zetaTwo)).mpr
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hMR.le
      (sq_nonneg (divisorDensity L)))
      (by linarith : 0 ≤ 128-36*divisorDensity L)) hZ.le]
  · let H : ℕ := ⌊divisorDensity L*(M : ℝ)/2⌋₊
    have hHupper : (H : ℝ) ≤ divisorDensity L*(M : ℝ)/2 :=
      Nat.floor_le (by positivity)
    have hHlower : divisorDensity L*(M : ℝ)/4 ≤ (H : ℝ) := by
      have := Nat.lt_floor_add_one (divisorDensity L*(M : ℝ)/2)
      change divisorDensity L*(M : ℝ)/2 < (H : ℝ)+1 at this
      linarith
    have hHK : H < K := by
      have hKR : (M : ℝ) < K := by exact_mod_cast (by omega : M < K)
      have : (H : ℝ) < K := by nlinarith
      exact_mod_cast this
    have hsizeK : 2*(H : ℝ) ≤ divisorDensity L*(K : ℝ) := by
      have : (M : ℝ) ≤ K := by exact_mod_cast (by omega : M ≤ K)
      nlinarith [mul_le_mul_of_nonneg_left this ha.1]
    have h := cutoff_jump_energy L K H hL hK hHK hsizeK
    apply le_trans _ h
    apply (div_le_div_iff₀ (by positivity : 0 < 128*zetaTwo)
      (by positivity : 0 < 32*zetaTwo)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hHlower (sq_nonneg (divisorDensity L))]
theorem primorial_density_eq (N : ℕ) :
    divisorDensity (primorial N) = PrimorialDensity.density N := by
  rw [divisorDensity_euler _ (squarefree_primorial N), primeFactors_primorial]
  rfl

theorem third_density_cube_growth :
    Tendsto (fun N : ℕ => ((N/3 : ℕ) : ℝ) * PrimorialDensity.density N ^ 3)
      atTop atTop := by
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)*PrimorialDensity.density N^3-2)/3)
      atTop atTop := by
    have ht' := tendsto_atTop_add_const_right atTop (-2 : ℝ)
      PrimorialDensity.density_cube_growth
    simpa only [sub_eq_add_neg] using ht'.atTop_div_const (by norm_num : (0 : ℝ) < 3)
  apply tendsto_atTop_mono _ ht
  intro N
  have hN : (N : ℝ) ≤ 3*((N/3 : ℕ) : ℝ)+2 := by
    exact_mod_cast (show N ≤ 3*(N/3)+2 by omega)
  have ha := PrimorialDensity.density_pos N
  have hb := PrimorialDensity.density_le_one N
  have hc : PrimorialDensity.density N^3 ≤ 1 := pow_le_one₀ ha.le hb
  have hm := mul_le_mul_of_nonneg_right hN (pow_nonneg ha.le 3)
  nlinarith

/-- Every positive single-cutoff choice has divergent complete Q source energy. -/
theorem primorial_cutoff_norm_sq_tendsto (K : ℕ → ℕ) (hK : ∀ N, 0 < K N) :
    Tendsto (fun N : ℕ => ‖cutoffLift (primorial N) (K N)‖^2) atTop atTop := by
  have hZ := zetaTwo_pos
  have ht := third_density_cube_growth.const_mul_atTop
    (by positivity : 0 < 1/(128*zetaTwo))
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    third_density_cube_growth.eventually (eventually_ge_atTop (4 : ℝ))] with N hN hsize
  have ha := PrimorialDensity.density_pos N
  have hb := PrimorialDensity.density_le_one N
  have hcube : PrimorialDensity.density N^3 ≤ PrimorialDensity.density N := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hb),
      mul_nonneg ha.le (sq_nonneg (PrimorialDensity.density N-1))]
  have hsize' : 4 ≤ divisorDensity (primorial N)*((N/3 : ℕ) : ℝ) := by
    rw [primorial_density_eq]
    nlinarith [mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg (N/3))]
  have hc : Covers (primorial N) (3*(N/3)) := by
    intro j hj hjN
    exact primorial_covers N j hj (hjN.trans (Nat.mul_div_le N 3))
  have h := cutoff_uniform_energy (primorial N) (K N) (N/3)
    (primorial_pos N) (hK N) (by omega) hc hsize'
  rw [primorial_density_eq] at h
  simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using h

theorem primorial_cutoff_p_norm_sq_tendsto (K : ℕ → ℕ) (hK : ∀ N, 0 < K N) :
    Tendsto (fun N : ℕ =>
      ‖ZetaTwoParetoTransfer.toPareto (cutoffLift (primorial N) (K N))‖^2)
      atTop atTop := by
  have hZ := zetaTwo_pos
  have ht := (primorial_cutoff_norm_sq_tendsto K hK).const_mul_atTop
    (by positivity : 0 < zetaTwo/2)
  apply tendsto_atTop_mono _ ht
  intro N
  have h := ZetaTwoParetoTransfer.zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (cutoffLift (primorial N) (K N))
  nlinarith

theorem primorial_cutoff_damped_tendsto (K : ℕ → ℕ) (hK : ∀ N, 0 < K N)
    (hcofinal : Tendsto K atTop atTop) :
    Tendsto (fun N : ℕ => D (cutoffLift (primorial N) (K N))) atTop (𝓝 (D qOne)) := by
  have hpred : Tendsto (fun N => K N - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hcofinal.eventually (eventually_ge_atTop (b+1))] with N hN
    omega
  have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tailMass_tendsto qModel).comp hpred)
  have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp (tailMass_tendsto qModel)
  have ht : Tendsto (fun N : ℕ =>
      Real.sqrt (tailMass qModel (K N - 1)) + Real.sqrt (tailMass qModel N))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, add_zero] using h1.add h2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) _ ht
  intro N
  have h := finiteApprox_error qModel (primorial N) N 1 (K N)
    (primorial_ne_zero N) (by norm_num) (hK N) (primorial_covers N)
  simpa only [← damped_cutoffLift_eq, tailVector_one_eq,
    Nat.cast_one, div_one, one_mul, qModel, ContinuousLinearMap.id_apply] using h

/-- An explicit bound independent of the choice of cutoff. -/
theorem primorial_uniform_energy_explicit (N K : ℕ) (hN : 3 ≤ N) (hK : 0 < K)
    (hsize : 24 ≤ (N : ℝ)*PrimorialDensity.density N) :
    (N : ℝ)*PrimorialDensity.density N^3/(768*zetaTwo) ≤
      ‖cutoffLift (primorial N) K‖^2 := by
  have hZ := zetaTwo_pos
  have ha := (PrimorialDensity.density_pos N).le
  have hfloor : (N : ℝ) ≤ 6*((N/3 : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ 6*(N/3) by omega)
  have hsize' : 4 ≤ divisorDensity (primorial N)*((N/3 : ℕ) : ℝ) := by
    rw [primorial_density_eq]
    nlinarith [mul_le_mul_of_nonneg_right hfloor ha]
  have hc : Covers (primorial N) (3*(N/3)) := by
    intro j hj hjN
    exact primorial_covers N j hj (hjN.trans (Nat.mul_div_le N 3))
  have h := cutoff_uniform_energy (primorial N) K (N/3)
    (primorial_pos N) hK (by omega) hc hsize'
  rw [primorial_density_eq] at h
  apply le_trans _ h
  apply (div_le_div_iff₀ (by positivity : 0 < 768*zetaTwo)
    (by positivity : 0 < 128*zetaTwo)).mpr
  have hm := mul_le_mul_of_nonneg_right hfloor (pow_nonneg ha 3)
  nlinarith [mul_le_mul_of_nonneg_right hm hZ.le]

private theorem norm_tendsto_of_sq {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) (h : Tendsto (fun N => ‖f N‖^2) atTop atTop) :
    Tendsto (fun N => ‖f N‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [h.eventually (eventually_ge_atTop ((max b 0)^2))] with N hN
  exact (le_max_left b 0).trans
    ((sq_le_sq₀ (le_max_right b 0) (norm_nonneg _)).mp hN)

/-- No sequence of positive cutoffs can yield bounded sources, in either measure. -/
theorem primorial_cutoff_norms_tendsto (K : ℕ → ℕ) (hK : ∀ N, 0 < K N) :
    Tendsto (fun N => ‖cutoffLift (primorial N) (K N)‖) atTop atTop ∧
      Tendsto (fun N =>
        ‖ZetaTwoParetoTransfer.toPareto (cutoffLift (primorial N) (K N))‖) atTop atTop :=
  ⟨norm_tendsto_of_sq _ (primorial_cutoff_norm_sq_tendsto K hK),
    norm_tendsto_of_sq _ (primorial_cutoff_p_norm_sq_tendsto K hK)⟩

/-- Any correction that makes these sources bounded must itself have divergent norm. -/
theorem necessary_correction_norm_tendsto (K : ℕ → ℕ) (hK : ∀ N, 0 < K N)
    (c : ℕ → QHilbert) (C : ℝ)
    (hbound : ∀ N, ‖cutoffLift (primorial N) (K N) + c N‖ ≤ C) :
    Tendsto (fun N => ‖c N‖) atTop atTop := by
  have ht := (primorial_cutoff_norms_tendsto K hK).1
  apply tendsto_atTop.2
  intro b
  filter_upwards [ht.eventually (eventually_ge_atTop (b+C))] with N hN
  have hn : ‖cutoffLift (primorial N) (K N)‖ ≤
      ‖cutoffLift (primorial N) (K N) + c N‖ + ‖c N‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (cutoffLift (primorial N) (K N) + c N) (c N)
  linarith [hbound N]
end RiemannResearch.RH.PrimorialCutoff
