import RiemannResearch.RH.QuantitativeSieve
import RiemannResearch.RH.QReciprocalFullDensity
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Module

/-!
# The physical sieve lift and its divergent complete source energy

Source: user-provided `PQ_Augmented_Density_and_RH_Agenda.pdf`,
14 November 2026, Section 6.2 and Section 7.6 item 2. The exact floor and
periodic-count formulas precede the lower bound. No assertion of bounded
source energy is inferred from convergence after reciprocal damping.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimorialSieveLift
open ZetaTwoHilbert ZetaTwoProbability QPrimeSieve QMobiusPrimePacket
open ArithmeticCumulative QuantitativeSieve QReciprocalMetric QFullResidueProjection

def lift (L : ℕ) : QHilbert :=
  (Nat.totient L : ℝ) • qResidue L -
    ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue d

theorem residue_mem_legalSpan (d : ℕ) (hd : 0 < d) : qResidue d ∈ legalSpan := by
  by_cases h : d = 1
  · simp [h]
  · exact Submodule.subset_span ⟨d-2, congrArg qResidue (Nat.sub_add_cancel (by omega))⟩

theorem lift_mem_legalSpan (L : ℕ) (hL : 0 < L) : lift L ∈ legalSpan := by
  apply legalSpan.sub_mem (legalSpan.smul_mem _ (residue_mem_legalSpan L hL))
  apply legalSpan.sum_mem
  intro d hd
  exact legalSpan.smul_mem _ (residue_mem_legalSpan d (Nat.pos_of_mem_divisors hd))

theorem lift_sequence_raw (L n : ℕ) :
    qSequence (lift L) n = (Nat.totient L : ℝ) * residueFraction L n + divisorSieve L n := by
  change qSequenceLinear (_ - _) n = _
  rw [map_sub, map_smul, map_sum]
  simp only [Pi.sub_apply, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  change (Nat.totient L : ℝ) * qSequence (qResidue L) n -
    ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) * qSequence (qResidue d) n = _
  simp only [qSequence_qResidue, divisorSieve, sub_eq_add_neg]

/-- Equation (36), first equality, retaining the integer quotient exactly. -/
theorem lift_sequence_floor (L n : ℕ) (hL : 0 < L) :
    qSequence (lift L) n = coprimeCount L n -
      (Nat.totient L : ℝ) * ((n/L : ℕ) : ℝ) := by
  rw [lift_sequence_raw, Pareto.residueFraction_eq_div_sub_floor L n hL,
    divisorSieve_eq_count_sub_linear L n (by omega), divisorDensity_eq_totient L (by omega)]
  ring

theorem lift_sequence_mod (L n : ℕ) : qSequence (lift L) n = qSequence (lift L) (n%L) := by
  simp only [lift_sequence_raw, residueFraction, Nat.mod_mod, divisorSieve]
  congr 2
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mod_mod_of_dvd n (Nat.dvd_of_mem_divisors hd)]

/-- Equation (36), second equality: the actual physical value is a nonnegative count. -/
theorem lift_sequence_count (L n : ℕ) (hL : 0 < L) :
    qSequence (lift L) n = coprimeCount L (n%L) := by
  rw [lift_sequence_mod, lift_sequence_floor L (n%L) hL,
    Nat.div_eq_of_lt (Nat.mod_lt n hL)]
  simp

/-- This source is exactly the finite constructor with m=1 and K=L after damping. -/
theorem damped_lift_eq (L : ℕ) (hL : 0 < L) : D (lift L) = finiteApprox L 1 L := by
  rw [lift, map_sub, map_smul, map_sum, finiteApprox, coefficient,
    divisorDensity_eq_totient L (by omega), QDensityMetric.approximation]
  simp only [Nat.cast_one, div_one, one_mul, map_smul, smul_smul]
  congr 1
  congr 1
  field_simp

theorem coprimeCount_mono (L : ℕ) : Monotone (coprimeCount L) := by
  intro a b hab
  unfold coprimeCount cumulative
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro k hk hka
  dsimp only
  split_ifs <;> norm_num

/-- Pairing j with L-j gives the exact half-count for every even L greater than two. -/
theorem coprimeCount_half (L : ℕ) (hL : 2 < L) (heven : 2 ∣ L) :
    coprimeCount L (L/2) = (Nat.totient L : ℝ)/2 := by
  let t := L/2
  let f : ℕ → ℝ := fun k => if Nat.Coprime k L then 1 else 0
  have ht : t+t = L := by
    have h := Nat.mod_add_div L 2
    rw [Nat.mod_eq_zero_of_dvd heven] at h
    dsimp [t]
    omega
  have ht1 : 1 < t := by omega
  have hf0 : f 0 = 0 := by simp [f, Nat.coprime_iff_gcd_eq_one, show L ≠ 1 by omega]
  have hft : f t = 0 := by
    have hd : t ∣ L := ⟨2, by omega⟩
    simp [f, Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left hd, show t ≠ 1 by omega]
  have hshift : (∑ k ∈ Finset.range t, f (k+1)) = ∑ k ∈ Finset.range t, f k := by
    have h0 := Finset.sum_range_succ f t
    have h1 := Finset.sum_range_succ' f t
    rw [hf0] at h1
    rw [hft] at h0
    linarith
  have href : (∑ k ∈ Finset.range t, f (t+k+1)) = ∑ k ∈ Finset.range t, f k := by
    rw [← Finset.sum_range_reflect (fun k => f (t+k+1)) t]
    apply Finset.sum_congr rfl
    intro k hk
    have hkt := Finset.mem_range.mp hk
    have heq : t+(t-1-k)+1 = L-k := by omega
    rw [heq]
    simp only [f, Nat.coprime_self_sub_left (show k ≤ L by omega)]
  have hs := coprimeCount_self L
  change (∑ k ∈ Finset.range L, f (k+1)) = (Nat.totient L : ℝ) at hs
  rw [← ht, Finset.sum_range_add, ht] at hs
  change (∑ k ∈ Finset.range t, f (k+1)) +
    (∑ k ∈ Finset.range t, f (t+k+1)) = (Nat.totient L : ℝ) at hs
  rw [href, ← hshift] at hs
  change (∑ k ∈ Finset.range t, f (k+1)) = _
  linarith

theorem lift_upper_half (L n : ℕ) (hL : 2 < L) (heven : 2 ∣ L)
    (hn : L / 2 ≤ n) (hnL : n < L) :
    (Nat.totient L : ℝ)/2 ≤ qSequence (lift L) n := by
  rw [lift_sequence_count L n (by omega), Nat.mod_eq_of_lt hnL,
    ← coprimeCount_half L hL heven]
  exact coprimeCount_mono L hn

/-- The first lower bound in (37), before estimating the finite inverse-square sum. -/
theorem lift_norm_sq_ge_half_sum (L : ℕ) (hL : 2 < L) (heven : 2 ∣ L) :
    (Nat.totient L : ℝ)^2 / (4*zetaTwo) *
      (∑ n ∈ Finset.Ico (L/2) L, 1/(n : ℝ)^2) ≤ ‖lift L‖^2 := by
  rw [qNorm_weighted_sq, Finset.mul_sum]
  calc
    _ ≤ ∑ n ∈ Finset.Ico (L/2) L, positiveQWeight n * (qSequence (lift L) n)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnL⟩ := Finset.mem_Ico.mp hn
      have hb := lift_upper_half L n hL heven hn0 hnL
      have hs : ((Nat.totient L : ℝ)/2)^2 ≤ (qSequence (lift L) n)^2 :=
        (sq_le_sq₀ (by positivity) ((by positivity : 0 ≤ (Nat.totient L : ℝ)/2).trans hb)).mpr hb
      have hw := mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg n)
      convert hw using 1
      unfold positiveQWeight
      ring
    _ ≤ _ := (qSequence_square_summable (lift L)).sum_le_tsum _
      (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))

theorem inverse_square_half_sum (L : ℕ) (hL : 2 < L) (heven : 2 ∣ L) :
    1/(2*(L : ℝ)) ≤ ∑ n ∈ Finset.Ico (L/2) L, 1/(n : ℝ)^2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have he : 2*(L/2) = L := Nat.mul_div_cancel' heven
  have hcount : L-L/2 = L/2 := by omega
  have heR : 2*((L/2 : ℕ) : ℝ) = (L : ℝ) := by exact_mod_cast he
  calc
    _ = ∑ _n ∈ Finset.Ico (L/2) L, 1/(L : ℝ)^2 := by
      simp only [Finset.sum_const, Nat.card_Ico, hcount, nsmul_eq_mul]
      field_simp
      nlinarith
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnL⟩ := Finset.mem_Ico.mp hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact one_div_le_one_div_of_le (sq_pos_of_pos hnR)
        ((sq_le_sq₀ hnR.le hLR.le).mpr (by exact_mod_cast hnL.le))

/-- Equation (37), in the complete Q norm. -/
theorem lift_norm_sq_lower (L : ℕ) (hL : 2 < L) (heven : 2 ∣ L) :
    (Nat.totient L : ℝ)^2 / (8*zetaTwo*(L : ℝ)) ≤ ‖lift L‖^2 := by
  have hZ := zetaTwo_pos
  calc
    _ = (Nat.totient L : ℝ)^2 / (4*zetaTwo) * (1/(2*(L : ℝ))) := by ring
    _ ≤ (Nat.totient L : ℝ)^2 / (4*zetaTwo) *
        (∑ n ∈ Finset.Ico (L/2) L, 1/(n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (inverse_square_half_sum L hL heven) (by positivity)
    _ ≤ _ := lift_norm_sq_ge_half_sum L hL heven

/-- Exact prime product responsible for divergence of the source lower bound. -/
theorem totient_ratio_primorial (N : ℕ) :
    (Nat.totient (primorial N) : ℝ)^2 / (primorial N : ℝ) =
      ∏ p ∈ N.primesLE, ((p : ℝ)-1)^2/(p : ℝ) := by
  have hL : (primorial N : ℝ) ≠ 0 := by exact_mod_cast primorial_ne_zero N
  have he := divisorDensity_eq_totient (primorial N) (primorial_ne_zero N)
  rw [divisorDensity_euler _ (squarefree_primorial N), primeFactors_primorial] at he
  calc
    _ = (primorial N : ℝ) * (∏ p ∈ N.primesLE, (1-1/(p : ℝ)))^2 := by
      rw [he]
      field_simp
    _ = ∏ p ∈ N.primesLE, (p : ℝ) * (1-1/(p : ℝ))^2 := by
      rw [primorial_eq_prod_primesLE, Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero
      field_simp

theorem totient_ratio_primorial_lower (N : ℕ) (hN : 2 ≤ N) :
    (1/2 : ℝ) * (4/3 : ℝ)^((N.primesLE.erase 2).card) ≤
      (Nat.totient (primorial N) : ℝ)^2 / (primorial N : ℝ) := by
  have h2 : 2 ∈ N.primesLE := Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩
  rw [totient_ratio_primorial, ← Finset.mul_prod_erase _ _ h2]
  norm_num only [Nat.cast_ofNat, show ((2 : ℝ)-1)^2/(2 : ℝ) = 1/2 by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => by norm_num)
  intro p hp
  obtain ⟨hp2, hpmem⟩ := Finset.mem_erase.mp hp
  have hpge : 3 ≤ p := by have := (Nat.prime_of_mem_primesLE hpmem).two_le; omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hpge
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < p)).mpr
  nlinarith [sq_nonneg ((p : ℝ)-3)]

theorem odd_prime_count_tendsto :
    Tendsto (fun N : ℕ => (N.primesLE.erase 2).card) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [Nat.tendsto_primeCounting.eventually (eventually_ge_atTop (b+1)),
    eventually_ge_atTop (2 : ℕ)] with N hNb hN
  have h2 : 2 ∈ N.primesLE := Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩
  have hc := Finset.card_erase_add_one h2
  rw [Nat.primesLE_card_eq_primeCounting] at hc
  omega

theorem totient_ratio_primorial_tendsto :
    Tendsto (fun N : ℕ => (Nat.totient (primorial N) : ℝ)^2 / (primorial N : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop (eventually_ge_atTop 2 |>.mono fun N hN =>
    totient_ratio_primorial_lower N hN)
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4/3)).comp
    odd_prime_count_tendsto |>.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2)

theorem primorial_lift_norm_sq_tendsto :
    Tendsto (fun N : ℕ => ‖lift (primorial N)‖^2) atTop atTop := by
  have hZ := zetaTwo_pos
  have ht := totient_ratio_primorial_tendsto.const_mul_atTop (by positivity : 0 < 1/(8*zetaTwo))
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  have h3 : 2 < primorial N := by
    have hh : 3 ∣ primorial N := Nat.prime_three.dvd_primorial_iff.mpr hN
    exact (by omega : 2 < 3).trans_le (Nat.le_of_dvd (primorial_pos N) hh)
  have he : 2 ∣ primorial N := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  calc
    (1/(8*zetaTwo)) * ((Nat.totient (primorial N) : ℝ)^2 / (primorial N : ℝ)) =
        (Nat.totient (primorial N) : ℝ)^2 / (8*zetaTwo*(primorial N : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := lift_norm_sq_lower (primorial N) h3 he


/-- The primorial cutoff is cofinal even after removing its last site. -/
theorem primorial_pred_tendsto :
    Tendsto (fun N : ℕ => primorial N - 1) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_ge_atTop (M+1)] with N hN
  have h : N ≤ primorial N := le_primorial_self
  omega

theorem tailVector_one_eq : QReciprocalFullDensity.tailVector 1 = D qOne := by
  apply qSequence_injective
  funext n
  rw [QReciprocalFullDensity.tailVector_sequence, qSequence_D, qSequence_qOne]
  by_cases hn : n = 0
  · simp [hn, QReciprocalFullDensity.tailSequence, qOneSequence]
  · simp [QReciprocalFullDensity.tailSequence, qOneSequence, hn, show 1 ≤ n by omega]

/-- The diagonal sieve does converge to the correctly damped constant D1. -/
theorem primorial_damped_lift_tendsto :
    Tendsto (fun N : ℕ => D (lift (primorial N))) atTop (𝓝 (D qOne)) := by
  have h1 := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tailMass_tendsto qModel).comp primorial_pred_tendsto)
  have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp (tailMass_tendsto qModel)
  have ht : Tendsto (fun N : ℕ =>
      Real.sqrt (tailMass qModel (primorial N - 1)) + Real.sqrt (tailMass qModel N))
      atTop (𝓝 0) := by simpa only [Function.comp_def, Real.sqrt_zero, add_zero] using h1.add h2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) _ ht
  intro N
  have h := finiteApprox_error qModel (primorial N) N 1 (primorial N)
    (primorial_ne_zero N) (by norm_num) (primorial_pos N) (primorial_covers N)
  simpa only [← damped_lift_eq _ (primorial_pos N), tailVector_one_eq,
    Nat.cast_one, div_one, one_mul, qModel, ContinuousLinearMap.id_apply] using h

theorem primorial_lift_p_norm_sq_tendsto :
    Tendsto (fun N : ℕ => ‖ZetaTwoParetoTransfer.toPareto (lift (primorial N))‖^2)
      atTop atTop := by
  have hZ := zetaTwo_pos
  have ht := primorial_lift_norm_sq_tendsto.const_mul_atTop (by positivity : 0 < zetaTwo/2)
  apply tendsto_atTop_mono _ ht
  intro N
  have h := ZetaTwoParetoTransfer.zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (lift (primorial N))
  nlinarith

private theorem norm_tendsto_of_square {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) (h : Tendsto (fun N => ‖f N‖ ^ 2) atTop atTop) :
    Tendsto (fun N => ‖f N‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [h.eventually (eventually_ge_atTop ((max b 0)^2))] with N hN
  exact (le_max_left b 0).trans
    ((sq_le_sq₀ (le_max_right b 0) (norm_nonneg _)).mp hN)

/-- Equation (38): complete source norms diverge in both measures. -/
theorem primorial_lift_norms_tendsto :
    Tendsto (fun N : ℕ => ‖lift (primorial N)‖) atTop atTop ∧
      Tendsto (fun N : ℕ => ‖ZetaTwoParetoTransfer.toPareto (lift (primorial N))‖)
        atTop atTop :=
  ⟨norm_tendsto_of_square _ primorial_lift_norm_sq_tendsto,
    norm_tendsto_of_square _ primorial_lift_p_norm_sq_tendsto⟩

#print axioms primorial_damped_lift_tendsto
#print axioms primorial_lift_norms_tendsto
#print axioms lift_sequence_count
#print axioms lift_norm_sq_lower
#print axioms primorial_lift_norm_sq_tendsto
end RiemannResearch.RH.PrimorialSieveLift
