import RiemannResearch.RH.QReciprocalFullDensity
import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoDilation
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Module

/-!
# Complete two-measure error bounds for finite residue sieves

Source: user-provided `PQ_Augmented_Density_and_RH_Agenda.pdf`,
14 November 2026, equations (8), (12), (16), (17), and Section 7.6.
The statements use the complete infinite weighted norm. The cutoff conductor
may be any positive integer covering the indicated head; primorials qualify.
The finite approximants contain no constant vector in their defining formula.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QuantitativeSieve
open ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric QDensityMetric
open QReciprocalFullDensity QPrimeSieve QMobiusPrimePacket ZetaTwoParetoTransfer

/-- A physical-sequence preserving norm realization; instantiated below for P and Q. -/
structure WeightedModel (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  encode : QHilbert →L[ℝ] H
  weight : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ weight n
  summable : Summable weight
  square_summable : ∀ f, Summable (fun n => weight n * (qSequence f n)^2)
  norm_sq : ∀ f, ‖encode f‖^2 = ∑' n, weight n * (qSequence f n)^2

def qModel : WeightedModel QHilbert where
  encode := ContinuousLinearMap.id ℝ QHilbert
  weight := positiveQWeight
  nonneg := positiveQWeight_nonneg
  summable := positiveQWeight_summable
  square_summable := qSequence_square_summable
  norm_sq := qNorm_weighted_sq

def pModel : WeightedModel Pareto.ThresholdHilbert where
  encode := toParetoCLM
  weight := Pareto.positiveWeight
  nonneg := Pareto.positiveWeight_nonneg
  summable := Pareto.positiveWeight_summable
  square_summable := qSequence_pareto_square_summable
  norm_sq f := by rw [toParetoCLM_apply, Pareto.hilbert_norm_weighted_sq, toPareto_sequence]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def tailMass (A : WeightedModel H) (M : ℕ) : ℝ :=
  ∑' n, if M < n then A.weight n else 0

theorem tail_summable (A : WeightedModel H) (M : ℕ) :
    Summable (fun n => if M < n then A.weight n else 0) := by
  apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [A.nonneg])
    (fun n => by split_ifs <;> simp [A.nonneg]) A.summable

theorem tailMass_nonneg (A : WeightedModel H) (M : ℕ) : 0 ≤ tailMass A M :=
  tsum_nonneg (fun n => by split_ifs <;> simp [A.nonneg])


/-- Summability of the actual weights makes the complete tail mass vanish. -/
theorem tailMass_tendsto (A : WeightedModel H) :
    Tendsto (tailMass A) atTop (𝓝 0) := by
  have hp (n : ℕ) : Tendsto (fun M : ℕ => if M < n then A.weight n else 0)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with M hM
    simp [not_lt.mpr hM]
  have hb : ∀ᶠ M : ℕ in atTop, ∀ n, ‖if M < n then A.weight n else 0‖ ≤ A.weight n := by
    apply Eventually.of_forall
    intro M n
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (A.nonneg n), A.nonneg n]
  change Tendsto (fun M : ℕ => ∑' n : ℕ, if M < n then A.weight n else (0 : ℝ)) atTop (𝓝 0)
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ => (0 : ℝ)) A.summable hp hb

/-- Exact head support and a physical bound control the whole norm, including its tail. -/
theorem norm_sq_le_tail (A : WeightedModel H) (f : QHilbert) (M : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hhead : ∀ n, n ≤ M → qSequence f n = 0)
    (hb : ∀ n, |qSequence f n| ≤ C) :
    ‖A.encode f‖^2 ≤ C^2 * tailMass A M := by
  rw [A.norm_sq, tailMass, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (A.square_summable f) ((tail_summable A M).mul_left _)
  intro n
  by_cases hn : M < n
  · rw [if_pos hn]
    have hs : (qSequence f n)^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb n)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (A.nonneg n)
  · simp [hn, hhead n (by omega)]

theorem norm_le_sqrt_tail (A : WeightedModel H) (f : QHilbert) (M : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hhead : ∀ n, n ≤ M → qSequence f n = 0)
    (hb : ∀ n, |qSequence f n| ≤ C) :
    ‖A.encode f‖ ≤ C * Real.sqrt (tailMass A M) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt (tailMass_nonneg A M)] using
    norm_sq_le_tail A f M C hC hhead hb

theorem approximation_head (K n : ℕ) (hK : 0 < K) (hn : n ≤ K - 1) :
    qSequence (approximation K - qOne) n = 0 := by
  rw [approximation_error_sequence K n hK, Nat.mod_eq_of_lt (by omega)]
  by_cases hn0 : n = 0
  · simp [hn0, qOneSequence]
  · simp [qOneSequence, hn0, Nat.cast_ne_zero.mpr hn0]

/-- Equation (8), in either of the concrete realizations `qModel` and `pModel`. -/
theorem approximation_error_sq (A : WeightedModel H) (K : ℕ) (hK : 0 < K) :
    ‖A.encode (approximation K - qOne)‖^2 ≤ tailMass A (K-1) := by
  simpa only [one_pow, one_mul] using
    norm_sq_le_tail A _ (K-1) 1 zero_le_one
      (fun n hn => approximation_head K n hK hn)
      (fun n => approximation_error_abs_le_one K n hK)

theorem approximation_error (A : WeightedModel H) (K : ℕ) (hK : 0 < K) :
    ‖A.encode (approximation K - qOne)‖ ≤ Real.sqrt (tailMass A (K-1)) := by
  simpa only [one_mul] using
    norm_le_sqrt_tail A _ (K-1) 1 zero_le_one
      (fun n hn => approximation_head K n hK hn)
      (fun n => approximation_error_abs_le_one K n hK)

def sieve (L m : ℕ) : QHilbert :=
  ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) • floorAtom (m*d)

theorem sieve_sequence (L m : ℕ) (hL : L ≠ 0) (hm : 0 < m) (n : ℕ) :
    qSequence (sieve L m) n = coprimeCount L (n/m) / (n : ℝ) := by
  calc
    _ = ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((n/m/d : ℕ) : ℝ) / (n : ℝ)) := by
      change qSequenceLinear (∑ d ∈ L.divisors, _ • _) n = _
      rw [map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro d hd
      change (ArithmeticFunction.moebius d : ℝ) * qSequence (floorAtom (m*d)) n = _
      rw [floorAtom_sequence _ (Nat.mul_pos hm (Nat.pos_of_mem_divisors hd)),
        Nat.div_div_eq_div_mul]
    _ = (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((n/m/d : ℕ) : ℝ)) / (n : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [finite_floor_sieve _ _ hL]

theorem sieve_bounds (L m : ℕ) (hL : L ≠ 0) (hm : 0 < m) (n : ℕ) :
    0 ≤ qSequence (sieve L m) n ∧ qSequence (sieve L m) n ≤ 1/(m : ℝ) := by
  rw [sieve_sequence L m hL hm]
  have hc := coprimeCount_bounds L (n/m)
  constructor
  · exact div_nonneg hc.1 (Nat.cast_nonneg n)
  · by_cases hn : n = 0
    · simp [hn]
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    apply (div_le_iff₀ hnR).mpr
    have hd : ((n/m : ℕ) : ℝ) * (m : ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n m
    have hb := hc.2.trans ((le_div_iff₀ hmR).mpr hd)
    simpa only [one_div_mul_eq_div] using hb

theorem reciprocal_tail_bounds (m : ℕ) (hm : 0 < m) (n : ℕ) :
    0 ≤ qSequence (tailVector m) n ∧ qSequence (tailVector m) n ≤ 1/(m : ℝ) := by
  rw [tailVector_sequence, tailSequence]
  split_ifs with h
  · exact ⟨by positivity, one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h)⟩
  · exact ⟨le_rfl, by positivity⟩

def Covers (L N : ℕ) : Prop := ∀ j, 2 ≤ j → j ≤ N → ¬ Nat.Coprime j L

theorem primorial_covers (N : ℕ) : Covers (primorial N) N := by
  intro j hj hjN hc
  obtain ⟨p, hp, hpj⟩ := Nat.exists_prime_and_dvd (by omega : j ≠ 1)
  have hpN := (Nat.le_of_dvd (by omega : 0 < j) hpj).trans hjN
  have hpg := Nat.dvd_gcd hpj (hp.dvd_primorial_iff.mpr hpN)
  rw [hc.gcd_eq_one] at hpg
  exact hp.not_dvd_one hpg

theorem sieve_head (L N m : ℕ) (hL : L ≠ 0) (hm : 0 < m)
    (hc : Covers L N) (n : ℕ) (hn : n ≤ m * N) :
    qSequence (sieve L m) n = qSequence (tailVector m) n := by
  rw [sieve_sequence L m hL hm, tailVector_sequence]
  by_cases hmn : m ≤ n
  · have hr : 0 < n/m := Nat.div_pos hmn hm
    have hrN : n/m ≤ N := by
      have hd := Nat.div_mul_le_self n m
      by_contra h
      have : N+1 ≤ n/m := by omega
      nlinarith
    rw [coprimeCount_head L N (n/m) hr hrN hc]
    simp [tailSequence, hmn]
  · simp [Nat.div_eq_of_lt (show n < m by omega), coprimeCount,
      ArithmeticCumulative.cumulative, tailSequence, hmn]

theorem sieve_error_abs (L m : ℕ) (hL : L ≠ 0) (hm : 0 < m) (n : ℕ) :
    |qSequence (sieve L m - tailVector m) n| ≤ 1/(m : ℝ) := by
  have hs := sieve_bounds L m hL hm n
  have ht := reciprocal_tail_bounds m hm n
  change |qSequenceLinear (_ - _) n| ≤ _
  rw [map_sub]
  change |qSequence (sieve L m) n - qSequence (tailVector m) n| ≤ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Equation (12), including its complete weight tail. -/
theorem sieve_error_sq (A : WeightedModel H) (L N m : ℕ)
    (hL : L ≠ 0) (hm : 0 < m) (hc : Covers L N) :
    ‖A.encode (sieve L m - tailVector m)‖^2 ≤ (1/(m : ℝ))^2 * tailMass A (m*N) := by
  apply norm_sq_le_tail A _ _ _ (by positivity) _ (sieve_error_abs L m hL hm)
  intro n hn
  change qSequenceLinear (_ - _) n = 0
  rw [map_sub]
  change qSequence (sieve L m) n - qSequence (tailVector m) n = 0
  rw [sieve_head L N m hL hm hc n hn, sub_self]

theorem sieve_error (A : WeightedModel H) (L N m : ℕ)
    (hL : L ≠ 0) (hm : 0 < m) (hc : Covers L N) :
    ‖A.encode (sieve L m - tailVector m)‖ ≤ (1/(m : ℝ)) * Real.sqrt (tailMass A (m*N)) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt (tailMass_nonneg A _)] using
    sieve_error_sq A L N m hL hm hc

def coefficient (L m : ℕ) : ℝ := divisorDensity L / (m : ℝ)

theorem coefficient_bounds (L m : ℕ) (hL : L ≠ 0) (hm : 0 < m) :
    0 ≤ coefficient L m ∧ coefficient L m ≤ 1/(m : ℝ) := by
  rw [coefficient, divisorDensity_eq_totient L hL]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have ht : (Nat.totient L : ℝ) ≤ L := by exact_mod_cast Nat.totient_le L
  exact ⟨by positivity, div_le_div_of_nonneg_right ((div_le_one hLpos).mpr ht) (by positivity)⟩

def finiteApprox (L m K : ℕ) : QHilbert :=
  coefficient L m • approximation K -
    ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) • D (qResidue (m*d))

theorem sieve_eq (L m : ℕ) :
    sieve L m = coefficient L m • qOne -
      ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) • D (qResidue (m*d)) := by
  simp only [sieve, floorAtom, smul_sub, smul_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul]
  congr 2
  simp only [coefficient, divisorDensity, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  push_cast
  ring

/-- Exact signed difference before the triangle inequality. -/
theorem finiteApprox_sub_sieve (L m K : ℕ) :
    finiteApprox L m K - sieve L m = coefficient L m • (approximation K - qOne) := by
  rw [finiteApprox, sieve_eq]
  module

/-- Equation (16): finite conductors, with both independent tails retained. -/
theorem finiteApprox_error (A : WeightedModel H) (L N m K : ℕ)
    (hL : L ≠ 0) (hm : 0 < m) (hK : 0 < K) (hc : Covers L N) :
    ‖A.encode (finiteApprox L m K - tailVector m)‖ ≤
      (1/(m : ℝ)) * (Real.sqrt (tailMass A (K-1)) + Real.sqrt (tailMass A (m*N))) := by
  have he : finiteApprox L m K - tailVector m =
      coefficient L m • (approximation K - qOne) + (sieve L m - tailVector m) := by
    rw [← finiteApprox_sub_sieve]
    module
  rw [he, map_add, map_smul]
  have hcB := coefficient_bounds L m hL hm
  calc
    _ ≤ ‖coefficient L m • A.encode (approximation K - qOne)‖ +
        ‖A.encode (sieve L m - tailVector m)‖ := norm_add_le _ _
    _ ≤ (1/(m : ℝ)) * Real.sqrt (tailMass A (K-1)) +
        (1/(m : ℝ)) * Real.sqrt (tailMass A (m*N)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcB.1]
      exact add_le_add
        (mul_le_mul hcB.2 (approximation_error A K hK) (norm_nonneg _) (by positivity))
        (sieve_error A L N m hL hm hc)
    _ = _ := by ring

def pointApprox (L m K : ℕ) : QHilbert :=
  (m : ℝ) • (finiteApprox L m K - finiteApprox L (m+1) K)

/-- Equation (17), with `qPoint k` the indicator of the physical site `k+1`. -/
theorem pointApprox_error (A : WeightedModel H) (L N k K : ℕ)
    (hL : L ≠ 0) (hK : 0 < K) (hc : Covers L N) :
    ‖A.encode (pointApprox L (k+1) K - qPoint k)‖ ≤
      (1 + ((k+1 : ℕ) : ℝ)/((k+2 : ℕ) : ℝ)) * Real.sqrt (tailMass A (K-1)) +
        Real.sqrt (tailMass A ((k+1)*N)) +
        (((k+1 : ℕ) : ℝ)/((k+2 : ℕ) : ℝ)) * Real.sqrt (tailMass A ((k+2)*N)) := by
  have he : pointApprox L (k+1) K - qPoint k =
      ((k+1 : ℕ) : ℝ) • ((finiteApprox L (k+1) K - tailVector (k+1)) -
        (finiteApprox L (k+2) K - tailVector (k+2))) := by
    rw [pointApprox, qPoint_eq_tail_difference]
    module
  rw [he, map_smul, map_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((k+1 : ℕ) : ℝ) *
        (‖A.encode (finiteApprox L (k+1) K - tailVector (k+1))‖ +
          ‖A.encode (finiteApprox L (k+2) K - tailVector (k+2))‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ ((k+1 : ℕ) : ℝ) *
        ((1/((k+1 : ℕ) : ℝ)) * (Real.sqrt (tailMass A (K-1)) + Real.sqrt (tailMass A ((k+1)*N))) +
         (1/((k+2 : ℕ) : ℝ)) * (Real.sqrt (tailMass A (K-1)) + Real.sqrt (tailMass A ((k+2)*N)))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (finiteApprox_error A L N (k+1) K hL (by omega) hK hc)
        (finiteApprox_error A L N (k+2) K hL (by omega) hK hc)) (by positivity)
    _ = _ := by field_simp; ring


/-- Every displayed finite constructor is in the genuine finite augmented span. -/
theorem finiteApprox_mem_augmentedSpan (L m K : ℕ) (hm : 0 < m) (hK : 2 ≤ K) :
    finiteApprox L m K ∈ augmentedSpan {k : ℕ | 2 ≤ k} := by
  let S := augmentedSpan {k : ℕ | 2 ≤ k}
  have hD (k : ℕ) (hk : 0 < k) : D (qResidue k) ∈ S := by
    by_cases hk1 : k = 1
    · simp [hk1]
    have hk2 : 2 ≤ k := by omega
    have hg : qResidue k ∈ S := Submodule.subset_span ⟨k, hk2, Or.inl rfl⟩
    have hB : B (qResidue k) ∈ S := Submodule.subset_span ⟨k, hk2, Or.inr rfl⟩
    rw [QDensityMetricInverse.D_eq_density]
    exact S.sub_mem (S.smul_mem _ hB) hg
  apply S.sub_mem (S.smul_mem _ (approximation_mem_augmentedSpan _ K hK))
  apply S.sum_mem
  intro d hd
  exact S.smul_mem _ (hD (m*d) (Nat.mul_pos hm (Nat.pos_of_mem_divisors hd)))

#print axioms finiteApprox_error
#print axioms pointApprox_error
end RiemannResearch.RH.QuantitativeSieve
