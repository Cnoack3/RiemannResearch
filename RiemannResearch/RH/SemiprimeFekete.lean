import RiemannResearch.NumberTheory.FeketePowerSlope
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.MixedPacketDensityTests
import RiemannResearch.RH.MixedReciprocalDensity
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ParetoDensityDilation
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Subadditive
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fekete's lemma for signed sums over blocks of consecutive prime pairs

The upper increment of the cumulative signed pairing is subadditive in the
block length. The complete Pareto error bound is uniform over the starting
prime, so the infimum in Fekete's lemma is the negative residual energy.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete

open CoefficientStabilization MixedPacketDensity CenteredMeanSnake
open RiemannResearch.NumberTheory RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ParetoDensityDilation RiemannResearch.RH.QDensityMetricInverse

local notation "nthPrime" => Nat.nth Nat.Prime

/-- The positive density normalization preserves the sign of each original pairing. -/
def signedPairing (j : ℕ) : ℝ :=
  zetaTwo * inner ℝ limitResidual (densityP (consecutivePacket j))

/-- Cumulative signed pairings up to but excluding the specified index. -/
def cumulative (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, signedPairing j

/-- Upper total over all starting points for a block of length n. -/
def upperBlock (n : ℕ) : ℝ := upperIncrement cumulative n

/-- Full-norm reciprocal error bound for the pair starting at index j. -/
def errorRate (j : ℕ) : ℝ := Real.sqrt (4 / (nthPrime j : ℝ))

private theorem prime_mono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private theorem errorRate_antitone : Antitone errorRate := by
  intro i j hij
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (by norm_num)
    (by exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i).pos)
    (by exact_mod_cast prime_mono.monotone hij)

private theorem errorRate_tendsto : Tendsto errorRate atTop (𝓝 0) := by
  have hd : Tendsto (fun j => (nthPrime j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp prime_mono.tendsto_atTop
  have ht : Tendsto (fun j => (4 : ℝ) / (nthPrime j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  change Tendsto (fun j : ℕ => Real.sqrt (4 / (nthPrime j : ℝ))) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp ht)

theorem signedPairing_error_le (j : ℕ) :
    |signedPairing j + ‖limitResidual‖ ^ 2| ≤ ‖limitResidual‖ * errorRate j := by
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j
  have hq := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1)
  have hlt := prime_mono (Nat.lt_succ_self j)
  have hh : ‖DP (consecutivePacket j) + hilbertOne‖ ^ 2 ≤ 4 / (nthPrime j : ℝ) := by
    simpa only [consecutivePacket, min_eq_left hlt.le] using
      semiprime_reciprocal_error_sq_le hp hq hlt.ne
  have he : ‖DP (consecutivePacket j) + hilbertOne‖ ≤ errorRate j := by
    simpa only [Real.sqrt_sq (norm_nonneg _), errorRate] using Real.sqrt_le_sqrt hh
  have hid : signedPairing j + ‖limitResidual‖ ^ 2 =
      inner ℝ limitResidual (DP (consecutivePacket j) + hilbertOne) := by
    rw [add_comm]
    exact residual_pairing_identity hp hq hlt.ne
  rw [hid]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))

theorem cumulative_increment (k n : ℕ) :
    cumulative (k + n) - cumulative k = ∑ j ∈ Finset.range n, signedPairing (k + j) := by
  simp only [cumulative, Finset.sum_range_add, add_sub_cancel_left]

/-- The start-independent bound controls every finite block before taking its supremum. -/
theorem block_error_le (k n : ℕ) :
    |cumulative (k + n) - cumulative k + (n : ℝ) * ‖limitResidual‖ ^ 2| ≤
      ‖limitResidual‖ * ∑ j ∈ Finset.range n, errorRate j := by
  rw [cumulative_increment, Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.range n, signedPairing (k + j)) + (n : ℝ) * ‖limitResidual‖ ^ 2 =
      ∑ j ∈ Finset.range n, (signedPairing (k + j) + ‖limitResidual‖ ^ 2) := by
    simp [Finset.sum_add_distrib, nsmul_eq_mul]
  rw [hsum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun j _ => (signedPairing_error_le (k + j)).trans
    (mul_le_mul_of_nonneg_left (errorRate_antitone (Nat.le_add_left j k)) (norm_nonneg _))

private theorem increment_bdd (n : ℕ) :
    BddAbove (range fun k : ℕ => cumulative (k + n) - cumulative k) := by
  refine ⟨‖limitResidual‖ * (∑ j ∈ Finset.range n, errorRate j) -
    (n : ℝ) * ‖limitResidual‖ ^ 2, ?_⟩
  rintro _ ⟨k, rfl⟩
  linarith [(abs_le.mp (block_error_le k n)).2]

theorem upperBlock_subadditive : Subadditive upperBlock :=
  upperIncrement_subadditive cumulative increment_bdd

theorem upperBlock_error_le (n : ℕ) :
    |upperBlock n + (n : ℝ) * ‖limitResidual‖ ^ 2| ≤
      ‖limitResidual‖ * ∑ j ∈ Finset.range n, errorRate j := by
  have hle : cumulative (0 + n) - cumulative 0 ≤ upperBlock n :=
    le_csSup (increment_bdd n) (mem_range_self 0)
  have hup : upperBlock n ≤ ‖limitResidual‖ * (∑ j ∈ Finset.range n, errorRate j) -
      (n : ℝ) * ‖limitResidual‖ ^ 2 := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨k, rfl⟩
    linarith [(abs_le.mp (block_error_le k n)).2]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp (block_error_le 0 n)).1], by linarith⟩

private theorem upperBlock_div_tendsto :
    Tendsto (fun n : ℕ => upperBlock n / n) atTop (𝓝 (-‖limitResidual‖ ^ 2)) := by
  have hc : Tendsto (fun n : ℕ => (‖limitResidual‖ * ∑ j ∈ Finset.range n, errorRate j) / n)
      atTop (𝓝 0) := by
    have h := errorRate_tendsto.cesaro_smul.const_mul ‖limitResidual‖
    simpa only [smul_eq_mul, mul_zero, zero_mul, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _ hc
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hid : upperBlock n / (n : ℝ) + ‖limitResidual‖ ^ 2 =
      (upperBlock n + (n : ℝ) * ‖limitResidual‖ ^ 2) / n := by
    field_simp [hnR.ne']
  rw [Real.norm_eq_abs, sub_neg_eq_add, hid, abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right (upperBlock_error_le n) hnR.le

private theorem normalized_lower_bdd :
    BddBelow (range fun n : ℕ => upperBlock n / n) := by
  refine ⟨-‖limitResidual‖ ^ 2 - ‖limitResidual‖ * errorRate 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero]
    have h := Real.sqrt_nonneg (4 / (nthPrime 0 : ℝ))
    change -‖limitResidual‖ ^ 2 - ‖limitResidual‖ * Real.sqrt (4 / (nthPrime 0 : ℝ)) ≤ 0
    nlinarith [mul_nonneg (norm_nonneg limitResidual) h, sq_nonneg ‖limitResidual‖]
  · apply (le_div_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).2
    have hsum : (∑ j ∈ Finset.range n, errorRate j) ≤ (n : ℝ) * errorRate 0 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range n, errorRate 0 :=
          Finset.sum_le_sum fun j _ => errorRate_antitone (Nat.zero_le j)
        _ = _ := by simp [nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left hsum (norm_nonneg limitResidual)
    nlinarith [(abs_le.mp (upperBlock_error_le n)).1]

/-- Fekete's infimum is exactly the negative squared Pareto residual norm. -/
theorem upperBlock_fekete_eq :
    sInf ((fun n : ℕ => upperBlock n / n) '' Ici 1) = -‖limitResidual‖ ^ 2 := by
  have h := upperBlock_subadditive.tendsto_lim normalized_lower_bdd
  rw [Subadditive.lim] at h
  exact tendsto_nhds_unique h upperBlock_div_tendsto

private theorem rh_iff_residual_zero :
    RiemannHypothesis ↔ limitResidual = 0 :=
  (riemannHypothesis_iff_naturalApproximation.trans
    BaezDuarte.naturalApproximation_iff_one_mem).trans
    (limitResidual_zero_iff_energy_zero.trans limitEnergy_zero_iff_mem).symm

/-- One nonnegative block yields a finite certificate involving the primes in its length bound. -/
theorem energy_le_of_nonnegative_block {k n : ℕ} (hn : 0 < n)
    (hs : 0 ≤ cumulative (k + n) - cumulative k) :
    ‖limitResidual‖ ^ 2 ≤ ((∑ j ∈ Finset.range n, errorRate j) / n) ^ 2 := by
  have hb := (abs_le.mp (block_error_le k n)).2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ j ∈ Finset.range n, errorRate j :=
    Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  have hh : ‖limitResidual‖ ≤ (∑ j ∈ Finset.range n, errorRate j) / n := by
    apply (le_div_iff₀ hnR).2
    by_cases hd : ‖limitResidual‖ = 0
    · simpa only [hd, zero_mul] using hsum
    · have hdpos := lt_of_le_of_ne (norm_nonneg limitResidual) (Ne.symm hd)
      apply (le_of_mul_le_mul_left _ hdpos)
      nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hsum hnR.le)).mpr hh

/-- Nonnegative signed block sums at arbitrarily large lengths characterize RH. -/
theorem riemannHypothesis_iff_frequently_nonnegative_block :
    RiemannHypothesis ↔ ∃ᶠ n : ℕ in atTop, ∃ k : ℕ, 0 ≤ cumulative (k + n) - cumulative k := by
  rw [rh_iff_residual_zero]
  constructor
  · intro hd
    apply Filter.Eventually.frequently
    exact Eventually.of_forall (fun _ => ⟨0, by simp [cumulative, signedPairing, hd]⟩)
  · intro hf
    by_contra hd
    have hneg : -‖limitResidual‖ ^ 2 < 0 := neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hd))
    have ht := upperBlock_div_tendsto.eventually (Iio_mem_nhds hneg)
    obtain ⟨n, ⟨k, hk⟩, hbad⟩ := (hf.and_eventually ht).exists
    have hle : cumulative (k + n) - cumulative k ≤ upperBlock n :=
      le_csSup (increment_bdd n) (mem_range_self k)
    exact (not_lt_of_ge (div_nonneg (hk.trans hle) (Nat.cast_nonneg n))) hbad

open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoParetoTransfer
open RiemannResearch.RH.QParetoEquivalence RiemannResearch.RH.QDensityMetric

/-- The residual paired with the reciprocal raw residue at conductor a. -/
def reciprocalResiduePairing (a : ℕ) : ℝ :=
  inner ℝ limitResidual (toPareto (approximation a))

theorem reciprocalResiduePairing_eq_density (n : ℕ) :
    reciprocalResiduePairing (n + 2) =
      zetaTwo * inner ℝ limitResidual (densityP (toPareto (MixedReciprocalDensity.raw n))) := by
  let x := toPareto (MixedReciprocalDensity.raw n)
  have hx : x ∈ closedSpace :=
    (MixedReciprocalDensity.legal_iff _).mp (MixedReciprocalDensity.raw_legal n)
  have hz : inner ℝ limitResidual x = 0 :=
    (real_inner_comm _ _).trans (limitResidual_mem_orthogonal x hx)
  have hD : approximation (n + 2) = QReciprocalMetric.D (MixedReciprocalDensity.raw n) := by
    simp only [approximation, MixedReciprocalDensity.raw, map_smul]
  have hB : zetaTwo • densityP x = x + DP x := by
    change zetaTwo • ((1 / zetaTwo) • (x + DP x)) = _
    simp only [smul_smul, one_div, mul_inv_cancel₀ zetaTwo_pos.ne', one_smul]
  have h := congrArg (fun y => inner ℝ limitResidual y) hB
  change inner ℝ limitResidual (zetaTwo • densityP x) = inner ℝ limitResidual (x + DP x) at h
  rw [real_inner_smul_right, inner_add_right, hz, zero_add] at h
  rw [reciprocalResiduePairing, hD, ← DP_toPareto]
  exact h.symm

/-- The scalar intercept is the complete residual energy. -/
theorem reciprocalResiduePairing_tendsto :
    Tendsto reciprocalResiduePairing atTop (𝓝 (‖limitResidual‖ ^ 2)) := by
  have hv := (tendsto_toPareto_iff approximation qOne).mpr approximation_tendsto
  rw [toPareto_qOne] at hv
  have h := ((innerSL ℝ limitResidual).continuous.tendsto hilbertOne).comp hv
  change Tendsto reciprocalResiduePairing atTop (𝓝 (inner ℝ limitResidual hilbertOne)) at h
  rwa [limitResidual_mean_and_screened_norm.1] at h

theorem reciprocalResiduePairing_pow_tendsto {a : ℕ} (ha : 1 < a) :
    Tendsto (fun k : ℕ => reciprocalResiduePairing (a ^ k)) atTop (𝓝 (‖limitResidual‖ ^ 2)) :=
  reciprocalResiduePairing_tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt ha)

/-- Dividing by the exponent erases the intercept at every base. -/
theorem reciprocalResiduePairing_div_exponent_tendsto_zero {a : ℕ} (ha : 1 < a) :
    Tendsto (fun k : ℕ => reciprocalResiduePairing (a ^ k) / (k : ℝ)) atTop (𝓝 0) :=
  (reciprocalResiduePairing_pow_tendsto ha).div_atTop tendsto_natCast_atTop_atTop

/-- On all sufficiently large bases the actual exponent sequence is subadditive.
Its Fekete power rate is zero even though its unnormalized limit is the residual energy. -/
theorem eventually_power_subadditive_zero_rate :
    ∀ᶠ a : ℕ in atTop, Subadditive (fun k : ℕ => reciprocalResiduePairing (a ^ k)) ∧
      powerRate reciprocalResiduePairing a = 0 := by
  have hone : reciprocalResiduePairing 1 = 0 := by
    have hz : approximation 1 = 0 := by simp [approximation, qResidue_one]
    change inner ℝ limitResidual (paretoEquiv (approximation 1)) = 0
    rw [hz, map_zero, inner_zero_right]
  have hgood : ∀ᶠ a : ℕ in atTop,
      Subadditive (fun k : ℕ => reciprocalResiduePairing (a ^ k)) ∧
      ∀ k : ℕ, 0 ≤ reciprocalResiduePairing (a ^ k) := by
    by_cases hz : limitResidual = 0
    · exact Eventually.of_forall fun a =>
        ⟨fun m n => by simp [reciprocalResiduePairing, hz],
          fun k => by simp [reciprocalResiduePairing, hz]⟩
    · let E := ‖limitResidual‖ ^ 2
      have hpos : 0 < E := sq_pos_of_pos (norm_pos_iff.mpr hz)
      have htail : ∀ᶠ b : ℕ in atTop, reciprocalResiduePairing b ∈ Ioo (3 * E / 4) (5 * E / 4) :=
        reciprocalResiduePairing_tendsto.eventually
          (Ioo_mem_nhds (by change 3 * E / 4 < E; linarith) (by change E < 5 * E / 4; linarith))
      obtain ⟨A, hA⟩ := eventually_atTop.1 htail
      filter_upwards [eventually_ge_atTop A] with a ha
      have ht (k : ℕ) (hk : k ≠ 0) := hA (a ^ k) (ha.trans (Nat.le_self_pow hk a))
      constructor
      · intro m n
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp [hone]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [hone]
        have hmn := (ht (m + n) (by omega)).2
        linarith [(ht m hm.ne').1, (ht n hn.ne').1]
      · intro k
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [hone]
        · linarith [(ht k hk.ne').1]
  filter_upwards [hgood, eventually_gt_atTop (1 : ℕ)] with a ha ha1
  have hb : BddBelow (range fun k : ℕ => reciprocalResiduePairing (a ^ k) / k) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact div_nonneg (ha.2 k) (Nat.cast_nonneg _)
  exact ⟨ha.1, tendsto_nhds_unique (tendsto_powerRate ha.1 hb)
    (reciprocalResiduePairing_div_exponent_tendsto_zero ha1)⟩

/-- The signed difference in the superadditivity test has limit minus the energy. -/
theorem reciprocalResiduePairing_doubling_tendsto {a : ℕ} (ha : 1 < a) :
    Tendsto (fun k : ℕ => reciprocalResiduePairing (a ^ (k + k)) -
        2 * reciprocalResiduePairing (a ^ k)) atTop (𝓝 (-(‖limitResidual‖ ^ 2))) := by
  have hd : Tendsto (fun k : ℕ => k + k) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with k hk
    omega
  have hp := reciprocalResiduePairing_pow_tendsto ha
  have hlim : ‖limitResidual‖ ^ 2 - (‖limitResidual‖ ^ 2 + ‖limitResidual‖ ^ 2) =
      -(‖limitResidual‖ ^ 2) := by ring
  simpa only [Function.comp_def, two_mul, hlim] using (hp.comp hd).sub (hp.add hp)

/-- One fixed base suffices. The weak doubling inequalities are the open input. -/
theorem riemannHypothesis_iff_frequently_residue_doubling {a : ℕ} (ha : 1 < a) :
    RiemannHypothesis ↔ ∃ᶠ k : ℕ in atTop,
      2 * reciprocalResiduePairing (a ^ k) ≤ reciprocalResiduePairing (a ^ (k + k)) := by
  rw [rh_iff_residual_zero]
  constructor
  · intro hd
    apply Filter.Eventually.frequently
    exact Eventually.of_forall (fun _ => by simp [reciprocalResiduePairing, hd])
  · intro hf
    by_contra hd
    have he : 0 < ‖limitResidual‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
    have ht : ∀ᶠ k : ℕ in atTop,
        reciprocalResiduePairing (a ^ (k + k)) - 2 * reciprocalResiduePairing (a ^ k) < 0 :=
      (reciprocalResiduePairing_doubling_tendsto ha).eventually (Iio_mem_nhds (neg_lt_zero.mpr he))
    obtain ⟨k, hk, hk'⟩ := (hf.and_eventually ht).exists
    exact (not_lt_of_ge (sub_nonneg.mpr hk)) hk'

/-- The signed semiprime test is precisely the failure of coprime additivity
of the density-transformed residue pairing. -/
theorem semiprime_pairing_eq_residue_defect {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    zetaTwo * inner ℝ limitResidual (densityP (ramanujanPacketHilbert (p * q))) =
      reciprocalResiduePairing (p * q) - reciprocalResiduePairing p -
        reciprocalResiduePairing q := by
  have hv : DP (ramanujanPacketHilbert (p * q)) =
      toPareto (approximation (p * q)) - toPareto (approximation p) -
        toPareto (approximation q) := by
    apply hilbertSequence_injective
    funext n
    simp only [DP_physical, semiprime_packet_sequence hp hq hne, hilbertSequence_sub, Pi.sub_apply,
      toPareto_sequence, approximation_sequence _ n (Nat.mul_pos hp.pos hq.pos),
      approximation_sequence _ n hp.pos, approximation_sequence _ n hq.pos, residue, sub_div]
  have h := residual_pairing_identity hp hq hne
  rw [hv, inner_add_right, limitResidual_mean_and_screened_norm.1, inner_sub_right,
    inner_sub_right] at h
  unfold reciprocalResiduePairing
  linarith


/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.upperBlock_fekete_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upperBlock_fekete_eq

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.riemannHypothesis_iff_frequently_nonnegative_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_frequently_nonnegative_block

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.riemannHypothesis_iff_frequently_residue_doubling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_frequently_residue_doubling

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.semiprime_pairing_eq_residue_defect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms semiprime_pairing_eq_residue_defect

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.eventually_power_subadditive_zero_rate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_power_subadditive_zero_rate

end RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete
