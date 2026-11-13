import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


/-!
# The physical Pareto logarithm and smooth exponential targets

Source: Christian Noack's corrected assertion that h(n) = Lambda(n)/log(n)
itself belongs to the Pareto legal closure. No Ramanujan packet synthesis
is used here.

We encode that actual bounded sequence in the complete Pareto Hilbert space.
The prime-restricted Euler exponential has coefficients equal to the smooth
indicator. The Euler-exponential identification is explained in the companion
note; this module verifies the physical indicator, its exact error mass,
the bound 1/(N+1), and convergence to one.

Ambient Hilbert membership is unconditional. Membership of the logarithm in
the legal closure, and legality of its smooth exponential targets, are kept
as separate propositions. Neither is supplied as a proved provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalLogarithm

def physicalLog (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)

@[simp] theorem physicalLog_zero : physicalLog 0 = 0 := by simp [physicalLog]
@[simp] theorem physicalLog_one : physicalLog 1 = 0 := by simp [physicalLog]

theorem physicalLog_bounds (n : ℕ) : 0 ≤ physicalLog n ∧ physicalLog n ≤ 1 := by
  by_cases h : n ≤ 1
  · interval_cases n <;> norm_num
  · have hn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    exact ⟨div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn.le,
      (div_le_one hn).mpr ArithmeticFunction.vonMangoldt_le_log⟩

theorem bounded_square_summable {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) :
    Summable (fun n => positiveWeight n * f n ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) _ positiveWeight_summable
  intro n
  have hs : f n ^ 2 ≤ 1 := by nlinarith [(hf n).1, (hf n).2]
  simpa using mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg n)

def physicalLogHilbert : ThresholdHilbert :=
  sequenceHilbert physicalLog (bounded_square_summable physicalLog_bounds)

@[simp] theorem physicalLogHilbert_sequence :
    hilbertSequence physicalLogHilbert = physicalLog :=
  hilbertSequence_sequenceHilbert _ _ physicalLog_zero

def Smooth (N n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ≤ N

local instance : DecidableRel Smooth := fun _ _ => Classical.propDecidable _

def smoothSequence (N n : ℕ) : ℝ := by
  classical
  exact if n = 0 then 0 else if Smooth N n then 1 else 0

theorem smooth_of_le {N n : ℕ} (hn : n ≤ N) : Smooth N n := by
  intro p hp
  exact (Nat.le_of_mem_primeFactors hp).trans hn

@[simp] theorem smoothSequence_zero (N : ℕ) : smoothSequence N 0 = 0 := by
  simp [smoothSequence]

theorem smoothSequence_bounds (N n : ℕ) :
    0 ≤ smoothSequence N n ∧ smoothSequence N n ≤ 1 := by
  classical
  unfold smoothSequence
  split_ifs <;> norm_num

theorem smoothSequence_exact_head (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    smoothSequence N n = 1 := by
  simp [smoothSequence, ne_of_gt hn, smooth_of_le hnN]

def smoothHilbert (N : ℕ) : ThresholdHilbert :=
  sequenceHilbert (smoothSequence N)
    (bounded_square_summable (smoothSequence_bounds N))

@[simp] theorem smoothHilbert_sequence (N : ℕ) :
    hilbertSequence (smoothHilbert N) = smoothSequence N :=
  hilbertSequence_sequenceHilbert _ _ (smoothSequence_zero N)

theorem smooth_error_eq_rough_mass (N : ℕ) :
    ‖hilbertOne - smoothHilbert N‖ ^ 2 =
      ∑' n : ℕ, if Smooth N n then 0 else positiveWeight n := by
  classical
  rw [hilbert_norm_weighted_sq]
  apply tsum_congr
  intro n
  have he : hilbertSequence (hilbertOne - smoothHilbert N) n =
      hilbertSequence hilbertOne n - hilbertSequence (smoothHilbert N) n := by
    exact congrFun (hilbertSequenceLinear.map_sub _ _) n
  rw [he, hilbertOne_sequence, smoothHilbert_sequence]
  by_cases hn : n = 0
  · subst n
    simp [zeroAnchor, positiveWeight, smoothSequence]
  · by_cases hs : Smooth N n <;> simp [zeroAnchor, smoothSequence, hn, hs]

theorem smooth_error_sq_le (N : ℕ) :
    ‖hilbertOne - smoothHilbert N‖ ^ 2 ≤ 1 / ((N : ℝ) + 1) := by
  classical
  rw [smooth_error_eq_rough_mass]
  let r : ℕ → ℝ := fun n => if Smooth N n then 0 else positiveWeight n
  have hr : Summable r := by
    apply Summable.of_nonneg_of_le _ _ positiveWeight_summable
    · intro n
      dsimp [r]
      split_ifs
      · exact le_rfl
      · exact positiveWeight_nonneg n
    · intro n
      dsimp [r]
      split_ifs <;> simp [positiveWeight_nonneg]
  have hh : (∑ n ∈ Finset.range (N + 1), r n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [r, smooth_of_le (by have := Finset.mem_range.mp hn; omega : n ≤ N)]
  have ht := hr.sum_add_tsum_nat_add (N + 1)
  rw [hh, zero_add] at ht
  change (∑' n, r n) ≤ _
  rw [← ht]
  calc
    (∑' n, r (n + (N + 1))) ≤ ∑' n, positiveWeight (n + (N + 1)) := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff _).mpr hr)
        ((summable_nat_add_iff _).mpr positiveWeight_summable)
      intro n
      dsimp [r]
      split_ifs <;> simp [positiveWeight_nonneg]
    _ = _ := by simpa using positiveWeight_tail_tsum (N + 1) (by omega)

theorem physicalLog_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    physicalLog (p ^ k) = 1 / (k : ℝ) := by
  rw [physicalLog, ArithmeticFunction.vonMangoldt_apply_pow (ne_of_gt hk),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  field_simp

theorem physicalLog_eq_zero_of_not_primePow (n : ℕ) (hn : ¬ IsPrimePow n) :
    physicalLog n = 0 := by
  simp [physicalLog, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

theorem smoothHilbert_tendsto_one :
    Tendsto smoothHilbert atTop (𝓝 hilbertOne) := by
  have hs : Tendsto (fun N => ‖hilbertOne - smoothHilbert N‖ ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun N => sq_nonneg _) smooth_error_sq_le
      tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using ht


/-- Restriction of the physical logarithm to prime powers supported on primes
at most N. This is an ambient Hilbert vector, with no legality asserted. -/
def primeLogSequence (N n : ℕ) : ℝ :=
  physicalLog n * smoothSequence N n

theorem primeLogSequence_bounds (N n : ℕ) :
    0 ≤ primeLogSequence N n ∧ primeLogSequence N n ≤ 1 := by
  constructor
  · exact mul_nonneg (physicalLog_bounds n).1 (smoothSequence_bounds N n).1
  · exact mul_le_one₀ (physicalLog_bounds n).2
      (smoothSequence_bounds N n).1 (smoothSequence_bounds N n).2

def primeLogHilbert (N : ℕ) : ThresholdHilbert :=
  sequenceHilbert (primeLogSequence N)
    (bounded_square_summable (primeLogSequence_bounds N))

@[simp] theorem primeLogHilbert_sequence (N : ℕ) :
    hilbertSequence (primeLogHilbert N) = primeLogSequence N := by
  apply hilbertSequence_sequenceHilbert
  simp [primeLogSequence]

theorem primeLog_error_sq_le_smooth_error (N : ℕ) :
    ‖physicalLogHilbert - primeLogHilbert N‖ ^ 2 ≤
      ‖hilbertOne - smoothHilbert N‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq, hilbert_norm_weighted_sq]
  apply Summable.tsum_le_tsum _
    (hilbertSequence_square_summable _) (hilbertSequence_square_summable _)
  intro n
  have he : hilbertSequence (physicalLogHilbert - primeLogHilbert N) n =
      physicalLog n - primeLogSequence N n := by
    rw [show hilbertSequence (physicalLogHilbert - primeLogHilbert N) n =
        hilbertSequence physicalLogHilbert n -
          hilbertSequence (primeLogHilbert N) n from
      congrFun (hilbertSequenceLinear.map_sub _ _) n]
    simp
  have ht : hilbertSequence (hilbertOne - smoothHilbert N) n =
      zeroAnchor (fun _ => 1) n - smoothSequence N n := by
    rw [show hilbertSequence (hilbertOne - smoothHilbert N) n =
        hilbertSequence hilbertOne n - hilbertSequence (smoothHilbert N) n from
      congrFun (hilbertSequenceLinear.map_sub _ _) n]
    simp [hilbertOne_sequence]
  rw [he, ht]
  by_cases hn : n = 0
  · subst n
    simp [primeLogSequence, zeroAnchor]
  · by_cases hs : Smooth N n
    · simp [primeLogSequence, smoothSequence, hn, hs, zeroAnchor]
    · simp only [primeLogSequence, smoothSequence, if_neg hs,
        mul_zero, sub_zero, zeroAnchor, if_neg hn, one_pow, mul_one]
      have hsq : physicalLog n ^ 2 ≤ 1 := by
        nlinarith [(physicalLog_bounds n).1, (physicalLog_bounds n).2]
      simpa using mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)

theorem primeLog_error_sq_le (N : ℕ) :
    ‖physicalLogHilbert - primeLogHilbert N‖ ^ 2 ≤ 1 / ((N : ℝ) + 1) :=
  (primeLog_error_sq_le_smooth_error N).trans (smooth_error_sq_le N)

theorem primeLogHilbert_tendsto :
    Tendsto primeLogHilbert atTop (𝓝 physicalLogHilbert) := by
  have hs : Tendsto (fun N => ‖physicalLogHilbert - primeLogHilbert N‖ ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun N => sq_nonneg _) primeLog_error_sq_le
      tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using ht

/-- The user's assertion, retained as a proposition rather than an assumption
silently discharged by ambient square summability. -/
def PhysicalLogLegality : Prop :=
  physicalLogHilbert ∈ CoefficientStabilization.closedSpace

/-- Open arithmetic-to-legal transfer for the prime-restricted exponential
targets, required only eventually, so this does not assume the N = 0 unit.
PhysicalLogLegality is not proved to imply this proposition. -/
def SmoothExponentialLegality : Prop :=
  ∀ᶠ N in atTop, smoothHilbert N ∈ CoefficientStabilization.closedSpace

theorem one_mem_of_smooth_exponential_legality (h : SmoothExponentialLegality) :
    hilbertOne ∈ CoefficientStabilization.closedSpace := by
  have hc : IsClosed (CoefficientStabilization.closedSpace : Set ThresholdHilbert) :=
    isClosed_closure
  exact hc.mem_of_tendsto smoothHilbert_tendsto_one h

/-- Conditional research reduction: complete norm convergence is proved;
SmoothExponentialLegality is the undischarged domain-specific obligation. -/
theorem riemannHypothesis_of_smooth_exponential_legality
    (h : SmoothExponentialLegality) : RiemannHypothesis :=
  CoefficientStabilization.riemannHypothesis_of_limitCoefficients
    (CoefficientStabilization.limitCoefficients_eq_mobius_iff_mem.mpr
      (one_mem_of_smooth_exponential_legality h))

end RiemannResearch.RH.Pareto.PhysicalLogarithm
