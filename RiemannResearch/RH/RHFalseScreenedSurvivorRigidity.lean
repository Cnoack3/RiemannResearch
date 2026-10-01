import RiemannResearch.RH.RHFalseTailConstraints
import RiemannResearch.RH.ParetoFirstSitePrimeSourceFloors

/-!
# Harmonic rigidity of actual prime survivors under failure of RH

Source: user-requested negated-RH synthesis, October 1, 2026; finite estimates
assemble the existing exact Schur and harmonic source identities.

The pointwise harmonic source floor is applied to the actual signed Schur
survivor, not to a raw CRT row. The finite inequalities retain the entire
survivor square and bound every adaptive finite window. Exceptional-row
counts require no PNT. The stronger asymptotic interpretation with prime
density is external ordinary mathematics, not an imported Lean axiom.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis
open RiemannResearch.RH.Pareto.IntegerDPP

/-- Actual prime survivor divided by the strictly positive arithmetic source. -/
def primeRelativeSurvivor (n : ℕ) : ℝ :=
  schurEta (n+1) / factorialPrimeDelta n

def harmonicPrimeSurvivorEnergy (n : ℕ) : ℝ :=
  harmonicPrimeSourceFloor n * (primeRelativeSurvivor n)^2

def harmonicPrimeSurvivorWindow (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, harmonicPrimeSurvivorEnergy (N+i)

def primeSurvivorTailBudget (N : ℕ) : ℝ :=
  (∑' n, factorialPrimeGain n) - primeGainBudget N

def primeExceptionalSurvivorRows (N k : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range k).filter (fun i =>
    Nat.Prime (N+i+3) ∧ ε ≤ |primeRelativeSurvivor (N+i)|)

theorem primeRelativeSurvivor_eq_relative_error (n : ℕ)
    (hp : Nat.Prime (n+3)) :
    primeRelativeSurvivor n = 1 + factorialPrimeError n / factorialPrimeDelta n := by
  have he : schurEta (n+1) = factorialPrimeDelta n + factorialPrimeError n := by
    simpa only [factorialPrimeDelta] using factorialPrimeError_decomposition n hp
  unfold primeRelativeSurvivor
  rw [he]
  field_simp [ne_of_gt (factorialPrimeDelta_pos n)]

theorem primeGain_eq_source_relative_survivor (n : ℕ) :
    factorialPrimeGain n =
      (primeSchurWeight n * (factorialPrimeDelta n)^2) *
        (primeRelativeSurvivor n)^2 := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [factorialPrimeGain, primeSchurWeight, if_pos hp]
    unfold primeRelativeSurvivor
    field_simp [ne_of_gt (factorialPrimeDelta_pos n), ne_of_gt (schurSigma_pos (n+1))]

  · simp [factorialPrimeGain, primeSchurWeight, hp]

theorem harmonicPrimeSurvivorEnergy_nonneg (n : ℕ) :
    0 ≤ harmonicPrimeSurvivorEnergy n :=
  mul_nonneg (harmonicPrimeSourceFloor_nonneg n) (sq_nonneg _)

theorem harmonicPrimeSurvivorEnergy_le_gain (n : ℕ) :
    harmonicPrimeSurvivorEnergy n ≤ factorialPrimeGain n := by
  rw [primeGain_eq_source_relative_survivor]
  exact mul_le_mul_of_nonneg_right (harmonicPrimeSourceFloor_le n) (sq_nonneg _)

theorem harmonicPrimeSurvivorEnergy_summable_of_gain_summable
    (hg : Summable factorialPrimeGain) : Summable harmonicPrimeSurvivorEnergy :=
  Summable.of_nonneg_of_le harmonicPrimeSurvivorEnergy_nonneg
    harmonicPrimeSurvivorEnergy_le_gain hg

theorem factorialPrimeGain_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) : Summable factorialPrimeGain := by
  have hg := (summable_nat_add_iff 1).mpr (schurGain_summable_of_not_RH hRH)
  exact Summable.of_nonneg_of_le factorialPrimeGain_nonneg
    (fun n => by
      unfold factorialPrimeGain
      split_ifs
      · exact le_rfl
      · exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le) hg

theorem harmonicPrimeSurvivorEnergy_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) : Summable harmonicPrimeSurvivorEnergy :=
  harmonicPrimeSurvivorEnergy_summable_of_gain_summable
    (factorialPrimeGain_summable_of_not_RH hRH)

/-- Uniform over all finite lengths k, including lengths selected from the rows. -/
theorem harmonicPrimeSurvivorWindow_le_tailBudget (N k : ℕ)
    (hg : Summable factorialPrimeGain) :
    harmonicPrimeSurvivorWindow N k ≤ primeSurvivorTailBudget N := by
  have hwindow : harmonicPrimeSurvivorWindow N k ≤
      ∑ i ∈ Finset.range k, factorialPrimeGain (N+i) :=
    Finset.sum_le_sum (fun i _ => harmonicPrimeSurvivorEnergy_le_gain (N+i))
  have hsum := hg.sum_le_tsum (Finset.range (N+k))
    (fun n _ => factorialPrimeGain_nonneg n)
  change (∑ n ∈ Finset.range (N+k), factorialPrimeGain n) ≤ _ at hsum
  rw [Finset.sum_range_add] at hsum
  unfold primeSurvivorTailBudget primeGainBudget
  linarith

theorem primeSurvivorTailBudget_tendsto_zero
    (hg : Summable factorialPrimeGain) :
    Tendsto primeSurvivorTailBudget atTop (𝓝 0) := by
  have ht : Tendsto primeGainBudget atTop (𝓝 (∑' n, factorialPrimeGain n)) :=
    hg.hasSum.tendsto_sum_nat
  change Tendsto (fun N => (∑' n, factorialPrimeGain n) - primeGainBudget N) atTop (𝓝 0)
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' n, factorialPrimeGain n)).sub ht

/-- Failure of RH gives a single vanishing bound valid for all future windows. -/
theorem harmonicPrimeSurvivorWindows_uniform_of_not_RH
    (hRH : ¬ RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ,
      harmonicPrimeSurvivorWindow N k < ε := by
  have hg := factorialPrimeGain_summable_of_not_RH hRH
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp (primeSurvivorTailBudget_tendsto_zero hg)).2 ε hε)
  exact ⟨N₀, fun N hN k =>
    (harmonicPrimeSurvivorWindow_le_tailBudget N k hg).trans_lt (hN₀ N hN)⟩

theorem harmonicPrimeSourceFloor_window_lower (N k i : ℕ)
    (hi : i < k) (hp : Nat.Prime (N+i+3)) :
    1 / (4 * (harmonic (N+k+1) : ℝ)) ≤ harmonicPrimeSourceFloor (N+i) := by
  simp only [harmonicPrimeSourceFloor, if_pos hp]
  have hpos := (harmonic_interval_bounds 1 (N+i+2) (by omega)).1
  have h1 : (harmonic 1 : ℝ) = 1 := by norm_num
  rw [h1] at hpos
  apply one_div_le_one_div_of_le (by linarith)
  have hm := (harmonic_interval_bounds (N+i+2) (N+k+1) (by omega)).1
  linarith

/-- Exact finite Markov bound: the full signed actual survivors define the set. -/
theorem primeExceptionalSurvivorRows_count_energy (N k : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ((primeExceptionalSurvivorRows N k ε).card : ℝ) *
      (ε^2 / (4 * (harmonic (N+k+1) : ℝ))) ≤
        harmonicPrimeSurvivorWindow N k := by
  have hpoint (i : ℕ) (hi : i ∈ primeExceptionalSurvivorRows N k ε) :
      ε^2 / (4 * (harmonic (N+k+1) : ℝ)) ≤
        harmonicPrimeSurvivorEnergy (N+i) := by
    obtain ⟨hi, hp, he⟩ := Finset.mem_filter.mp hi
    have hs : ε^2 ≤ (primeRelativeSurvivor (N+i))^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hε he 2
    have hf := harmonicPrimeSourceFloor_window_lower N k i (Finset.mem_range.mp hi) hp
    have hlo : 0 ≤ 1 / (4 * (harmonic (N+k+1) : ℝ)) := by
      exact div_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (harmonic_nonnegative _))
    unfold harmonicPrimeSurvivorEnergy
    calc
      _ = (1 / (4 * (harmonic (N+k+1) : ℝ))) * ε^2 := by ring
      _ ≤ harmonicPrimeSourceFloor (N+i) * (primeRelativeSurvivor (N+i))^2 :=
        mul_le_mul hf hs (sq_nonneg ε) (harmonicPrimeSourceFloor_nonneg _)
  have hsum := Finset.sum_le_sum hpoint
  have hsub : (∑ i ∈ primeExceptionalSurvivorRows N k ε,
      harmonicPrimeSurvivorEnergy (N+i)) ≤ harmonicPrimeSurvivorWindow N k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun i _ _ => harmonicPrimeSurvivorEnergy_nonneg (N+i))
  have hconst : (∑ _i ∈ primeExceptionalSurvivorRows N k ε,
      ε^2 / (4 * (harmonic (N+k+1) : ℝ))) =
        ((primeExceptionalSurvivorRows N k ε).card : ℝ) *
          (ε^2 / (4 * (harmonic (N+k+1) : ℝ))) := by simp
  rw [hconst] at hsum
  exact hsum.trans hsub

theorem primeExceptionalSurvivorRows_count_tail (N k : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (hg : Summable factorialPrimeGain) :
    ((primeExceptionalSurvivorRows N k ε).card : ℝ) *
      (ε^2 / (4 * (harmonic (N+k+1) : ℝ))) ≤
        primeSurvivorTailBudget N :=
  (primeExceptionalSurvivorRows_count_energy N k ε hε).trans
    (harmonicPrimeSurvivorWindow_le_tailBudget N k hg)

/-- OPEN arithmetic provider: no such nonsummability is established here. -/
theorem riemannHypothesis_of_harmonicPrimeSurvivorEnergy_not_summable
    (h : ¬ Summable harmonicPrimeSurvivorEnergy) : RiemannHypothesis := by
  by_contra hRH
  exact h (harmonicPrimeSurvivorEnergy_summable_of_not_RH hRH)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-!
Append after the first failure-rigidity candidate. Every composite gain and
the final remaining certificate error stay visible in the exact equality.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP

def primeSurvivorWindow (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, factorialPrimeGain (N+i)

def compositeSurvivorWindow (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, factorialCompositeGain (N+i)

theorem primeSurvivorWindow_nonneg (N k : ℕ) :
    0 ≤ primeSurvivorWindow N k :=
  Finset.sum_nonneg (fun i _ => factorialPrimeGain_nonneg (N+i))

theorem compositeSurvivorWindow_nonneg (N k : ℕ) :
    0 ≤ compositeSurvivorWindow N k :=
  Finset.sum_nonneg (fun i _ => factorialCompositeGain_nonneg (N+i))

/-- Exact finite capacity step retaining every prime and composite row. -/
theorem capacity_eq_complete_survivor_window (N k : ℕ) :
    tailCapacity (N+k+1) = tailCapacity (N+1) +
      primeSurvivorWindow N k + compositeSurvivorWindow N k := by
  rw [capacity_eq_prime_composite_budget (N+k), capacity_eq_prime_composite_budget N]
  unfold primeGainBudget compositeGainBudget primeSurvivorWindow compositeSurvivorWindow
  rw [Finset.sum_range_add, Finset.sum_range_add]
  ring

/-- Exact certificate error split; the full remaining error is retained. -/
theorem tailCertificate_error_eq_complete_survivor_window (N k : ℕ)
    (z : ThresholdHilbert) (hz : IsResidueTailCertificate z) :
    ‖z - tailMinimum (N+1)‖^2 =
      primeSurvivorWindow N k + compositeSurvivorWindow N k +
        ‖z - tailMinimum (N+k+1)‖^2 := by
  have hfirst := tailCertificate_energy_completion z hz (N+1)
  have hlast := tailCertificate_energy_completion z hz (N+k+1)
  rw [capacity_eq_complete_survivor_window] at hlast
  linarith

theorem harmonicPrimeSurvivorWindow_le_prime_window (N k : ℕ) :
    harmonicPrimeSurvivorWindow N k ≤ primeSurvivorWindow N k :=
  Finset.sum_le_sum (fun i _ => harmonicPrimeSurvivorEnergy_le_gain (N+i))

/-- Uniform finite bound for any genuine certificate; no summability premise. -/
theorem harmonicPrimeSurvivorWindow_le_certificate_error (N k : ℕ)
    (z : ThresholdHilbert) (hz : IsResidueTailCertificate z) :
    harmonicPrimeSurvivorWindow N k ≤ ‖z - tailMinimum (N+1)‖^2 := by
  have he := tailCertificate_error_eq_complete_survivor_window N k z hz
  have hh := harmonicPrimeSurvivorWindow_le_prime_window N k
  linarith [compositeSurvivorWindow_nonneg N k,
    sq_nonneg ‖z - tailMinimum (N+k+1)‖]

theorem primeExceptionalSurvivorRows_count_certificate_error
    (N k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (z : ThresholdHilbert) (hz : IsResidueTailCertificate z) :
    ((primeExceptionalSurvivorRows N k ε).card : ℝ) *
      (ε^2 / (4 * (harmonic (N+k+1) : ℝ))) ≤
        ‖z - tailMinimum (N+1)‖^2 :=
  (primeExceptionalSurvivorRows_count_energy N k ε hε).trans
    (harmonicPrimeSurvivorWindow_le_certificate_error N k z hz)

theorem harmonicPrimeSurvivorWindow_le_canonical_error_of_not_RH
    (hRH : ¬ RiemannHypothesis) (N k : ℕ) :
    harmonicPrimeSurvivorWindow N k ≤
      ‖canonicalTailCertificate - tailMinimum (N+1)‖^2 :=
  harmonicPrimeSurvivorWindow_le_certificate_error N k canonicalTailCertificate
    (canonicalTailCertificate_isCertificate
      (not_RH_pointDualResidual_ne_zero hRH))

theorem primeExceptionalSurvivorRows_count_canonical_error_of_not_RH
    (hRH : ¬ RiemannHypothesis) (N k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ((primeExceptionalSurvivorRows N k ε).card : ℝ) *
      (ε^2 / (4 * (harmonic (N+k+1) : ℝ))) ≤
        ‖canonicalTailCertificate - tailMinimum (N+1)‖^2 :=
  primeExceptionalSurvivorRows_count_certificate_error N k ε hε
    canonicalTailCertificate (canonicalTailCertificate_isCertificate
      (not_RH_pointDualResidual_ne_zero hRH))

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
