import RiemannResearch.RH.ParetoPrimeNormalizedCancellation
import RiemannResearch.RH.CanonicalTailCapacityGeometry

/-!
# Exact prime budgets for the first-site capacity provider

Source: user continuation from e9f76732570540900138d9e6b01c43ee4188c3d6
(2026-09-30), and the existing factorial-coprime Schur identities in
ParetoCoprimePrimeUpdates, ParetoPrimeSourceDivergence and ParetoPrimeCancellation.
These references support the definitions and proof strategy.

Stage n contains moduli 2 through n+1. Budget index j uses the innovation
at stage j+1 and the prospective modulus j+3. All physical tails, signed
cross terms, error squares and nonprime increments are retained.

The positive source budget is already known to diverge. The new exact
identity isolates the combined signed correction. The cofinal strict-fraction
bounds remain explicit OPEN arithmetic hypotheses. No provider, capacity
divergence, zero limiting vacancy or unconditional RH is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP

def factorialPrimeGain (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then (schurEta (n+1))^2 / schurSigma (n+1) else 0

def factorialCompositeGain (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then 0 else (schurEta (n+1))^2 / schurSigma (n+1)

/-- The signed mixed term, before multiplication by two. -/
def factorialPrimeCrossEnergy (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then
    factorialPrimeDelta n * factorialPrimeError n / schurSigma (n+1) else 0

def primeSourceBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, factorialPrimeSourceEnergy n

def primeErrorBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, factorialPrimeErrorEnergy n

def primeGainBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, factorialPrimeGain n

def primeCrossBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, factorialPrimeCrossEnergy n

def compositeGainBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, factorialCompositeGain n

/-- Error square plus signed mixed energy plus every nonprime increment. -/
def primeSignedBudget (N : ℕ) : ℝ :=
  primeErrorBudget N + 2 * primeCrossBudget N + compositeGainBudget N

theorem factorialPrimeGain_nonneg (n : ℕ) : 0 ≤ factorialPrimeGain n := by
  unfold factorialPrimeGain
  split_ifs
  · exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le
  · exact le_rfl

theorem factorialCompositeGain_nonneg (n : ℕ) : 0 ≤ factorialCompositeGain n := by
  unfold factorialCompositeGain
  split_ifs
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le

theorem factorialSchurGain_eq_split (n : ℕ) :
    (schurEta (n+1))^2 / schurSigma (n+1) =
      factorialPrimeGain n + factorialCompositeGain n := by
  by_cases hp : Nat.Prime (n+3) <;>
    simp [factorialPrimeGain, factorialCompositeGain, hp]

theorem factorialPrimeGain_eq_signed_energy (n : ℕ) :
    factorialPrimeGain n =
      factorialPrimeSourceEnergy n + factorialPrimeErrorEnergy n +
        2 * factorialPrimeCrossEnergy n := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [factorialPrimeGain, factorialPrimeSourceEnergy,
      factorialPrimeErrorEnergy, factorialPrimeCrossEnergy, if_pos hp]
    rw [factorialPrimeError_decomposition n hp]
    unfold factorialPrimeDelta
    ring
  · simp [factorialPrimeGain, factorialPrimeSourceEnergy,
      factorialPrimeErrorEnergy, factorialPrimeCrossEnergy, hp]

/-- Exact accounting after separating prospective prime and nonprime moduli. -/
theorem capacity_eq_prime_composite_budget (N : ℕ) :
    tailCapacity (N+1) =
      tailCapacity 1 + primeGainBudget N + compositeGainBudget N := by
  induction N with
  | zero => simp [primeGainBudget, compositeGainBudget]
  | succ N ih =>
    rw [capacity_schur_step, ih]
    simp only [primeGainBudget, compositeGainBudget, Finset.sum_range_succ]
    rw [factorialSchurGain_eq_split]
    ring

theorem primeGainBudget_eq_signed (N : ℕ) :
    primeGainBudget N =
      primeSourceBudget N + primeErrorBudget N + 2 * primeCrossBudget N := by
  unfold primeGainBudget primeSourceBudget primeErrorBudget primeCrossBudget
  simp_rw [factorialPrimeGain_eq_signed_energy]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The full capacity identity; the initial modulus-two capacity is retained. -/
theorem capacity_eq_prime_signed_budget (N : ℕ) :
    tailCapacity (N+1) =
      tailCapacity 1 + primeSourceBudget N + primeSignedBudget N := by
  rw [capacity_eq_prime_composite_budget, primeGainBudget_eq_signed]
  unfold primeSignedBudget
  ring

/-- The unconditional borderline estimate, compatible with bounded capacity. -/
theorem primeSignedBudget_lower (N : ℕ) :
    -primeSourceBudget N ≤ primeSignedBudget N := by
  have h := tailCapacity_monotone (show 1 ≤ N+1 by omega)
  rw [capacity_eq_prime_signed_budget N] at h
  linarith

theorem primeSourceBudget_tendsto :
    Tendsto primeSourceBudget atTop atTop :=
  factorialPrimeSourceEnergy_sum_tendsto

/-- The weakest exact scalar provider: unbounded combined signed budgets.
This is an equivalence of propositions, not a provider construction. -/
theorem tailCapacity_tendsto_iff_prime_budget_unbounded :
    Tendsto tailCapacity atTop atTop ↔
      ∀ B : ℝ, ∃ N : ℕ, B < primeSourceBudget N + primeSignedBudget N := by
  constructor
  · intro ht B
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_atTop.mp ht) (B + tailCapacity 1 + 1))
    have hh := hN (N+1) (Nat.le_succ N)
    rw [capacity_eq_prime_signed_budget N] at hh
    exact ⟨N, by linarith⟩
  · intro h
    apply tendsto_atTop.mpr
    intro B
    obtain ⟨N, hN⟩ := h (B - tailCapacity 1)
    have hC : B ≤ tailCapacity (N+1) := by
      rw [capacity_eq_prime_signed_budget]
      linarith
    exact eventually_atTop.mpr ⟨N+1, fun n hn =>
      hC.trans (tailCapacity_monotone hn)⟩

/-- CONDITIONAL RESEARCH REDUCTION. The open arithmetic hypothesis is a
cofinal fixed strict-fraction lower bound on the combined signed correction. -/
theorem tailCapacity_tendsto_of_prime_signed_fraction
    (θ K : ℝ) (hθ : θ < 1)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      -θ * primeSourceBudget N - K ≤ primeSignedBudget N) :
    Tendsto tailCapacity atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hp : 0 < 1 - θ := by linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_atTop.mp primeSourceBudget_tendsto)
      ((B + K - tailCapacity 1) / (1-θ)))
  obtain ⟨N, hN, hs⟩ := h N₀
  have hu := (div_le_iff₀ hp).mp (hN₀ N hN)
  have hC : B ≤ tailCapacity (N+1) := by
    rw [capacity_eq_prime_signed_budget]
    nlinarith
  exact eventually_atTop.mpr ⟨N+1, fun n hn =>
    hC.trans (tailCapacity_monotone hn)⟩

def primeYoungSquare (t : ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then
    (t * schurEta (n+1) + factorialPrimeError n)^2 /
      (t * schurSigma (n+1))
  else 0

theorem primeYoungSquare_nonneg (t : ℝ) (ht : 0 < t) (n : ℕ) :
    0 ≤ primeYoungSquare t n := by
  unfold primeYoungSquare
  split_ifs
  · exact div_nonneg (sq_nonneg _) (mul_pos ht (schurSigma_pos _)).le
  · exact le_rfl

/-- Exact weighted square completion; no mixed term is discarded. -/
theorem prime_source_young_completion (t : ℝ) (ht : 0 < t) (n : ℕ) :
    factorialPrimeSourceEnergy n + primeYoungSquare t n =
      (1+t) * factorialPrimeGain n +
        (1+1/t) * factorialPrimeErrorEnergy n := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [factorialPrimeSourceEnergy, primeYoungSquare,
      factorialPrimeGain, factorialPrimeErrorEnergy, if_pos hp]
    rw [factorialPrimeError_decomposition n hp]
    field_simp [ne_of_gt ht, ne_of_gt (schurSigma_pos (n+1))]
    ring
  · simp [factorialPrimeSourceEnergy, primeYoungSquare,
      factorialPrimeGain, factorialPrimeErrorEnergy, hp]

/-- Full cumulative square completion, with the remainder retained. -/
theorem primeSourceBudget_young_completion (t : ℝ) (ht : 0 < t) (N : ℕ) :
    primeSourceBudget N + (∑ n ∈ Finset.range N, primeYoungSquare t n) =
      (1+t) * primeGainBudget N + (1+1/t) * primeErrorBudget N := by
  unfold primeSourceBudget primeGainBudget primeErrorBudget
  rw [← Finset.sum_add_distrib]
  simp_rw [prime_source_young_completion t ht]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem primeGainBudget_le_capacity (N : ℕ) :
    primeGainBudget N ≤ tailCapacity (N+1) := by
  have hc : 0 ≤ compositeGainBudget N :=
    Finset.sum_nonneg (fun n _ => factorialCompositeGain_nonneg n)
  rw [capacity_eq_prime_composite_budget]
  linarith [tailCapacity_nonneg 1]

/-- Upper comparison obtained only after dropping the explicit nonnegative
Young square and nonprime gains from the preceding exact identities. -/
theorem primeSourceBudget_le_capacity_error (t : ℝ) (ht : 0 < t) (N : ℕ) :
    primeSourceBudget N ≤
      (1+t) * tailCapacity (N+1) + (1+1/t) * primeErrorBudget N := by
  have hs : 0 ≤ ∑ n ∈ Finset.range N, primeYoungSquare t n :=
    Finset.sum_nonneg (fun n _ => primeYoungSquare_nonneg t ht n)
  have hg := mul_le_mul_of_nonneg_left (primeGainBudget_le_capacity N)
    (by linarith : 0 ≤ 1+t)
  linarith [primeSourceBudget_young_completion t ht N]

/-- CONDITIONAL RESEARCH REDUCTION with an explicit tunable comparison.
The cofinal relative error-budget bound is not proved here. -/
theorem tailCapacity_tendsto_of_prime_error_fraction
    (t θ K : ℝ) (ht : 0 < t) (hθ : (1+1/t) * θ < 1)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      primeErrorBudget N ≤ θ * primeSourceBudget N + K) :
    Tendsto tailCapacity atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have ha : 0 < 1+1/t := by positivity
  have hb : 0 < 1+t := by linarith
  have hp : 0 < 1-(1+1/t)*θ := by linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_atTop.mp primeSourceBudget_tendsto)
      (((1+t)*B + (1+1/t)*K) / (1-(1+1/t)*θ)))
  obtain ⟨N, hN, hs⟩ := h N₀
  have hu := (div_le_iff₀ hp).mp (hN₀ N hN)
  have he := mul_le_mul_of_nonneg_left hs ha.le
  have hy := primeSourceBudget_le_capacity_error t ht N
  have hC : B ≤ tailCapacity (N+1) := by
    nlinarith
  exact eventually_atTop.mpr ⟨N+1, fun n hn =>
    hC.trans (tailCapacity_monotone hn)⟩


/-- A cofinal error-energy fraction below one suffices; error summability
is not required. The fraction bound remains OPEN. -/
theorem tailCapacity_tendsto_of_prime_error_strict_fraction
    (θ K : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      primeErrorBudget N ≤ θ * primeSourceBudget N + K) :
    Tendsto tailCapacity atTop atTop := by
  let t : ℝ := (1+θ)/(1-θ)
  have hp : 0 < 1-θ := by linarith
  have hq : 0 < 1+θ := by linarith
  have ht : 0 < t := div_pos hq hp
  have he : (1+1/t)*θ = 2*θ/(1+θ) := by
    dsimp [t]
    field_simp [ne_of_gt hp, ne_of_gt hq]
    ring
  apply tailCapacity_tendsto_of_prime_error_fraction t θ K ht _ h
  rw [he]
  exact (div_lt_one hq).mpr (by linarith)

/-- A nonzero closed residual forces aggregate cancellation at the exact
boundary -1. The converse is not asserted. -/
theorem primeSignedBudget_ratio_tendsto_of_nonzero_residual
    (hr : pointDualResidual ≠ 0) :
    Tendsto (fun N => primeSignedBudget N / primeSourceBudget N)
      atTop (𝓝 (-1 : ℝ)) := by
  have hC := (tailCapacity_tendsto_canonical_energy hr).comp (tendsto_add_atTop_nat 1)
  have hU := tendsto_inv_atTop_zero.comp primeSourceBudget_tendsto
  have hl : Tendsto
      (fun N => (tailCapacity (N+1) - tailCapacity 1) *
        (primeSourceBudget N)⁻¹ - 1) atTop (𝓝 (-1 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero, zero_sub] using
      ((hC.sub (tendsto_const_nhds (x := tailCapacity 1))).mul hU).sub
        (tendsto_const_nhds (x := (1 : ℝ)))
  have he : ∀ᶠ N in atTop,
      (tailCapacity (N+1) - tailCapacity 1) * (primeSourceBudget N)⁻¹ - 1 =
        primeSignedBudget N / primeSourceBudget N := by
    filter_upwards [(tendsto_atTop.mp primeSourceBudget_tendsto) 1] with N hN
    have hU0 : primeSourceBudget N ≠ 0 := by linarith
    rw [capacity_eq_prime_signed_budget N]
    field_simp [hU0]
    ring
  exact hl.congr' he

/-- CONDITIONAL RESEARCH REDUCTION: all arithmetic content remains in h. -/
theorem riemannHypothesis_of_prime_signed_fraction
    (θ K : ℝ) (hθ : θ < 1)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      -θ * primeSourceBudget N - K ≤ primeSignedBudget N) :
    RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (tailCapacity_tendsto_of_prime_signed_fraction θ K hθ h)


/-- Every bounded-capacity alternative forces the same normalized signed
cancellation. This necessary condition is not an equivalence. -/
theorem primeSignedBudget_ratio_tendsto_of_capacity_bounded
    (h : ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B) :
    Tendsto (fun N => primeSignedBudget N / primeSourceBudget N)
      atTop (𝓝 (-1 : ℝ)) := by
  apply primeSignedBudget_ratio_tendsto_of_nonzero_residual
  intro hz
  obtain ⟨B, hB⟩ := h
  have he : Tendsto pointError atTop (𝓝 0) := by
    simpa only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      pointError_tendsto_residual
  have ht := tailCapacity_tendsto_iff.mpr he
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (B+1))
  have hh := hN N le_rfl
  linarith [hB N]



end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
