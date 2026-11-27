/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualPrimeChronologicalHaar
import RiemannResearch.Analysis.ActualConsecutiveTripleFourier
import Mathlib.NumberTheory.Bertrand

/-! # Three consecutive primes recover two neighboring unfolded zero gaps

Finite-frequency cancellation and the microscopic tests have different total
prime frequencies. Resonant three-ordinate tests retain both gaps. Rounding
their two integer orders incurs a telescoping first-moment error. Bertrand's
theorem makes the estimate uniform in the choice of consecutive primes.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate ZeroOrdinate CompactCharacter CompactGaugeOrbitLaw

local instance : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance : BorelSpace PrimeTorus := ⟨rfl⟩
local instance : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

/-- The two gap frequencies may be varied independently of the base ordinate frequency. -/
def markedAdjacentGapMean (T h u v : ℝ) : ℂ :=
  (∑ j ∈ Finset.range (Ncount 0 T - 2),
    phase h (cutoffOrdinate T j) * (phase u (cutoffGap T j) * phase v (cutoffGap T (j + 1)))) /
      (Ncount 0 T : ℂ)

theorem interiorTriple_eq_markedGap (T a b c : ℝ) :
    interiorTriplePhaseSum T a b c / (Ncount 0 T : ℂ) = markedAdjacentGapMean T (a + b + c) (b + c) c := by
  unfold interiorTriplePhaseSum markedAdjacentGapMean
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [phase, cutoffGap, ← Complex.exp_add, show j + 1 + 1 = j + 2 by omega]
  congr 1
  push_cast
  ring

private theorem phase_frequency_error (x u v : ℝ) (hx : 0 ≤ x) :
    ‖phase u x - phase v x‖ ≤ |u - v| * x := by
  have h := OrdinateLagPhase.phase_norm_sub_le x u v
  simpa only [OrdinateLagEquidistribution.lagPhase_eq_zeroOrdinatePhase, phase,
    mul_comm x u, mul_comm x v, abs_of_nonneg hx, mul_comm x |u - v|] using h

private theorem gap_phase_product_error (x y u v U V : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖phase u x * phase v y - phase U x * phase V y‖ ≤ |u - U| * x+|v - V| * y := by
  have he : phase u x * phase v y - phase U x * phase V y =
      (phase u x - phase U x) * phase v y + phase U x * (phase v y - phase V y) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, phase_norm, mul_one, one_mul]
  exact add_le_add (phase_frequency_error x u U hx) (phase_frequency_error y v V hy)

/-- A first-moment bound, uniform in the modulating base phase, for two genuine consecutive gaps. -/
theorem markedAdjacentGapMean_lipschitz {T : ℝ} (hT : 0 ≤ T) (h u v U V : ℝ) :
    ‖markedAdjacentGapMean T h u v - markedAdjacentGapMean T h U V‖ ≤
      (|u - U| + |v - V|) * (T / (Ncount 0 T : ℝ)) := by
  let J := Ncount 0 T - 2
  have hnon (j : ℕ) : 0 ≤ cutoffOrdinate T j := by
    by_cases hj : j < Ncount 0 T
    · exact (cutoffOrdinate_bounds hj).1.le
    · rw [cutoffOrdinate_of_count_le (le_of_not_gt hj)]; exact hT
  have hs0 : (∑ j ∈ Finset.range J, cutoffGap T j) ≤ T := by
    rw [show (∑ j ∈ Finset.range J, cutoffGap T j) = cutoffOrdinate T J - cutoffOrdinate T 0 from
      Finset.sum_range_sub (cutoffOrdinate T) J]
    linarith only [hnon 0, cutoffOrdinate_le T J]
  have hs1 : (∑ j ∈ Finset.range J, cutoffGap T (j + 1)) ≤ T := by
    rw [show (∑ j ∈ Finset.range J, cutoffGap T (j + 1)) = cutoffOrdinate T (J + 1) - cutoffOrdinate T 1 from
      Finset.sum_range_sub (fun n => cutoffOrdinate T (n + 1)) J]
    linarith only [hnon 1, cutoffOrdinate_le T (J + 1)]
  unfold markedAdjacentGapMean
  rw [← sub_div, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (_root_.norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range J, (|u - U| * cutoffGap T j+|v - V| * cutoffGap T (j + 1)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, norm_mul, phase_norm, one_mul]
      exact gap_phase_product_error _ _ _ _ _ _ (cutoffGap_nonneg T j) (cutoffGap_nonneg T (j + 1))
    _ = |u - U| * (∑ j ∈ Finset.range J, cutoffGap T j)+|v - V| * (∑ j ∈ Finset.range J, cutoffGap T (j + 1)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (|u - U| + |v - V|) * T := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hs0 (abs_nonneg _)) (mul_le_mul_of_nonneg_left hs1 (abs_nonneg _))

theorem tendsto_height_div_zero_count : Tendsto (fun T : ℝ => T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_lag_height_div_count (fun _ => 1)
    (by simpa using Real.tendsto_log_atTop.const_div_atTop (1 : ℝ))
  simpa using h

/-- Cancellation of a fixed, unbalanced three-ordinate character holds at count normalization. -/
theorem tendsto_fixed_triple_word (s t w : PrimeWord) :
    Tendsto (fun T : ℝ => interiorTriplePhaseSum T (wordFrequency s) (wordFrequency t) (wordFrequency w) /
      (Ncount 0 T : ℂ)) atTop (𝓝 (haarMoment ((s++t)++w))) := by
  let W := (s++t)++w
  let a := wordFrequency s
  let b := wordFrequency t
  let c := wordFrequency w
  let F : C(PrimeTorus × PrimeTorus, ℂ) := (character W).comp ⟨Prod.fst, continuous_fst⟩
  have hsingle := tendsto_chronologicalPairAverage (fun _ => 2)
    (by simpa using Real.tendsto_log_atTop.const_div_atTop (2 : ℝ)) F
  have hmean (T : ℝ) : chronologicalPairAverage T 2 F = markedAdjacentGapMean T (a + b + c) 0 0 := by
    unfold chronologicalPairAverage markedAdjacentGapMean
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change character W (phasePoint _) = _
    simp only [character_phasePoint, W, wordFrequency_append, a, b, c, phase_zero, mul_one]
  have hlim : (∫ x, F x ∂diagonalHaar) = haarMoment W := by
    rw [diagonalHaar_integral]
    exact primeHaar_word W
  simp_rw [hmean] at hsingle
  rw [hlim] at hsingle
  have hdiff : Tendsto (fun T => markedAdjacentGapMean T (a + b + c) (b + c) c -
      markedAdjacentGapMean T (a + b + c) 0 0) atTop (𝓝 0) := by
    have hz := tendsto_height_div_zero_count.const_mul (|b + c| + |c|)
    simp only [mul_zero] at hz
    apply squeeze_zero_norm' _ hz
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [sub_zero] using markedAdjacentGapMean_lipschitz hT (a + b + c) (b + c) c 0 0
  simp_rw [interiorTriple_eq_markedGap]
  simpa only [sub_add_cancel, zero_add] using hdiff.add hsingle

/-- For three different ordered primes the fixed p, q^(-2), r correlation vanishes. -/
theorem tendsto_offDiagonal_three_primes (p q r : Nat.Primes) (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) :
    Tendsto (fun T : ℝ => interiorTriplePhaseSum T (Real.log (p : ℕ)) (-2 * Real.log (q : ℕ)) (Real.log (r : ℕ)) /
      (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
  let W : PrimeWord := [(p, 1), (q, -2), (r, 1)]
  have hx : (fun i : wordPrimes W => wordMode W i) ≠ 0 := by
    intro h
    have hmem : (p : ℕ) ∈ wordPrimes W := by simp [W, wordPrimes]
    have he := congrFun h (⟨(p : ℕ), hmem⟩ : wordPrimes W)
    simp [W, wordMode, ne_of_lt hpq, ne_of_lt (hpq.trans hqr)] at he
  have hW : haarMoment W = 0 := by rw [haarMoment_eq, if_neg hx]
  have h := tendsto_fixed_triple_word [(p, 1)] [(q, -2)] [(r, 1)]
  change Tendsto _ atTop (𝓝 (haarMoment W)) at h
  rw [hW] at h
  simpa [wordFrequency] using h


/-- The cumulative second-moment estimate obtained by dyadically summing
Fujii's bound suffices, including the shortened terminal gap at the cutoff. -/
theorem vanishingCutoffGapEnergy_of_second_moment {K : ℝ}
    (h : ∀ᶠ T : ℝ in atTop, cutoffGapEnergy T ≤ K * T / Real.log T) : VanishingCutoffGapEnergy := by
  apply squeeze_zero' _ _ (Real.tendsto_log_atTop.const_div_atTop K)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T ht
    exact div_nonneg (cutoffGapEnergy_nonneg T) ht.le
  · filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hi ht
    apply (div_le_iff₀ (zero_lt_one.trans ht)).mpr
    exact hi.trans_eq (by ring)

/-- The fixed three-prime off-diagonal also cancels at height normalization
under the gap - energy input implied by Fujii's unconditional second moment. -/
theorem tendsto_offDiagonal_three_primes_height (p q r : Nat.Primes) (hpq : (p : ℕ) < q)
    (hqr : (q : ℕ) < r) (hgap : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ => interiorTriplePhaseSum T (Real.log (p : ℕ)) (-2 * Real.log (q : ℕ)) (Real.log (r : ℕ)) /
      (T : ℂ)) atTop (𝓝 0) := by
  let n := (p : ℕ) * (r : ℕ)
  let m := (q : ℕ) * (q : ℕ)
  have hn : 1 ≤ n := Nat.mul_pos p.property.pos r.property.pos
  have hm : 1 ≤ m := Nat.mul_pos q.property.pos q.property.pos
  have nd (x y : Nat.Primes) (h : (x : ℕ) ≠ y) : ¬ (x : ℕ) ∣ (y : ℕ) := fun hdiv =>
    h (((Nat.dvd_prime y.property).mp hdiv).resolve_left x.property.ne_one)
  have hqn : ¬ (q : ℕ) ∣ n := by
    intro hh
    rcases q.property.dvd_mul.mp hh with h | h
    · exact nd q p (ne_of_lt hpq).symm h
    · exact nd q r (ne_of_lt hqr) h
  have hpm : ¬ (p : ℕ) ∣ m := by
    intro hh
    rcases p.property.dvd_mul.mp hh with h | h <;> exact nd p q (ne_of_lt hpq) h
  have hmn : ¬ m ∣ n := fun h => hqn ((dvd_mul_right (q : ℕ) (q : ℕ)).trans h)
  have hnm : ¬ n ∣ m := fun h => hpm ((dvd_mul_right (p : ℕ) (r : ℕ)).trans h)
  have hne : n ≠ m := fun e => hnm (dvd_of_eq e)
  have hz : rationalFMZMain n m = 0 := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · simp [rationalFMZMain, not_lt.mpr hl.le, rationalLandauMain_eq_vonMangoldt_div_sqrt hn hl, hnm]
    · simp [rationalFMZMain, hl, rationalLandauMain_eq_vonMangoldt_div_sqrt hm hl, hmn]
  have hfreq : Real.log (p : ℕ) + (-2 * Real.log (q : ℕ)) + Real.log (r : ℕ) = Real.log ((n : ℝ) / m) := by
    dsimp only [n, m]
    push_cast
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast r.property.ne_zero
    rw [Real.log_div (mul_ne_zero hp0 hr0) (mul_ne_zero hq0 hq0), Real.log_mul (by exact_mod_cast p.property.ne_zero)
      (by exact_mod_cast r.property.ne_zero), Real.log_mul (by exact_mod_cast q.property.ne_zero)
      (by exact_mod_cast q.property.ne_zero)]
    ring
  simpa only [hz] using tendsto_interiorTriple_rational_of_gap hn hm hne _ _ _ hfreq hgap

def ratioWord (p q : Nat.Primes) (k : ℤ) : PrimeWord := [(q, k), (p, -k)]

def logPrimeStep (p q : Nat.Primes) : ℝ := Real.log (q : ℕ) - Real.log (p : ℕ)

theorem ratioWord_frequency (p q : Nat.Primes) (k : ℤ) :
    wordFrequency (ratioWord p q k) = (k : ℝ) * logPrimeStep p q := by
  simp [ratioWord, wordFrequency, logPrimeStep]; ring

/-- A resonant correlation on three successive zeros. Each factor is a finite prime character. -/
def resonantThreePrimeSample (T : ℝ) (p q r : Nat.Primes) (k l : ℤ) : ℂ :=
  (∑ j ∈ Finset.range (Ncount 0 T - 2),
    character (ratioWord p q (-k)) (phasePoint (cutoffOrdinate T j)) *
    character (ratioWord p q k ++ ratioWord q r (-l)) (phasePoint (cutoffOrdinate T (j + 1))) *
    character (ratioWord q r l) (phasePoint (cutoffOrdinate T (j + 2)))) / (Ncount 0 T : ℂ)

theorem resonantThreePrimeSample_eq (T : ℝ) (p q r : Nat.Primes) (k l : ℤ) :
    resonantThreePrimeSample T p q r k l =
      markedAdjacentGapMean T 0 ((k : ℝ) * logPrimeStep p q) ((l : ℝ) * logPrimeStep q r) := by
  let u := (k : ℝ) * logPrimeStep p q
  let v := (l : ℝ) * logPrimeStep q r
  have he : resonantThreePrimeSample T p q r k l = interiorTriplePhaseSum T (-u) (u - v) v / (Ncount 0 T : ℂ) := by
    unfold resonantThreePrimeSample interiorTriplePhaseSum
    simp only [character_phasePoint, wordFrequency_append, ratioWord_frequency, Int.cast_neg, neg_mul, sub_eq_add_neg, u, v]
  rw [he, interiorTriple_eq_markedGap, show - u + (u - v) + v = 0 by ring, sub_add_cancel]


/-- Each fixed resonant order sees the collapse of the two unscaled gaps. -/
theorem tendsto_resonantThreePrimeSample_fixed (p q r : Nat.Primes) (k l : ℤ) :
    Tendsto (fun T : ℝ => resonantThreePrimeSample T p q r k l) atTop (𝓝 1) := by
  let s := ratioWord p q (-k)
  let t := ratioWord p q k ++ ratioWord q r (-l)
  let w := ratioWord q r l
  have hsum : wordFrequency ((s++t)++w) = 0 := by
    simp only [s, t, w, wordFrequency_append, ratioWord_frequency, Int.cast_neg, neg_mul]
    ring
  have h := tendsto_fixed_triple_word s t w
  rw [haarMoment_frequency, if_pos hsum] at h
  apply h.congr
  intro T
  unfold resonantThreePrimeSample interiorTriplePhaseSum
  simp only [s, t, w, character_phasePoint]

def unfoldedAdjacentGapTransform (T ξ η : ℝ) : ℂ :=
  markedAdjacentGapMean T 0 (ξ * (Real.log T / (2 * Real.pi))) (η * (Real.log T / (2 * Real.pi)))

def roundedOrder (step x : ℝ) : ℤ := ⌊x / step + 1 / 2⌋

theorem roundedOrder_error {step : ℝ} (hs : 0 < step) (x : ℝ) :
    |(roundedOrder step x : ℝ) * step - x| ≤ step / 2 := by
  have hlo := Int.floor_le (x / step + 1 / 2)
  have hhi := Int.lt_floor_add_one (x / step + 1 / 2)
  have hlo' := mul_le_mul_of_nonneg_right hlo hs.le
  have hhi' := mul_lt_mul_of_pos_right hhi hs
  rw [add_mul, div_mul_cancel₀ _ hs.ne'] at hlo'
  rw [add_mul, div_mul_cancel₀ _ hs.ne', add_mul] at hhi'
  apply abs_le.mpr
  dsimp [roundedOrder]
  constructor <;> linarith only [hlo', hhi']

def roundedThreePrimeSample (T : ℝ) (p q r : Nat.Primes) (ξ η : ℝ) : ℂ :=
  resonantThreePrimeSample T p q r
    (roundedOrder (logPrimeStep p q) (ξ * (Real.log T / (2 * Real.pi))))
    (roundedOrder (logPrimeStep q r) (η * (Real.log T / (2 * Real.pi))))

theorem logPrimeStep_pos {p q : Nat.Primes} (h : (p : ℕ) < q) : 0 < logPrimeStep p q :=
  sub_pos.mpr (Real.log_lt_log (by exact_mod_cast p.property.pos) (by exact_mod_cast h))

/-- Quantitative reconstruction of the joint microscopic Fourier test, at all frequency pairs. -/
theorem roundedThreePrimeSample_error {T : ℝ} (hT : 0 ≤ T) (p q r : Nat.Primes)
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) (ξ η : ℝ) :
    ‖roundedThreePrimeSample T p q r ξ η - unfoldedAdjacentGapTransform T ξ η‖ ≤
      (logPrimeStep p q + logPrimeStep q r) / 2 * (T / (Ncount 0 T : ℝ)) := by
  unfold roundedThreePrimeSample unfoldedAdjacentGapTransform
  rw [resonantThreePrimeSample_eq]
  apply (markedAdjacentGapMean_lipschitz hT _ _ _ _ _).trans
  apply mul_le_mul_of_nonneg_right _ (div_nonneg hT (Nat.cast_nonneg _))
  exact (add_le_add (roundedOrder_error (logPrimeStep_pos hpq) _) (roundedOrder_error (logPrimeStep_pos hqr) _)).trans_eq (by ring)

def NextPrime (p q : Nat.Primes) : Prop :=
  (p : ℕ) < q ∧ ∀ n : ℕ, n.Prime → (p : ℕ) < n → (q : ℕ) ≤ n

theorem NextPrime.logPrimeStep_le {p q : Nat.Primes} (h : NextPrime p q) : logPrimeStep p q ≤ Real.log 2 := by
  obtain ⟨n, hn, hpn, hnp⟩ := Nat.exists_prime_lt_and_le_two_mul (p : ℕ) p.property.ne_zero
  have hqp : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast (h.2 n hn hpn).trans hnp
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hh := Real.log_le_log (by exact_mod_cast q.property.pos : 0 < (q : ℝ)) hqp
  rw [Real.log_mul (by norm_num) hp.ne'] at hh
  dsimp [logPrimeStep]
  linarith only [hh]

/-- Uniformity includes moving consecutive prime triples and arbitrary moving frequency pairs. -/
theorem roundedThreePrimeSample_error_consecutive {T : ℝ} (hT : 0 ≤ T) {p q r : Nat.Primes}
    (hpq : NextPrime p q) (hqr : NextPrime q r) (ξ η : ℝ) :
    ‖roundedThreePrimeSample T p q r ξ η - unfoldedAdjacentGapTransform T ξ η‖ ≤
      Real.log 2 * (T / (Ncount 0 T : ℝ)) := by
  apply (roundedThreePrimeSample_error hT p q r hpq.1 hqr.1 ξ η).trans
  exact mul_le_mul_of_nonneg_right (by linarith only [hpq.logPrimeStep_le, hqr.logPrimeStep_le])
    (div_nonneg hT (Nat.cast_nonneg _))


/-- The same prime triple controls every finite Fourier test of the two gaps.
The loss is its coefficient ℓ¹ norm times the uniform one - character error. -/
theorem threePrime_gap_polynomial_error {ι : Type*} (I : Finset ι) (b : ι → ℂ) (ξ η : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {p q r : Nat.Primes} (hpq : NextPrime p q) (hqr : NextPrime q r) :
    ‖(∑ i ∈ I, b i * roundedThreePrimeSample T p q r (ξ i) (η i)) -
      ∑ i ∈ I, b i * unfoldedAdjacentGapTransform T (ξ i) (η i)‖ ≤
      (∑ i ∈ I, ‖b i‖) * (Real.log 2 * (T / (Ncount 0 T : ℝ))) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (_root_.norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (roundedThreePrimeSample_error_consecutive hT hpq hqr _ _) (norm_nonneg _)

theorem tendsto_threePrime_iff_unfoldedGapPair (p q r : ℝ → Nat.Primes)
    (hpq : ∀ᶠ T : ℝ in atTop, NextPrime (p T) (q T)) (hqr : ∀ᶠ T : ℝ in atTop, NextPrime (q T) (r T))
    (ξ η : ℝ → ℝ) (z : ℂ) :
    Tendsto (fun T => roundedThreePrimeSample T (p T) (q T) (r T) (ξ T) (η T)) atTop (𝓝 z) ↔
      Tendsto (fun T => unfoldedAdjacentGapTransform T (ξ T) (η T)) atTop (𝓝 z) := by
  have hd : Tendsto (fun T => roundedThreePrimeSample T (p T) (q T) (r T) (ξ T) (η T) -
      unfoldedAdjacentGapTransform T (ξ T) (η T)) atTop (𝓝 0) := by
    have hz := tendsto_height_div_zero_count.const_mul (Real.log 2)
    simp only [mul_zero] at hz
    apply squeeze_zero_norm' _ hz
    filter_upwards [eventually_ge_atTop (0 : ℝ), hpq, hqr] with T ht hp hq
    exact roundedThreePrimeSample_error_consecutive ht hp hq _ _
  constructor
  · intro h
    simpa only [sub_sub_cancel, sub_zero] using h.sub hd
  · intro h
    simpa only [sub_add_cancel, zero_add] using hd.add h

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.tendsto_offDiagonal_three_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_offDiagonal_three_primes

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.tendsto_offDiagonal_three_primes_height' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_offDiagonal_three_primes_height

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.roundedThreePrimeSample_error_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms roundedThreePrimeSample_error_consecutive

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.tendsto_threePrime_iff_unfoldedGapPair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_threePrime_iff_unfoldedGapPair

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
