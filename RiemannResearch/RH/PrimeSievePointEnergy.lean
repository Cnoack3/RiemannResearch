import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.CoupledCorrectionRHBridge
import Mathlib.Data.Nat.Factorial.Basic
import RiemannResearch.RH.ParetoPrimePackets
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting
import RiemannResearch.Analysis.FinitePrimeProductBounds

/-!
# The actual finite Möbius sieve for the first-coordinate target

Source: user-provided `RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 27–28. The support `Y.factorial.divisors` is used: non-squarefree
divisors have Möbius coefficient zero, so this is the same finite sieve as the
primorial support. All displayed sums retain their signs.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- The finite signed reciprocal mass of a conductor. -/
def sieveReciprocal (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

/-- Exact count of positive integers up to `k` coprime to `P`. -/
def sieveRoughCount (P k : ℕ) : ℝ :=
  cumulative (fun j => if Nat.gcd P j = 1 then 1 else 0) k

/-- The full finite signed residue sieve. -/
def sieveResidue (P n k : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * residueFraction (n*d) k

private theorem moebius_real_sum_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have hi := (mobius_inversion
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun k => (if k = 0 then 0 else 1 : ℝ) -
      (if k - 1 = 0 then 0 else 1 : ℝ))).mpr
      (fun d hd => mobiusDifference_one d hd)
  have hh := hi n (Nat.pos_of_ne_zero hn0)
  simpa [hn0, hn1, show n - 1 ≠ 0 by omega] using hh

/-- Finite Möbius inclusion–exclusion, with the arithmetic gcd proved explicitly. -/
theorem sieve_divisorIndicator (P k : ℕ) (hP : 0 < P) (_hk : 0 < k) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d k) =
      if Nat.gcd P k = 1 then 1 else 0 := by
  have hg : Nat.gcd P k ≠ 0 := ne_of_gt (Nat.gcd_pos_of_pos_left k hP)
  have hfilter : P.divisors.filter (fun d => d ∣ k) = (Nat.gcd P k).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdP, _⟩, hdk⟩
      exact ⟨Nat.dvd_gcd hdP hdk, hg⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_left P k), ne_of_gt hP⟩,
        dvd_trans hdg (Nat.gcd_dvd_right P k)⟩
  simp only [divisorIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter, moebius_real_sum_divisors]

/-- Actual finite floor counting, with no distributional approximation. -/
theorem sieve_floor_count (P k : ℕ) (hP : 0 < P) :
    (∑ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : ℝ) * ((k / d : ℕ) : ℝ)) =
        sieveRoughCount P k := by
  calc
    _ = ∑ d ∈ P.divisors,
        (ArithmeticFunction.moebius d : ℝ) * cumulative (divisorIndicator d) k := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [cumulative_divisorIndicator d k (Nat.pos_of_mem_divisors hd)]
    _ = cumulative (fun j => ∑ d ∈ P.divisors,
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d j) k := by
      unfold cumulative
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      unfold sieveRoughCount cumulative
      apply Finset.sum_congr rfl
      intro j hj
      exact sieve_divisorIndicator P (j+1) hP (by omega)

private theorem sieve_residue_div_floor (d k : ℕ) (hd : 0 < d) :
    residueFraction d k = (k : ℝ) / (d : ℝ) - ((k / d : ℕ) : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have he : ((k % d : ℕ) : ℝ) + (d : ℝ) * ((k / d : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.mod_add_div k d
  unfold residueFraction
  field_simp
  nlinarith

/-- Equation (27.1), for every positive conductor, including repeated prime factors. -/
theorem sieveResidue_exact (P n k : ℕ) (hP : 0 < P) (hn : 0 < n) :
    sieveResidue P n k = sieveReciprocal P * (k : ℝ) / n -
      sieveRoughCount P (k/n) := by
  unfold sieveResidue
  calc
    _ = ∑ d ∈ P.divisors,
        ((k : ℝ) / n * ((ArithmeticFunction.moebius d : ℝ) / d) -
          (ArithmeticFunction.moebius d : ℝ) * (((k/n)/d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [sieve_residue_div_floor (n*d) k (Nat.mul_pos hn (Nat.pos_of_mem_divisors hd)),
        Nat.div_div_eq_div_mul]
      push_cast
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sieve_floor_count P (k/n) hP]
      unfold sieveReciprocal
      ring

@[simp] theorem sieveRoughCount_zero (P : ℕ) : sieveRoughCount P 0 = 0 := by
  simp [sieveRoughCount]

/-- Below the factorial cutoff the only surviving positive integer is one. -/
theorem sieveRoughCount_factorial_head (Y k : ℕ) (hk : 0 < k) (hkY : k ≤ Y) :
    sieveRoughCount Y.factorial k = 1 := by
  calc
    _ = cumulative (fun j => if j = 1 then (1 : ℝ) else 0) k := by
      unfold sieveRoughCount cumulative
      apply Finset.sum_congr rfl
      intro j hj
      have hjY : j+1 ≤ Y := by have := Finset.mem_range.mp hj; omega
      dsimp only
      simp only [Nat.gcd_eq_right (Nat.dvd_factorial (by omega) hjY)]
    _ = 1 := cumulative_delta_one k hk

/-- The reciprocal mass is the exact rough-number density on one full period. -/
theorem sieveReciprocal_mul_conductor (P : ℕ) (hP : 0 < P) :
    sieveReciprocal P * P = sieveRoughCount P P := by
  have h := sieveResidue_exact P 1 P hP (by decide)
  have hz : sieveResidue P 1 P = 0 := by
    unfold sieveResidue
    apply Finset.sum_eq_zero
    intro d hd
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
  simp only [Nat.div_one, Nat.cast_one, div_one, hz] at h
  linarith

theorem sieveReciprocal_pos (P : ℕ) (hP : 0 < P) : 0 < sieveReciprocal P := by
  have hb : (1 : ℝ) ≤ sieveRoughCount P P := by
    have h := Finset.single_le_sum
      (s := Finset.range P) (f := fun j => if Nat.gcd P (j+1) = 1 then (1 : ℝ) else 0)
      (fun j hj => by split_ifs <;> norm_num)
      (show 0 ∈ Finset.range P by exact Finset.mem_range.mpr hP)
    simpa [sieveRoughCount, cumulative] using h
  have hid := sieveReciprocal_mul_conductor P hP
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  nlinarith

theorem sieveReciprocal_le_one (P : ℕ) (hP : 0 < P) : sieveReciprocal P ≤ 1 := by
  have hb : sieveRoughCount P P ≤ (P : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range P, (1 : ℝ) := by
        unfold sieveRoughCount cumulative
        apply Finset.sum_le_sum
        intro j hj
        dsimp only
        split_ifs <;> norm_num
      _ = _ := by simp
  have hid := sieveReciprocal_mul_conductor P hP
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  nlinarith

theorem primeSievePoint_den_pos (Y : ℕ) : 0 < 1 - sieveReciprocal Y.factorial / 2 := by
  have := sieveReciprocal_le_one Y.factorial (Nat.factorial_pos Y)
  linarith

/-- The actual candidate from (28.1), with factorial divisors as redundant support. -/
def primeSievePoint (Y k : ℕ) : ℝ :=
  sieveResidue Y.factorial 2 k - sieveResidue Y.factorial 1 k

/-- The signed prime-sieve arithmetic identity (28.2). -/
theorem primeSievePoint_exact (Y k : ℕ) :
    primeSievePoint Y k = sieveRoughCount Y.factorial k -
      sieveRoughCount Y.factorial (k/2) - sieveReciprocal Y.factorial * k / 2 := by
  unfold primeSievePoint
  rw [sieveResidue_exact _ _ _ (Nat.factorial_pos Y) (by decide),
    sieveResidue_exact _ _ _ (Nat.factorial_pos Y) (by decide)]
  simp only [Nat.div_one, Nat.cast_one, div_one]
  ring

/-- The exact physical head (28.3), not merely a coefficient identity. -/
theorem primeSievePoint_head (Y k : ℕ) (hk : 0 < k) (hkY : k ≤ Y) :
    primeSievePoint Y k = (if k = 1 then 1 else 0) -
      sieveReciprocal Y.factorial * k / 2 := by
  rw [primeSievePoint_exact, sieveRoughCount_factorial_head Y k hk hkY]
  by_cases hk1 : k = 1
  · subst k
    norm_num
  · rw [if_neg hk1, sieveRoughCount_factorial_head Y (k/2) (by omega)
        ((Nat.div_le_self k 2).trans hkY)]
    ring

theorem sieveResidue_mem_legal (P n : ℕ) (hn : 0 < n) :
    sieveResidue P n ∈ legalSeedSpan allPositiveSeeds := by
  have hs : (∑ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : ℝ) • residueFraction (n*d)) ∈
        legalSeedSpan allPositiveSeeds := by
    apply Submodule.sum_mem
    intro d hd
    exact (legalSeedSpan allPositiveSeeds).smul_mem _
      (residueFraction_mem_legal (n*d) (Nat.mul_pos hn (Nat.pos_of_mem_divisors hd)))
  convert hs using 1
  funext k
  simp only [sieveResidue, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem primeSievePoint_mem_legal (Y : ℕ) :
    primeSievePoint Y ∈ legalSeedSpan allPositiveSeeds := by
  exact (legalSeedSpan allPositiveSeeds).sub_mem
    (sieveResidue_mem_legal Y.factorial 2 (by decide))
    (sieveResidue_mem_legal Y.factorial 1 (by decide))

/-- First-coordinate normalization, with its denominator retained explicitly. -/
def normalizedPrimeSievePoint (Y k : ℕ) : ℝ :=
  primeSievePoint Y k / (1 - sieveReciprocal Y.factorial / 2)

theorem normalizedPrimeSievePoint_mem_legal (Y : ℕ) :
    normalizedPrimeSievePoint Y ∈ legalSeedSpan allPositiveSeeds := by
  have h := (legalSeedSpan allPositiveSeeds).smul_mem
    (1 / (1 - sieveReciprocal Y.factorial / 2)) (primeSievePoint_mem_legal Y)
  convert h using 1
  funext k
  simp [normalizedPrimeSievePoint, div_eq_mul_inv, mul_comm]

theorem normalizedPrimeSievePoint_one (Y : ℕ) (hY : 1 ≤ Y)
    :
    normalizedPrimeSievePoint Y 1 = 1 := by
  unfold normalizedPrimeSievePoint
  rw [primeSievePoint_head Y 1 (by decide) hY]
  simpa using div_self (ne_of_gt (primeSievePoint_den_pos Y))

/-- Pointwise convergence follows from the ordinary prime-product limit only. -/
theorem primeSievePoint_tendsto (hc : Tendsto (fun Y : ℕ => sieveReciprocal Y.factorial)
    atTop (𝓝 0)) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun Y => primeSievePoint Y k) atTop (𝓝 (if k = 1 then 1 else 0)) := by
  have h : Tendsto (fun Y : ℕ => (if k = 1 then (1 : ℝ) else 0) -
      sieveReciprocal Y.factorial * k / 2) atTop
      (𝓝 ((if k = 1 then (1 : ℝ) else 0) - 0 * (k : ℝ) / 2)) :=
    tendsto_const_nhds.sub ((hc.mul_const (k : ℝ)).div_const 2)
  have he : (fun Y => primeSievePoint Y k) =ᶠ[atTop]
      (fun Y => (if k = 1 then (1 : ℝ) else 0) - sieveReciprocal Y.factorial * k / 2) := by
    filter_upwards [eventually_ge_atTop k] with Y hY
    exact primeSievePoint_head Y k hk hY
  simpa using h.congr' he.symm

theorem normalizedPrimeSievePoint_tendsto
    (hc : Tendsto (fun Y : ℕ => sieveReciprocal Y.factorial) atTop (𝓝 0))
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun Y => normalizedPrimeSievePoint Y k) atTop
      (𝓝 (if k = 1 then 1 else 0)) := by
  have h := (primeSievePoint_tendsto hc k hk).div
    (tendsto_const_nhds.sub (hc.div_const 2)) (by norm_num : (1 : ℝ) - 0 / 2 ≠ 0)
  change Tendsto (fun Y : ℕ => primeSievePoint Y k /
    (1 - sieveReciprocal Y.factorial / 2)) atTop
      (𝓝 ((if k = 1 then (1 : ℝ) else 0) / (1 - 0/2))) at h
  simpa [normalizedPrimeSievePoint] using h

/-- Full physical tail energy; legal membership guarantees summability below. -/
def primeSievePointTailEnergy (Y : ℕ) : ℝ :=
  ∑' j : ℕ, weight (j+2) * normalizedPrimeSievePoint Y (j+2)^2

theorem primeSievePointTailEnergy_summable (Y : ℕ) :
    Summable (fun j : ℕ => weight (j+2) * normalizedPrimeSievePoint Y (j+2)^2) := by
  exact (legal_fullSquaredNorm_summable allPositiveSeeds
    (by intro d hd; exact hd) _ (normalizedPrimeSievePoint_mem_legal Y)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)

/-- Every retained physical coordinate has the exact square dictated by the signed sieve. -/
theorem primeSievePoint_tail_coordinate (Y j : ℕ) (hj : j+2 ≤ Y) :
    weight (j+2) * normalizedPrimeSievePoint Y (j+2)^2 =
      (sieveReciprocal Y.factorial)^2 /
        (4 * (1 - sieveReciprocal Y.factorial / 2)^2) * ((j+2 : ℕ) : ℝ) /
          ((j+3 : ℕ) : ℝ) := by
  rw [normalizedPrimeSievePoint,
    primeSievePoint_head Y (j+2) (by omega) hj, if_neg (by omega)]
  have hj2 : ((j+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj3 : ((j+3 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold weight
  push_cast
  by_cases hden : 1 - sieveReciprocal Y.factorial / 2 = 0
  · simp [hden]
  · field_simp
    ring

/-- The exact retained-energy lower bound in (28.5), before harmonic rewriting. -/
theorem primeSievePointTailEnergy_lower (Y : ℕ) :
    (sieveReciprocal Y.factorial)^2 /
      (4 * (1 - sieveReciprocal Y.factorial / 2)^2) *
        (∑ j ∈ Finset.range (Y-1), ((j+2 : ℕ) : ℝ) / ((j+3 : ℕ) : ℝ)) ≤
      primeSievePointTailEnergy Y := by
  have h := (primeSievePointTailEnergy_summable Y).sum_le_tsum
    (Finset.range (Y-1)) (fun j hj => by unfold weight; positivity)
  calc
    _ = ∑ j ∈ Finset.range (Y-1),
        weight (j+2) * normalizedPrimeSievePoint Y (j+2)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [primeSievePoint_tail_coordinate Y j (by have := Finset.mem_range.mp hj; omega)]
      ring
    _ ≤ _ := h

/-- A coarse all-cutoff consequence of the exact retained energy, with no rate hypothesis. -/
theorem primeSievePointTailEnergy_coarse_lower (Y : ℕ) :
    (sieveReciprocal Y.factorial)^2 * ((Y-1 : ℕ) : ℝ) / 8 ≤
      primeSievePointTailEnergy Y := by
  let c := sieveReciprocal Y.factorial
  let d := 1 - c/2
  have hc : 0 < c := sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y)
  have hc1 : c ≤ 1 := sieveReciprocal_le_one Y.factorial (Nat.factorial_pos Y)
  have hd : 0 < d := primeSievePoint_den_pos Y
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hdsq : d^2 ≤ 1 := by nlinarith
  have hfac : c^2/4 ≤ c^2/(4*d^2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*d^2)).2
    nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hdsq)]
  have hret : ((Y-1 : ℕ) : ℝ)/2 ≤
      ∑ j ∈ Finset.range (Y-1), ((j+2 : ℕ) : ℝ)/((j+3 : ℕ) : ℝ) := by
    calc
      _ = ∑ _j ∈ Finset.range (Y-1), (1/2 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((j+3 : ℕ) : ℝ))).2
        push_cast
        nlinarith [show (0 : ℝ) ≤ j by positivity]
  calc
    _ = c^2/4 * (((Y-1 : ℕ) : ℝ)/2) := by ring
    _ ≤ c^2/(4*d^2) *
        (∑ j ∈ Finset.range (Y-1), ((j+2 : ℕ) : ℝ)/((j+3 : ℕ) : ℝ)) :=
      mul_le_mul hfac hret (by positivity) (by positivity)
    _ ≤ _ := primeSievePointTailEnergy_lower Y

/-- Exact formal dependency of the divergent-energy statement on its elementary rate. -/
theorem primeSievePointTailEnergy_tendsto_atTop_of_rate
    (hrate : Tendsto (fun Y : ℕ => (sieveReciprocal Y.factorial)^2 * (Y : ℝ))
      atTop atTop) : Tendsto primeSievePointTailEnergy atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have hlarge : ∀ᶠ Y : ℕ in atTop, 8*C+1 ≤ (sieveReciprocal Y.factorial)^2 * (Y : ℝ) :=
    (tendsto_atTop.1 hrate) (8*C+1)
  filter_upwards [hlarge, eventually_ge_atTop 1] with Y hY hY1
  have hlo := primeSievePointTailEnergy_coarse_lower Y
  have hc := sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y)
  have hc1 := sieveReciprocal_le_one Y.factorial (Nat.factorial_pos Y)
  rw [Nat.cast_sub hY1, Nat.cast_one] at hlo
  have hcsq : (sieveReciprocal Y.factorial)^2 ≤ 1 := by nlinarith
  nlinarith


/-- The positive-period count agrees exactly with Mathlib's Euler totient. -/
theorem sieveRoughCount_conductor_eq_totient (P : ℕ) :
    sieveRoughCount P P = (P.totient : ℝ) := by
  let f : ℕ → ℝ := fun j => if Nat.gcd P j = 1 then 1 else 0
  have hsum := (Finset.sum_range_succ' f P).symm.trans (Finset.sum_range_succ f P)
  have hend : f 0 = f P := by simp [f]
  have hshift : (∑ j ∈ Finset.range P, f (j+1)) = ∑ j ∈ Finset.range P, f j := by
    rw [hend] at hsum
    linarith
  change (∑ j ∈ Finset.range P, f (j+1)) = _
  rw [hshift]
  calc
    _ = ∑ _j ∈ (Finset.range P).filter (Nat.Coprime P), (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = (((Finset.range P).filter (Nat.Coprime P)).card : ℝ) := by simp
    _ = _ := by rw [Nat.totient_eq_card_coprime]

/-- Euler's finite product is identified with the actual signed reciprocal mass. -/
theorem sieveReciprocal_eq_primeFactors_product (P : ℕ) (hP : 0 < P) :
    sieveReciprocal P = ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ)) := by
  have ht : (P.totient : ℝ) = (P : ℝ) *
      ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have ht := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors P)
    push_cast at ht
    exact ht
  apply mul_right_cancel₀ (show (P : ℝ) ≠ 0 by positivity)
  rw [sieveReciprocal_mul_conductor P hP, sieveRoughCount_conductor_eq_totient]
  simpa [one_div, mul_comm] using ht

theorem factorial_primeFactors_eq_primesBelow (Y : ℕ) :
    Y.factorial.primeFactors = Y.succ.primesBelow := by
  ext p
  simp only [Nat.mem_primeFactors, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, hd, hn⟩
    exact ⟨by have := (hp.dvd_factorial).mp hd; omega, hp⟩
  · rintro ⟨hpY, hp⟩
    exact ⟨hp, hp.dvd_factorial.mpr (by omega), Nat.factorial_ne_zero Y⟩

/-- The redundant factorial support is exactly the manuscript's finite prime product. -/
theorem sieveReciprocal_factorial_eq_prime_product (Y : ℕ) :
    sieveReciprocal Y.factorial = ∏ p ∈ Y.succ.primesBelow, (1 - 1 / (p : ℝ)) := by
  rw [sieveReciprocal_eq_primeFactors_product _ (Nat.factorial_pos Y),
    factorial_primeFactors_eq_primesBelow]

@[simp] theorem primeSievePoint_zero (Y : ℕ) : primeSievePoint Y 0 = 0 := by
  simp [primeSievePoint, sieveResidue, residueFraction]

theorem primeSievePoint_head_including_zero (Y k : ℕ) (hkY : k ≤ Y) :
    primeSievePoint Y k = (if k = 1 then 1 else 0) -
      sieveReciprocal Y.factorial * k / 2 := by
  by_cases hk : k = 0
  · subst k
    simp
  · exact primeSievePoint_head Y k (Nat.pos_of_ne_zero hk) hkY

/-- The actual biorthogonal coefficient functional for the normalized residues. -/
def primeSievePointCoefficient (Y n : ℕ) : ℝ :=
  -mobiusDifference n (primeSievePoint Y)

/-- The coefficient functional really is biorthogonal to the physical residue atoms. -/
theorem negative_mobiusDifference_residueFraction (n d : ℕ) (hn : 1 < n) (hd : 0 < d) :
    -mobiusDifference n (residueFraction d) = if n = d then 1 else 0 := by
  have hscale : mobiusDifference n (residueFraction d) =
      mobiusDifference n (residue d) / (d : ℝ) := by
    simp [mobiusDifference, residueFraction, residue, sub_div, Finset.sum_div, mul_div_assoc]
  rw [hscale, mobiusDifference_residue n d hn]
  by_cases hnd : n = d
  · simp [hnd, ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd)]
  · simp [hnd]

/-- Every fixed actual coefficient is eventually exactly the forced point coefficient. -/
theorem primeSievePointCoefficient_stabilizes (Y n : ℕ) (hn : 1 < n) (hnY : n ≤ Y) :
    primeSievePointCoefficient Y n = -(ArithmeticFunction.moebius n : ℝ) +
      if 2 ∣ n then (ArithmeticFunction.moebius (n/2) : ℝ) else 0 := by
  have hdif (d : ℕ) (hd : d ∈ n.divisors) :
      primeSievePoint Y d - primeSievePoint Y (d-1) =
        (if d = 1 then (1 : ℝ) else 0) - (if d = 2 then 1 else 0) -
          sieveReciprocal Y.factorial / 2 := by
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdY : d ≤ Y := (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hnY
    rw [primeSievePoint_head_including_zero Y d hdY,
      primeSievePoint_head_including_zero Y (d-1) ((Nat.sub_le d 1).trans hdY),
      Nat.cast_sub hdpos, Nat.cast_one]
    have hpred : d-1 = 1 ↔ d = 2 := by omega
    simp only [hpred]
    ring
  have hsum : mobiusDifference n (primeSievePoint Y) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℝ) *
        ((if d = 1 then (1 : ℝ) else 0) - (if d = 2 then 1 else 0) -
          sieveReciprocal Y.factorial / 2) := by
    unfold mobiusDifference
    apply Finset.sum_congr rfl
    intro d hd
    rw [hdif d hd]
  rw [primeSievePointCoefficient, hsum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, sum_moebius_div n hn]
  have hn0 : n ≠ 0 := by omega
  simp [mul_ite, Nat.mem_divisors, hn0]
  ring

theorem primeSievePointCoefficient_tendsto (n : ℕ) (hn : 1 < n) :
    Tendsto (fun Y : ℕ => primeSievePointCoefficient Y n) atTop
      (𝓝 (-(ArithmeticFunction.moebius n : ℝ) +
        if 2 ∣ n then (ArithmeticFunction.moebius (n/2) : ℝ) else 0)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with Y hY
  exact (primeSievePointCoefficient_stabilizes Y n hn hY).symm

/-- Scalar normalization acts on the actual finite Möbius functional. -/
theorem normalizedPrimeSievePoint_coefficient (Y n : ℕ) :
    -mobiusDifference n (normalizedPrimeSievePoint Y) =
      primeSievePointCoefficient Y n / (1 - sieveReciprocal Y.factorial / 2) := by
  simp [primeSievePointCoefficient, mobiusDifference, normalizedPrimeSievePoint,
    sub_div, Finset.sum_div, neg_div, mul_div_assoc]

theorem normalizedPrimeSievePoint_coefficient_tendsto
    (hc : Tendsto (fun Y : ℕ => sieveReciprocal Y.factorial) atTop (𝓝 0))
    (n : ℕ) (hn : 1 < n) :
    Tendsto (fun Y : ℕ => -mobiusDifference n (normalizedPrimeSievePoint Y)) atTop
      (𝓝 (-(ArithmeticFunction.moebius n : ℝ) +
        if 2 ∣ n then (ArithmeticFunction.moebius (n/2) : ℝ) else 0)) := by
  have h := (primeSievePointCoefficient_tendsto n hn).div
    (tendsto_const_nhds.sub (hc.div_const 2)) (by norm_num : (1 : ℝ) - 0/2 ≠ 0)
  change Tendsto (fun Y : ℕ => primeSievePointCoefficient Y n /
    (1 - sieveReciprocal Y.factorial / 2)) atTop
      (𝓝 ((-(ArithmeticFunction.moebius n : ℝ) +
        if 2 ∣ n then (ArithmeticFunction.moebius (n/2) : ℝ) else 0) / (1 - 0/2))) at h
  simpa [normalizedPrimeSievePoint_coefficient] using h


/-- Euler's ordinary finite-product limit, now for the actual Möbius sieve mass. -/
theorem factorialSieveReciprocal_tendsto_zero :
    Tendsto (fun Y : ℕ => sieveReciprocal Y.factorial) atTop (𝓝 0) := by
  have he : (fun Y : ℕ => sieveReciprocal Y.factorial) = Analysis.finitePrimeProduct := by
    funext Y
    exact sieveReciprocal_factorial_eq_prime_product Y
  rw [he]
  exact Analysis.finitePrimeProduct_tendsto_zero

/-- The elementary lower rate is specialized to the actual legal sieve. -/
theorem factorialSieveReciprocal_square_mul_tendsto_atTop :
    Tendsto (fun Y : ℕ => (sieveReciprocal Y.factorial)^2 * (Y : ℝ)) atTop atTop := by
  simpa only [Analysis.finitePrimeProduct, ← sieveReciprocal_factorial_eq_prime_product] using
    Analysis.finitePrimeProduct_square_mul_tendsto_atTop

theorem normalizedPrimeSievePoint_pointwise_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun Y : ℕ => normalizedPrimeSievePoint Y k) atTop
      (𝓝 (if k = 1 then 1 else 0)) :=
  normalizedPrimeSievePoint_tendsto factorialSieveReciprocal_tendsto_zero k hk

/-- All actual normalized coefficients converge to the forced point-target values. -/
theorem normalizedPrimeSievePoint_actual_coefficients_tendsto (n : ℕ) (hn : 1 < n) :
    Tendsto (fun Y : ℕ => -mobiusDifference n (normalizedPrimeSievePoint Y)) atTop
      (𝓝 (-(ArithmeticFunction.moebius n : ℝ) +
        if 2 ∣ n then (ArithmeticFunction.moebius (n/2) : ℝ) else 0)) :=
  normalizedPrimeSievePoint_coefficient_tendsto factorialSieveReciprocal_tendsto_zero n hn

/-- Despite correct coordinate and coefficient limits, the full physical tail diverges. -/
theorem primeSievePointTailEnergy_tendsto_atTop :
    Tendsto primeSievePointTailEnergy atTop atTop :=
  primeSievePointTailEnergy_tendsto_atTop_of_rate
    factorialSieveReciprocal_square_mul_tendsto_atTop


end RiemannResearch.RH.Pareto
