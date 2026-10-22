import RiemannResearch.Analysis.CoefficientShift
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Divisibility logarithms and finite Möbius density

The vectors `logVector k` are the real Taylor coefficients of
`-log (1 - z^k)`. Finite Möbius sums over divisors of `N!` cancel all
coefficients except those whose remaining index is coprime to `N!`.
For each positive `k`, these finite sums converge in square norm to `e_k`.

This supplies the logarithmic-generator completeness used for the real
coefficient-space version of S. Waleed Noor, "A Hardy space analysis of the
Baez-Duarte criterion for the RH", Theorem 9,
https://arxiv.org/abs/1809.09577.
The citation supplies the application and logarithmic family; the proof here
uses the elementary finite divisor identity and dominated convergence.
No prime-number-theorem hypothesis is needed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.Noor
open CoefficientShift

/-- Coefficients of the logarithm; the zeroth coefficient is zero. -/
def logSequence (k n : ℕ) : ℝ := if k ∣ n then (k : ℝ) / (n : ℝ) else 0

theorem logSequence_zero (k : ℕ) : logSequence k 0 = 0 := by simp [logSequence]

theorem logSequence_sq_le (k n : ℕ) :
    logSequence k n ^ 2 ≤ (k : ℝ)^2 * (1 / (n : ℝ)^2) := by
  by_cases h : k ∣ n
  · simp only [logSequence, if_pos h, div_pow, mul_one_div, le_refl]
  · simp only [logSequence, if_neg h, zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem logSequence_square_summable (k : ℕ) :
    Summable (fun n => logSequence k n ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (logSequence_sq_le k)
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _)

def logVector (k : ℕ) : Space := ofSquareSummable (logSequence k) (logSequence_square_summable k)

@[simp] theorem logVector_apply (k n : ℕ) : logVector k n = logSequence k n := rfl

theorem norm_sq (a : Space) : ‖a‖ ^ 2 = ∑' n, a n ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [pow_two]

theorem logSequence_mul (k j : ℕ) (hk : 0 < k) :
    logSequence k (k * j) = 1 / (j : ℝ) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [logSequence, Nat.cast_mul, div_mul_eq_div_div, hk']

theorem logVector_norm_sq (k : ℕ) (hk : 0 < k) :
    ‖logVector k‖ ^ 2 = ∑' j : ℕ, 1 / (j : ℝ)^2 := by
  have hinj : Function.Injective (fun j : ℕ => k * j) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hk hij
  have hs : Function.support (fun n => logSequence k n ^ 2) ⊆
      Set.range (fun j : ℕ => k * j) := by
    intro n hn
    by_cases h : k ∣ n
    · obtain ⟨j, rfl⟩ := h
      exact ⟨j, rfl⟩
    · simp [Function.mem_support, logSequence, h] at hn
  rw [norm_sq]
  change (∑' n, logSequence k n ^ 2) = _
  rw [← hinj.tsum_eq hs]
  simp only [logSequence_mul k _ hk, div_pow, one_pow]

theorem logVector_norm (k : ℕ) (hk : 0 < k) :
    ‖logVector k‖ = ‖logVector 1‖ := by
  nlinarith [logVector_norm_sq k hk, logVector_norm_sq 1 (by omega),
    norm_nonneg (logVector k), norm_nonneg (logVector 1)]

theorem divisors_filter (Q m : ℕ) (hQ : Q ≠ 0) :
    Q.divisors.filter (fun d => d ∣ m) = (Nat.gcd m Q).divisors := by
  ext d
  have hg : Nat.gcd m Q ≠ 0 := Nat.gcd_ne_zero_right hQ
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  tauto

theorem moebius_sift (Q m : ℕ) (hQ : Q ≠ 0) :
    (∑ d ∈ Q.divisors.filter (fun d => d ∣ m),
      (ArithmeticFunction.moebius d : ℝ)) =
      if Nat.Coprime m Q then 1 else 0 := by
  rw [divisors_filter Q m hQ]
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply,
    Nat.coprime_iff_gcd_eq_one] using
    congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd m Q))
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))

/-- Exact cancellation formula for a finite divisor sieve. -/
theorem finite_sieve (Q k n : ℕ) (hQ : Q ≠ 0) :
    (∑ d ∈ Q.divisors,
      ((ArithmeticFunction.moebius d : ℝ) / d) * logSequence (k*d) n) =
    if 0 < n ∧ k ∣ n ∧ Nat.Coprime (n/k) Q then (k : ℝ)/n else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [logSequence]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hkn : k ∣ n
  · have hdiv (d : ℕ) : k*d ∣ n ↔ d ∣ n/k := by
      rw [Nat.dvd_div_iff_mul_dvd hkn]
    calc
      _ = ((k : ℝ)/n) *
          (∑ d ∈ Q.divisors,
            if d ∣ n/k then (ArithmeticFunction.moebius d : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hdR : (d : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
        by_cases hdvd : d ∣ n/k
        · have hkdvd := (hdiv d).mpr hdvd
          simp only [logSequence, if_pos hkdvd, if_pos hdvd, Nat.cast_mul]
          field_simp
        · have hkdvd : ¬k*d ∣ n := fun h => hdvd ((hdiv d).mp h)
          simp [logSequence, hkdvd, hdvd]
      _ = ((k : ℝ)/n) * (if Nat.Coprime (n/k) Q then 1 else 0) := by
        rw [← Finset.sum_filter, moebius_sift Q (n/k) hQ]
      _ = _ := by
        by_cases hc : Nat.Coprime (n/k) Q <;> simp [hnpos, hkn, hc]
  · rw [if_neg (by tauto)]
    apply Finset.sum_eq_zero
    intro d hd
    have hkdvd : ¬k*d ∣ n := fun h => hkn ((Nat.dvd_mul_right k d).trans h)
    simp [logSequence, hkdvd]

/-- Finite combinations of logarithmic vectors along divisors of a factorial. -/
def sieveVector (N k : ℕ) : Space :=
  ∑ d ∈ N.factorial.divisors, ((ArithmeticFunction.moebius d : ℝ) / d) • logVector (k*d)

theorem sieveVector_apply (N k n : ℕ) :
    sieveVector N k n =
      if 0 < n ∧ k ∣ n ∧ Nat.Coprime (n/k) N.factorial then (k : ℝ)/n else 0 := by
  change (∑ d ∈ N.factorial.divisors,
    ((ArithmeticFunction.moebius d : ℝ) / d) • logVector (k*d)) n = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, logVector_apply]
  exact finite_sieve N.factorial k n (Nat.factorial_ne_zero N)

theorem sieveVector_at_self (N k : ℕ) (hk : 0 < k) :
    sieveVector N k k = 1 := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  simp [sieveVector_apply, hk, hkR]

theorem sieveVector_eventually (k n : ℕ) (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop, sieveVector N k n = (lp.single 2 k (1 : ℝ) : Space) n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  by_cases hnk : n = k
  · subst n
    simp [sieveVector_at_self N k hk]
  rw [lp.single_apply_ne 2 k 1 hnk, sieveVector_apply]
  by_cases hn : n = 0
  · simp [hn]
  have hnpos := Nat.pos_of_ne_zero hn
  by_cases hkn : k ∣ n
  · have hmpos : 0 < n / k := Nat.div_pos (Nat.le_of_dvd hnpos hkn) hk
    have hmdvd : n / k ∣ N.factorial :=
      Nat.dvd_factorial hmpos ((Nat.div_le_self n k).trans hN)
    have hmne : n / k ≠ 1 := by
      intro he
      have hmul := Nat.mul_div_cancel' hkn
      rw [he, mul_one] at hmul
      exact hnk hmul.symm
    have hnc : ¬ Nat.Coprime (n / k) N.factorial := by
      simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left hmdvd] using hmne
    simp [hnc]
  · simp [hkn]

theorem sieveVector_error_sq_le (N k n : ℕ) (hk : 0 < k) :
    (sieveVector N k n - (lp.single 2 k (1 : ℝ) : Space) n)^2 ≤
      logSequence k n ^ 2 := by
  by_cases hnk : n = k
  · subst n
    simp only [sieveVector_at_self N k hk, lp.single_apply_self, sub_self,
      zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  rw [lp.single_apply_ne 2 k 1 hnk, sub_zero, sieveVector_apply]
  by_cases hh : 0 < n ∧ k ∣ n ∧ Nat.Coprime (n/k) N.factorial
  · simp only [if_pos hh, logSequence, if_pos hh.2.1, le_refl]
  · simp only [if_neg hh, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

/-- The finite sieve converges in the complete square norm to one coordinate. -/
theorem sieveVector_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N => sieveVector N k) atTop (𝓝 (lp.single 2 k (1 : ℝ) : Space)) := by
  have hs : Tendsto (fun N => ‖sieveVector N k - lp.single 2 k (1 : ℝ)‖ ^ 2)
      atTop (𝓝 0) := by
    have ht := tendsto_tsum_of_dominated_convergence (logSequence_square_summable k)
      (f := fun N n => (sieveVector N k n - (lp.single 2 k (1 : ℝ) : Space) n)^2)
      (g := fun _ => (0 : ℝ))
      (fun n => by
        apply tendsto_const_nhds.congr'
        filter_upwards [sieveVector_eventually k n hk] with N hN
        simp [hN])
      (Eventually.of_forall (fun N n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sieveVector_error_sq_le N k n hk))
    simpa only [norm_sq, lp.coeFn_sub, Pi.sub_apply, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

/-- The positive-index logarithmic vectors are total in the zero-constant subspace. -/
theorem eq_zero_of_orthogonal_logVector (a : Space) (ha0 : a 0 = 0)
    (ha : ∀ k : ℕ, 0 < k → inner ℝ a (logVector k) = 0) : a = 0 := by
  apply Subtype.ext
  funext k
  change a k = 0
  by_cases hk : k = 0
  · simpa only [hk] using ha0
  have hkp := Nat.pos_of_ne_zero hk
  have hz (N : ℕ) : inner ℝ a (sieveVector N k) = 0 := by
    unfold sieveVector
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro d hd
    rw [inner_smul_right, ha (k*d) (Nat.mul_pos hkp (Nat.pos_of_mem_divisors hd)), mul_zero]
  have hlim := (tendsto_const_nhds (x := a)).inner (𝕜 := ℝ) (sieveVector_tendsto k hkp)
  have he : inner ℝ a (lp.single 2 k (1 : ℝ)) = (0 : ℝ) :=
    tendsto_nhds_unique (by simpa only [hz] using hlim) tendsto_const_nhds
  simpa [lp.inner_single_right] using he

end RiemannResearch.Analysis.Noor
