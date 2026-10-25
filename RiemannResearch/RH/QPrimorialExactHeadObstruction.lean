/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeBalancedSignedTail
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.Basic
import Lean.Elab.Tactic.Omega

/-!
# The proposed primorial exact-head family is unbounded in complete Q norm

Source: the user's choice of a primorial correction conductor, 25 October 2026.
The proof retains the exact prime jump before estimating its finite-window
energy. Growth uses the established unconditional prime number theorem
provider in PrimeNumberTheorem.Consequences. This obstructs this explicit
family, not constant membership in the closed squarefree span.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimorialExactHeadObstruction
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QPrimeBalancedExactHead

/-- The explicit correction anchored at the entire H-primorial. -/
def synthesis (H : ℕ) : QHilbert := primeHead H (primorial H)

theorem synthesis_mem_squarefreeSpan (H : ℕ) :
    synthesis H ∈ qSquarefreeCRTSpan := by
  have hres (d : ℕ) (hd : 0 < d) (hs : Squarefree d) :
      qResidue d ∈ qSquarefreeCRTSpan := by
    by_cases h1 : d = 1
    · rw [h1, qResidue_one]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨d, by omega, hs⟩, rfl⟩
  unfold synthesis primeHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    by_cases hs : Squarefree d
    · exact Submodule.smul_mem _ _ (hres d (Finset.mem_Icc.mp hd).1 hs)
    · have hm : ArithmeticFunction.moebius d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      simp only [hm, Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _
      (hres _ (primorial_pos H) (squarefree_primorial H))

theorem synthesis_exact (H n : ℕ) (hH : 3 ≤ H)
    (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (synthesis H) n = 1 :=
  primeHead_exact H (primorial H) n (lt_primorial_self (by omega)) hn hnH

/-- Before the period wraps, the corrected vector is the finite floor sum. -/
theorem synthesis_before_period (H n : ℕ) (hn : n < primorial H) :
    qSequence (synthesis H) n =
      ∑ d ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
  rw [synthesis, primeHead_floor_identity H (primorial H) n (primorial_pos H),
    Nat.div_eq_of_lt hn]
  simp

/-- An exact new-prime jump, with no discarded arithmetic term. -/
theorem synthesis_prime_jump (p n : ℕ) (hp : Nat.Prime p)
    (hn : n < primorial (p - 1)) :
    qSequence (synthesis p - synthesis (p - 1)) n = -((n / p : ℕ) : ℝ) := by
  have hmono : primorial (p - 1) ≤ primorial p :=
    Nat.le_of_dvd (primorial_pos p) (primorial_dvd_primorial (Nat.sub_le p 1))
  have hsum := RiemannResearch.NumberTheory.positive_prefix_split_at
    (fun d => (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ))
    (p - 1) p (Nat.sub_le p 1)
  have hsucc : p - 1 + 1 = p := by have := hp.pos; omega
  simp only [hsucc, Finset.Icc_self, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one,
    neg_mul, one_mul] at hsum
  change qSequenceLinear (synthesis p - synthesis (p - 1)) n = _
  rw [map_sub]
  change qSequence (synthesis p) n - qSequence (synthesis (p - 1)) n = _
  rw [synthesis_before_period p n (hn.trans_le hmono),
    synthesis_before_period (p - 1) n hn, hsum]
  ring

private theorem floor_square_weight_lower (p n : ℕ)
    (hp : 0 < p) (hpn : p ≤ n) :
    1 / (4 * zetaTwo * (p : ℝ)^2) ≤
      positiveQWeight n * (((n / p : ℕ) : ℝ)^2) := by
  have hn : 0 < n := hp.trans_le hpn
  have hquot : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpn)
  have hmod := Nat.mod_lt n hp
  have hdecomp := Nat.mod_add_div n p
  have hdouble : n ≤ 2 * p * (n / p) := by nlinarith
  have hdoubleR : (n : ℝ) ≤ 2 * (p : ℝ) * ((n / p : ℕ) : ℝ) := by
    exact_mod_cast hdouble
  have hsq : (n : ℝ)^2 ≤ 4 * (p : ℝ)^2 * ((n / p : ℕ) : ℝ)^2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ n) hdoubleR]
  have hZ := zetaTwo_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold positiveQWeight
  rw [one_div_mul_eq_div]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * zetaTwo * (p : ℝ)^2)
    (by positivity : 0 < zetaTwo * (n : ℝ)^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hZ.le]

/-- Finite-coordinate energy is a lower bound on the complete Q norm. -/
theorem synthesis_prime_jump_norm_lower (p : ℕ) (hp : Nat.Prime p) :
    ((primorial (p - 1) - p : ℕ) : ℝ) /
        (4 * zetaTwo * (p : ℝ)^2) ≤
      ‖synthesis p - synthesis (p - 1)‖^2 := by
  let f := synthesis p - synthesis (p - 1)
  have hfinite :
      (∑ n ∈ Finset.Ico p (primorial (p - 1)),
        positiveQWeight n * (qSequence f n)^2) ≤ ‖f‖^2 := by
    rw [qNorm_weighted_sq]
    exact (qSequence_square_summable f).sum_le_tsum _
      (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
  have hsum :
      (∑ n ∈ Finset.Ico p (primorial (p - 1)),
        1 / (4 * zetaTwo * (p : ℝ)^2)) ≤
      ∑ n ∈ Finset.Ico p (primorial (p - 1)),
        positiveQWeight n * (qSequence f n)^2 := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hpn, hnP⟩ := Finset.mem_Ico.mp hn
    change 1 / (4 * zetaTwo * (p : ℝ)^2) ≤
      positiveQWeight n * (qSequence (synthesis p - synthesis (p - 1)) n)^2
    rw [synthesis_prime_jump p n hp hnP, neg_sq]
    exact floor_square_weight_lower p n hp.pos hpn
  have hcard :
      (∑ n ∈ Finset.Ico p (primorial (p - 1)),
        1 / (4 * zetaTwo * (p : ℝ)^2)) =
      ((primorial (p - 1) - p : ℕ) : ℝ) /
        (4 * zetaTwo * (p : ℝ)^2) := by
    simp [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, div_eq_mul_inv]
  rw [hcard] at hsum
  exact hsum.trans hfinite

/-- The adjacent pair must absorb the entire prime-jump energy. -/
theorem synthesis_prime_pair_norm_lower (p : ℕ) (hp : Nat.Prime p) :
    ((primorial (p - 1) - p : ℕ) : ℝ) /
        (4 * zetaTwo * (p : ℝ)^2) ≤
      2 * (‖synthesis p‖^2 + ‖synthesis (p - 1)‖^2) := by
  have h := synthesis_prime_jump_norm_lower p hp
  have ht := norm_sub_le (synthesis p) (synthesis (p - 1))
  have hn := norm_nonneg (synthesis p - synthesis (p - 1))
  have ha := norm_nonneg (synthesis p)
  have hb := norm_nonneg (synthesis (p - 1))
  have hs := sq_nonneg (‖synthesis p‖ - ‖synthesis (p - 1)‖)
  nlinarith

/-- A deliberately weak polynomial consequence of the established PNT provider.
It suffices for the finite-window obstruction and assumes no RH statement. -/
theorem primorial_cubic_eventually :
    ∀ᶠ H : ℕ in atTop, (H : ℝ)^3 / 48 ≤ (primorial H : ℝ) := by
  obtain ⟨E, hE, hprod⟩ :=
    RiemannResearch.NumberTheory.PrimeNumberTheorem.primorial_bounds
  have hb : ∀ᶠ H : ℕ in atTop, ‖E (H : ℝ)‖ ≤ (1 / 2 : ℝ) * ‖(H : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      (hE.bound (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hb] with H hH
  have hi : Finset.Iic H = Finset.range (H + 1) := by
    ext d
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  have heq : (primorial H : ℝ) = Real.exp ((H : ℝ) + E (H : ℝ)) := by
    simpa [primorial, Nat.floor_natCast, hi] using hprod (H : ℝ)
  have hhalf : (H : ℝ) / 2 ≤ (H : ℝ) + E (H : ℝ) := by
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg H : (0 : ℝ) ≤ (H : ℝ))] at hH
    linarith [neg_le_abs (E (H : ℝ))]
  calc
    (H : ℝ)^3 / 48 = ((H : ℝ) / 2)^3 / (Nat.factorial 3 : ℝ) := by
      norm_num
      ring
    _ ≤ Real.exp ((H : ℝ) / 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) 3
    _ ≤ Real.exp ((H : ℝ) + E (H : ℝ)) := Real.exp_le_exp.mpr hhalf
    _ = (primorial H : ℝ) := heq.symm

/-- No eventual uniform norm bound exists for this concrete primorial family. -/
theorem synthesis_not_eventually_norm_le (B : ℝ) :
    ¬ ∀ᶠ H : ℕ in atTop, ‖synthesis H‖ ≤ B := by
  intro hB
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp primorial_cubic_eventually
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hB
  obtain ⟨K, hK⟩ := exists_nat_gt (384 * (16 * zetaTwo * B^2 + 1))
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max (N + N0 + 5) K)
  have hplarge : N + N0 + 5 ≤ p := (le_max_left _ _).trans hpbound
  have hpK : K ≤ p := (le_max_right _ _).trans hpbound
  have hp5 : 5 ≤ p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hpbig : 384 * (16 * zetaTwo * B^2 + 1) < (p : ℝ) :=
    hK.trans_le (by exact_mod_cast hpK)
  have hsmall : (p - 1 : ℕ) < primorial (p - 1) :=
    lt_primorial_self (by omega)
  have hpP : p ≤ primorial (p - 1) := by omega
  have hpcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have hlow := hN (p - 1) (by omega)
  rw [hpcast] at hlow
  have hpHalf : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hcube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (p : ℝ) / 2) hpHalf 3
  have hPlow : (p : ℝ)^3 / 384 ≤ (primorial (p - 1) : ℝ) := by
    nlinarith
  have hn1 := hN0 p (by omega)
  have hn2 := hN0 (p - 1) (by omega)
  have hs1 : ‖synthesis p‖^2 ≤ B^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn1 2
  have hs2 : ‖synthesis (p - 1)‖^2 ≤ B^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn2 2
  have hpair := synthesis_prime_pair_norm_lower p hp
  have hupper : ((primorial (p - 1) - p : ℕ) : ℝ) /
      (4 * zetaTwo * (p : ℝ)^2) ≤ 4 * B^2 := by nlinarith
  rw [Nat.cast_sub hpP] at hupper
  have hZ := zetaTwo_pos
  have hmul := (div_le_iff₀ (by positivity :
    0 < 4 * zetaTwo * (p : ℝ)^2)).mp hupper
  have hstrict := mul_lt_mul_of_pos_right hpbig (sq_pos_of_pos hpR)
  have hpSq : (p : ℝ) ≤ (p : ℝ)^2 := by nlinarith
  nlinarith

/-- In particular this exact-head construction has no strong Q-Hilbert limit. -/
theorem synthesis_not_tendsto (f : QHilbert) :
    ¬ Tendsto synthesis atTop (𝓝 f) := by
  intro h
  apply synthesis_not_eventually_norm_le (‖f‖ + 1)
  exact (h.norm.eventually (Iio_mem_nhds (by linarith : ‖f‖ < ‖f‖ + 1))).mono
    (fun _ ht => ht.le)

end RiemannResearch.RH.QPrimorialExactHeadObstruction
