/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.Main
import RiemannResearch.RH.WeilExplicitFormula.Statement.SeamClosed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact prime resonances of band-limited zero-coordinate tests

Integer separation for logarithms of ratios isolates the arithmetic term.
The Guinand--Weil formula is as in Iwaniec--Kowalski, Analytic Number Theory,
Theorem 5.12, and is supplied here by the checked declaration
`Zeta23.WeilEF.EF_lit_zeta`. Both signed prime evaluations and every zero
multiplicity are retained. The prime-phase normalization follows the
user's prime-torus Parseval discussion.
-/

noncomputable section
open Set MeasureTheory Zeta23
open scoped ArithmeticFunction

namespace RiemannResearch.Analysis.PrimeBandlimitedWeil

def logRatio (n m : ℕ) : ℝ := Real.log n - Real.log m

/-- The angular Fourier test for a modulated height weight and sech smoothing. -/
def frequencyTest (F : ℝ → ℂ) (T u v : ℝ) : ℂ :=
  ((T / (2 * Real.pi) : ℝ) : ℂ) * F (T * (v - u)) *
    ((Real.cosh (v / 2))⁻¹ : ℝ)

/-- The arithmetic weight of one positive prime-power ratio. -/
def ratioWeight (k : ℕ) : ℝ :=
  (Λ k / Real.sqrt k) * (Real.cosh (Real.log k / 2))⁻¹

def directionalResonance (n m : ℕ) : ℝ :=
  if m ∣ n then ratioWeight (n / m) else 0

/-- The two signs in the Weil prime term contribute these two directions. -/
def resonance (n m : ℕ) : ℝ := directionalResonance n m + directionalResonance m n

/-- The sech weight changes the arithmetic coefficient from inverse square
root decay to inverse first-power decay. -/
theorem ratioWeight_eq (k : ℕ) (hk : 0 < k) :
    ratioWeight k = 2 * Λ k / ((k : ℝ) + 1) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have he : Real.exp (Real.log (k : ℝ) / 2) ^ 2 = (k : ℝ) := by
    rw [pow_two, ← Real.exp_add, show Real.log (k : ℝ) / 2 + Real.log (k : ℝ) / 2 =
      Real.log (k : ℝ) by ring, Real.exp_log hkR]
  have hx : Real.exp (Real.log (k : ℝ) / 2) = Real.sqrt k := by
    rw [← Real.sqrt_sq (Real.exp_pos _).le, he]
  have hs := Real.sqrt_pos.mpr hkR
  have hden : Real.sqrt k * Real.cosh (Real.log (k : ℝ) / 2) = ((k : ℝ) + 1) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, hx]
    calc
      _ = ((Real.sqrt k) ^ 2 + 1) / 2 := by
        field_simp [hs.ne']
      _ = _ := by rw [Real.sq_sqrt hkR.le]
  unfold ratioWeight
  rw [← div_eq_mul_inv, div_div, hden]
  field_simp

theorem resonance_self (n : ℕ) (hn : 0 < n) : resonance n n = 0 := by
  simp [resonance, directionalResonance, Nat.div_self hn, ratioWeight]

/-- The exact prime correction disappears between distinct first-prime modes. -/
theorem resonance_eq_zero_of_distinct_primes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) : resonance p q = 0 := by
  have h₁ : ¬q ∣ p := fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have h₂ : ¬p ∣ q := fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  simp [resonance, directionalResonance, h₁, h₂]

private theorem one_sub_div_le_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - a / b ≤ Real.log b - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  linarith

/-- A distinct positive integer is separated from the anchored logarithm
by the reciprocal of the anchor plus one, even if the other integer is larger. -/
theorem log_gap_nat (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hne : n ≠ k) :
    1 / ((n : ℝ) + 1) ≤ |Real.log k - Real.log n| := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
    have hlog := Real.log_le_log hnR (show (n : ℝ) ≤ k by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    calc
      _ = 1 - (n : ℝ) / ((n : ℝ) + 1) := by
        field_simp
        ring
      _ ≤ 1 - (n : ℝ) / (k : ℝ) := by
        linarith only [div_le_div_of_nonneg_left hnR.le (by positivity) hstep]
      _ ≤ _ := one_sub_div_le_log_sub hnR hkR
  · have hstep : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    have hlog := Real.log_le_log hkR (show (k : ℝ) ≤ n by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub]
    calc
      _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnR (by linarith)
      _ ≤ 1 - (k : ℝ) / (n : ℝ) := by
        have hh : 1 / (n : ℝ) + (k : ℝ) / (n : ℝ) ≤ 1 := by
          rw [← add_div]
          exact (div_le_one hnR).2 (by linarith)
        linarith
      _ ≤ _ := one_sub_div_le_log_sub hkR hnR

theorem frequencyTest_contDiff {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (T u : ℝ) :
    ContDiff ℝ 2 (frequencyTest F T u) := by
  have hcosh : ContDiff ℝ 2 (fun v : ℝ => Real.cosh (v / 2)) := by
    simp only [Real.cosh_eq]
    fun_prop
  have hc : ContDiff ℝ 2 (fun v : ℝ => (Real.cosh (v / 2))⁻¹) :=
    hcosh.fun_inv (fun v => (Real.cosh_pos (v / 2)).ne')
  have hc' : ContDiff ℝ 2 (fun v : ℝ => (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ 2 Complex.ofRealCLM).comp hc
  have hf : ContDiff ℝ 2 (fun v : ℝ => F (T * (v - u))) :=
    hF.comp (by fun_prop)
  exact (contDiff_const.mul hf).mul hc'

theorem frequencyTest_compact {F : ℝ → ℂ}
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    HasCompactSupport (frequencyTest F T u) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (u - 1 / T) (u + 1 / T)) isCompact_Icc
  intro v hv
  have hf : F (T * (v - u)) ≠ 0 := by
    intro h
    exact (Function.mem_support.mp hv) (by simp [frequencyTest, h])
  have h := hF (Function.mem_support.mpr hf)
  have h₁ : -(1 : ℝ) / T ≤ v - u := by
    apply (div_le_iff₀ hT).2
    simpa only [mul_comm] using h.1
  have h₂ : v - u ≤ 1 / T := by
    apply (le_div_iff₀ hT).2
    simpa only [mul_comm] using h.2
  rw [neg_div] at h₁
  exact ⟨by linarith, by linarith⟩

private theorem frequencyTest_eq_zero_of_gap {F : ℝ → ℂ}
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) {T a u v : ℝ} (ha : 0 < a)
    (hT : a < T) (hgap : 1 / a ≤ |v - u|) : frequencyTest F T u v = 0 := by
  have hT' := ha.trans hT
  have hlarge : 1 < |T * (v - u)| := by
    rw [abs_mul, abs_of_pos hT']
    have h₁ : 1 < T * (1 / a) := by
      rw [mul_one_div]
      exact (lt_div_iff₀ ha).2 (by simpa only [one_mul] using hT)
    exact h₁.trans_le (mul_le_mul_of_nonneg_left hgap hT'.le)
  have hz : F (T * (v - u)) = 0 := by
    by_contra h
    exact (not_le_of_gt hlarge) (abs_le.mpr (hF (Function.mem_support.mpr h)))
  simp [frequencyTest, hz]

/-- The positive log-prime argument can meet the band only at an exact ratio. -/
theorem positive_log_test_eq_zero {F : ℝ → ℂ}
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) {n m k : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) {T : ℝ} (hT : (n : ℝ) + 1 < T)
    (hne : n ≠ m * k) :
    frequencyTest F T (logRatio n m) (Real.log k) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : Real.log k - logRatio n m = Real.log (m * k : ℕ) - Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hmR hkR, logRatio]
    ring
  apply frequencyTest_eq_zero_of_gap hF (by positivity) hT
  rw [he]
  exact log_gap_nat n (m * k) hn (Nat.mul_pos hm hk) hne

/-- The negative log-prime argument isolates the reciprocal exact ratio. -/
theorem negative_log_test_eq_zero {F : ℝ → ℂ}
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) {n m k : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) {T : ℝ} (hT : (m : ℝ) + 1 < T)
    (hne : m ≠ n * k) :
    frequencyTest F T (logRatio n m) (-Real.log k) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : -Real.log k - logRatio n m = -(Real.log (n * k : ℕ) - Real.log m) := by
    rw [Nat.cast_mul, Real.log_mul hnR hkR, logRatio]
    ring
  apply frequencyTest_eq_zero_of_gap hF (by positivity) hT
  rw [he, abs_neg]
  exact log_gap_nat m (n * k) hm (Nat.mul_pos hn hk) hne

private theorem quotient_series (n m : ℕ) (hm : 0 < m) (a : ℕ → ℂ)
    (hvan : ∀ k, n ≠ m * k → a k = 0) :
    Summable a ∧ (∑' k, a k) = if m ∣ n then a (n / m) else 0 := by
  by_cases hd : m ∣ n
  · have he : m * (n / m) = n := by rw [Nat.mul_comm, Nat.div_mul_cancel hd]
    have hs : HasSum a (a (n / m)) := by
      apply hasSum_single
      intro k hk
      apply hvan
      intro h
      apply hk
      exact Nat.eq_of_mul_eq_mul_left hm (h.symm.trans he.symm)
    exact ⟨hs.summable, by rw [if_pos hd]; exact hs.tsum_eq⟩
  · have hzero : a = 0 := funext (fun k => hvan k (fun h => hd ⟨k, h⟩))
    rw [hzero, if_neg hd]
    exact ⟨summable_zero, tsum_zero⟩

private theorem positive_resonance_value (F : ℝ → ℂ) (T : ℝ) {n m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (h : n = m * k) :
    ((Λ k / Real.sqrt k : ℝ) : ℂ) * frequencyTest F T (logRatio n m) (Real.log k) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (ratioWeight k : ℂ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : Real.log k - logRatio n m = 0 := by
    rw [logRatio, h, Nat.cast_mul, Real.log_mul hmR hkR]
    ring
  simp only [frequencyTest, he, mul_zero, ratioWeight, Complex.ofReal_mul]
  ring

private theorem negative_resonance_value (F : ℝ → ℂ) (T : ℝ) {n m k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (h : m = n * k) :
    ((Λ k / Real.sqrt k : ℝ) : ℂ) * frequencyTest F T (logRatio n m) (-Real.log k) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (ratioWeight k : ℂ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : -Real.log k - logRatio n m = 0 := by
    rw [logRatio, h, Nat.cast_mul, Real.log_mul hnR hkR]
    ring
  simp only [frequencyTest, he, mul_zero, ratioWeight, Complex.ofReal_mul, neg_div,
    Real.cosh_neg]
  ring

/-- Exact prime sum in the band. All nonresonant terms are zero. -/
theorem prime_sum_eq_resonance {F : ℝ → ℂ}
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {T : ℝ}
    (hTn : (n : ℝ) + 1 < T) (hTm : (m : ℝ) + 1 < T) :
    (∑' k : ℕ, ((Λ k / Real.sqrt k : ℝ) : ℂ) *
      (frequencyTest F T (logRatio n m) (Real.log k) +
        frequencyTest F T (logRatio n m) (-Real.log k))) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (resonance n m : ℂ) := by
  let p (k : ℕ) := ((Λ k / Real.sqrt k : ℝ) : ℂ) *
    frequencyTest F T (logRatio n m) (Real.log k)
  let q (k : ℕ) := ((Λ k / Real.sqrt k : ℝ) : ℂ) *
    frequencyTest F T (logRatio n m) (-Real.log k)
  have hp := quotient_series n m hm p (fun k hne => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [p]
    · simp [p, positive_log_test_eq_zero hF hn hm hk hTn hne])
  have hq := quotient_series m n hn q (fun k hne => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [q]
    · simp [q, negative_log_test_eq_zero hF hn hm hk hTm hne])
  have he₁ : (∑' k, p k) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (directionalResonance n m : ℂ) := by
    rw [hp.2, directionalResonance]
    by_cases h : m ∣ n
    · rw [if_pos h, if_pos h]
      have he : n = m * (n / m) := by rw [Nat.mul_comm, Nat.div_mul_cancel h]
      have hk : 0 < n / m := Nat.pos_of_ne_zero (fun hz =>
        hn.ne' (by simpa [hz] using he))
      exact positive_resonance_value F T hm hk he
    · simp [h]
  have he₂ : (∑' k, q k) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (directionalResonance m n : ℂ) := by
    rw [hq.2, directionalResonance]
    by_cases h : n ∣ m
    · rw [if_pos h, if_pos h]
      have he : m = n * (m / n) := by rw [Nat.mul_comm, Nat.div_mul_cancel h]
      have hk : 0 < m / n := Nat.pos_of_ne_zero (fun hz =>
        hm.ne' (by simpa [hz] using he))
      exact negative_resonance_value F T hn hk he
    · simp [h]
  have he : (∑' k : ℕ, (p k + q k)) =
      ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (resonance n m : ℂ) := by
    rw [hp.1.tsum_add hq.1, he₁, he₂, resonance, Complex.ofReal_add, mul_add]
  simpa only [p, q, mul_add] using he

/-- The exact compact Weil identity for the actual zeros, with only the
resonant prime coefficient on the arithmetic side. -/
theorem actual_zero_sum_eq_resonance {F : ℝ → ℂ} (hFd : ContDiff ℝ 2 F)
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {T : ℝ}
    (hTn : (n : ℝ) + 1 < T) (hTm : (m : ℝ) + 1 < T) :
    let k := frequencyTest F T (logRatio n m)
    Summable (fun ρ : (zetaZeros zetaSeam).carrier =>
      ((zetaZeros zetaSeam).mult ρ : ℂ) * paperFT k (gammaOf ρ)) ∧
    (∑' ρ : (zetaZeros zetaSeam).carrier,
      ((zetaZeros zetaSeam).mult ρ : ℂ) * paperFT k (gammaOf ρ)) =
      paperFT k (Complex.I / 2) + paperFT k (-Complex.I / 2) -
        ((T / (2 * Real.pi) : ℝ) : ℂ) * F 0 * (resonance n m : ℂ) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
  dsimp only
  have hT : 0 < T := (by positivity : 0 < (n : ℝ) + 1).trans hTn
  obtain ⟨hs, he⟩ := WeilEF.EF_lit_zeta zetaSeam _ (frequencyTest_contDiff hFd T _)
    (frequencyTest_compact hF hT _)
  refine ⟨hs, ?_⟩
  rw [he, EF.literatureRHS, prime_sum_eq_resonance hF hn hm hTn hTm]

end RiemannResearch.Analysis.PrimeBandlimitedWeil
