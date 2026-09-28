import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual conductor symbols and their common zeros

Formalization of Section 10.4 of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.

This file concerns the actual entire factors `P_n(s) = 1/n - exp(-s log n)`.
It does not assume RH or any logarithm-irrationality hypothesis. The proof of
the two-conductor assertion reduces integer logarithm relations to natural
power equality and uses `2 ∤ 3`.

-/

noncomputable section

namespace RiemannResearch.RH.ArithmeticConductorCommonZeros

open Complex

/-- The exact entire conductor factor in the Mellin multiplier. -/
def conductorSymbol (n : ℕ) (s : ℂ) : ℂ :=
  (n : ℂ)⁻¹ - Complex.exp (-s * (Real.log n : ℂ))

private theorem exp_neg_log_nat (n : ℕ) (hn : 0 < n) :
    Complex.exp (-(Real.log n : ℂ)) = (n : ℂ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hnR]
  simp only [Complex.ofReal_natCast]

theorem conductorSymbol_one (n : ℕ) (hn : 0 < n) :
    conductorSymbol n 1 = 0 := by
  simp only [conductorSymbol, neg_one_mul, exp_neg_log_nat n hn, sub_self]

/-- Every zero has the exact integer phase prescribed by its conductor. -/
theorem conductorSymbol_zero_iff_phase (n : ℕ) (hn : 1 < n) (s : ℂ) :
    conductorSymbol n s = 0 ↔
      ∃ k : ℤ, (s - 1) * (Real.log n : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  constructor
  · intro h
    have he : Complex.exp (-s * (Real.log n : ℂ)) =
        Complex.exp (-(Real.log n : ℂ)) :=
      (sub_eq_zero.mp h).symm.trans (exp_neg_log_nat n hn0).symm
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    refine ⟨-k, ?_⟩
    simp only [Int.cast_neg]
    linear_combination -hk
  · rintro ⟨k, hk⟩
    have he : Complex.exp (-s * (Real.log n : ℂ)) =
        Complex.exp (-(Real.log n : ℂ)) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨-k, ?_⟩
      simp only [Int.cast_neg]
      linear_combination -hk
    unfold conductorSymbol
    rw [he, exp_neg_log_nat n hn0, sub_self]

/-- All artificial conductor zeros lie on the line with real part one. -/
theorem conductorSymbol_zero_re (n : ℕ) (hn : 1 < n) (s : ℂ)
    (hs : conductorSymbol n s = 0) : s.re = 1 := by
  obtain ⟨k, hk⟩ := (conductorSymbol_zero_iff_phase n hn s).mp hs
  have hr : (s.re - 1) * Real.log n = 0 := by
    have h := congrArg Complex.re hk
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero] at h
    exact h
  have hlog : Real.log n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hlog)

/-- In particular a zeta zero in the open critical strip is not a conductor zero. -/
theorem conductorSymbol_ne_zero_of_re_ne_one (n : ℕ) (hn : 1 < n) (s : ℂ)
    (hs : s.re ≠ 1) : conductorSymbol n s ≠ 0 :=
  fun h => hs (conductorSymbol_zero_re n hn s h)

/-- The explicit lattice of zeros responsible for the single-conductor obstruction. -/
theorem conductorSymbol_explicit_zero (n : ℕ) (hn : 1 < n) (k : ℤ) :
    conductorSymbol n
      (1 + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
        (Real.log n : ℂ)) = 0 := by
  apply (conductorSymbol_zero_iff_phase n hn _).mpr
  refine ⟨k, ?_⟩
  have hlog : (Real.log n : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      ((Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).ne')
  calc
    ((1 + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
        (Real.log n : ℂ)) - 1) * (Real.log n : ℂ) =
      ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
        (Real.log n : ℂ)) * (Real.log n : ℂ) := by ring
    _ = _ := div_mul_cancel₀ _ hlog

/-- A nonzero phase gives an artificial zero distinct from the removable point. -/
theorem conductorSymbol_extra_zero_ne_one (n : ℕ) (hn : 1 < n) (k : ℤ)
    (hk : k ≠ 0) :
    1 + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
      (Real.log n : ℂ) ≠ 1 := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hlog : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      ((Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)).ne')
  have hterm : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
      (Real.log n : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero hkC Complex.two_pi_I_ne_zero) hlog
  intro heq
  apply hterm
  linear_combination heq

private theorem nat_log_relation (k l : ℕ)
    (h : (k : ℝ) * Real.log 3 = (l : ℝ) * Real.log 2) :
    k = 0 ∧ l = 0 := by
  have hpowR : (3 : ℝ) ^ k = (2 : ℝ) ^ l := by
    apply Real.log_injOn_pos
      (pow_pos (by norm_num : (0 : ℝ) < 3) k)
      (pow_pos (by norm_num : (0 : ℝ) < 2) l)
    simpa only [Real.log_pow] using h
  have hpowN : (3 : ℕ) ^ k = (2 : ℕ) ^ l := by
    exact_mod_cast hpowR
  have hl : l = 0 := by
    cases l with
    | zero => rfl
    | succ l =>
      have hd : 2 ∣ (3 : ℕ) ^ k := by
        rw [hpowN, pow_succ]
        exact dvd_mul_left _ _
      have hbad : 2 ∣ (3 : ℕ) := Nat.prime_two.dvd_of_dvd_pow hd
      norm_num at hbad
  have hk : k = 0 := by
    have hlog3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
    rw [hl, Nat.cast_zero, zero_mul] at h
    have hkR : (k : ℝ) = 0 := (mul_eq_zero.mp h).resolve_right hlog3
    exact_mod_cast hkR
  exact ⟨hk, hl⟩

/-- No nontrivial integer relation joins the two logarithms. -/
theorem integer_log_relation (k l : ℤ)
    (h : (k : ℝ) * Real.log 3 = (l : ℝ) * Real.log 2) :
    k = 0 ∧ l = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hka : (k.natAbs : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hla : (l.natAbs : ℝ) = |(l : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have habs : (k.natAbs : ℝ) * Real.log 3 =
      (l.natAbs : ℝ) * Real.log 2 := by
    rw [hka, hla]
    simpa only [abs_mul, abs_of_pos hlog2, abs_of_pos hlog3] using congrArg abs h
  obtain ⟨hk, hl⟩ := nat_log_relation k.natAbs l.natAbs habs
  exact ⟨Int.natAbs_eq_zero.mp hk, Int.natAbs_eq_zero.mp hl⟩

/-- Conductors two and three have exactly one common artificial zero. -/
theorem conductorSymbol_two_three_common_zero_iff (s : ℂ) :
    (conductorSymbol 2 s = 0 ∧ conductorSymbol 3 s = 0) ↔ s = 1 := by
  constructor
  · rintro ⟨h2, h3⟩
    obtain ⟨k, hk⟩ := (conductorSymbol_zero_iff_phase 2 (by norm_num) s).mp h2
    obtain ⟨l, hl⟩ := (conductorSymbol_zero_iff_phase 3 (by norm_num) s).mp h3
    have hi2 : s.im * Real.log 2 = (k : ℝ) * (2 * Real.pi) := by
      have h := congrArg Complex.im hk
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
        show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add] at h
      exact h
    have hi3 : s.im * Real.log 3 = (l : ℝ) * (2 * Real.pi) := by
      have h := congrArg Complex.im hl
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
        show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add] at h
      exact h
    have hkl : (k : ℝ) * Real.log 3 = (l : ℝ) * Real.log 2 := by
      apply mul_right_cancel₀ (ne_of_gt Real.two_pi_pos)
      calc
        (k : ℝ) * Real.log 3 * (2 * Real.pi) =
            (s.im * Real.log 2) * Real.log 3 := by rw [hi2]; ring
        _ = (s.im * Real.log 3) * Real.log 2 := by ring
        _ = (l : ℝ) * Real.log 2 * (2 * Real.pi) := by rw [hi3]; ring
    obtain ⟨hk0, _⟩ := integer_log_relation k l hkl
    have him : s.im = 0 := by
      have hzero : s.im * Real.log 2 = 0 := by simpa [hk0] using hi2
      exact (mul_eq_zero.mp hzero).resolve_right ((Real.log_pos (by norm_num)).ne')
    apply Complex.ext
    · simpa using conductorSymbol_zero_re 2 (by norm_num) s h2
    · simpa using him
  · rintro rfl
    exact ⟨conductorSymbol_one 2 (by norm_num), conductorSymbol_one 3 (by norm_num)⟩

/-- Outside the removable point one, at least one actual conductor factor survives. -/
theorem conductorSymbol_two_or_three_ne_zero (s : ℂ) (hs : s ≠ 1) :
    conductorSymbol 2 s ≠ 0 ∨ conductorSymbol 3 s ≠ 0 := by
  classical
  by_cases h2 : conductorSymbol 2 s = 0
  · exact Or.inr fun h3 => hs ((conductorSymbol_two_three_common_zero_iff s).mp ⟨h2, h3⟩)
  · exact Or.inl h2

/-- Away from one, a shared factor accounts for all simultaneous product zeros.
Taking `z = riemannZeta s` gives the non-removable part of the common-zero claim.
This statement does not identify analytic vanishing orders or extend values at one. -/
theorem common_conductor_products_zero_iff (z s : ℂ) (hs : s ≠ 1) :
    (z * conductorSymbol 2 s = 0 ∧ z * conductorSymbol 3 s = 0) ↔ z = 0 := by
  constructor
  · rintro ⟨h2, h3⟩
    rcases conductorSymbol_two_or_three_ne_zero s hs with h2n | h3n
    · exact (mul_eq_zero.mp h2).resolve_right h2n
    · exact (mul_eq_zero.mp h3).resolve_right h3n
  · rintro rfl
    simp



/-- Equality of two conductor powers produces a zero of the translated
entire conductor symbol. -/
theorem conductorSymbol_shift_zero_of_cpow_eq
    (n : ℕ) (hn : 1 < n) (s t : ℂ)
    (h : (n : ℂ) ^ (-s) = (n : ℂ) ^ (-t)) :
    conductorSymbol n (1 + s - t) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn).ne'
  have he : Complex.exp (-s * (Real.log n : ℂ)) =
      Complex.exp (-t * (Real.log n : ℂ)) := by
    simpa only [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log,
      mul_comm] using h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  apply (conductorSymbol_zero_iff_phase n hn (1 + s - t)).mpr
  refine ⟨-k, ?_⟩
  simp only [Int.cast_neg]
  linear_combination -hk

/-- The pair of conductor powers at 2 and 3 determines the entire complex
Mellin parameter. No restriction to a vertical line is necessary. -/
theorem two_three_cpow_neg_injective :
    Function.Injective (fun s : ℂ => ((2 : ℂ) ^ (-s), (3 : ℂ) ^ (-s))) := by
  intro s t h
  have h2 : (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (-t) := congrArg Prod.fst h
  have h3 : (3 : ℂ) ^ (-s) = (3 : ℂ) ^ (-t) := congrArg Prod.snd h
  have hs : 1 + s - t = 1 :=
    (conductorSymbol_two_three_common_zero_iff (1 + s - t)).mp
      ⟨conductorSymbol_shift_zero_of_cpow_eq 2 (by norm_num) s t h2,
        conductorSymbol_shift_zero_of_cpow_eq 3 (by norm_num) s t h3⟩
  linear_combination hs

end RiemannResearch.RH.ArithmeticConductorCommonZeros
