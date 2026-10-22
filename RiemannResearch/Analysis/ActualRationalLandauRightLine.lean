import RiemannResearch.Analysis.FiniteOscillatoryKernel
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp

/-!
# The actual finite right line in rational Landau's formula

The actual zeta identification and summability come from Mathlib's proved
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and
`ArithmeticFunction.LSeriesSummable_vonMangoldt`. The finite signed-interval
interchange is Mathlib's interval dominated convergence theorem. The exact
finite phase kernel and rational separation are the checked project module
`FiniteOscillatoryKernel` at commit 9aad406.

All signed endpoints and resonant terms are retained. This supplies the
actual right vertical side only, not the complete Landau contour estimate.
The classical intended contour strategy is Ford--Zaharescu, Lemma 1,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf.
-/

open Complex MeasureTheory Set
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace RiemannResearch.Analysis.ZeroOrdinate

/-- Actual von Mangoldt coefficients on Re s = 2. The zero index is exactly zero. -/
def mangoldtSquareCoeff (k : ℕ) : ℝ := (Λ k : ℝ) / (k : ℝ) ^ 2

theorem mangoldtSquareCoeff_nonneg (k : ℕ) : 0 ≤ mangoldtSquareCoeff k :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)

@[simp] theorem mangoldtSquareCoeff_zero : mangoldtSquareCoeff 0 = 0 := by
  simp [mangoldtSquareCoeff]

@[simp] theorem mangoldtSquareCoeff_one : mangoldtSquareCoeff 1 = 0 := by
  simp [mangoldtSquareCoeff, ArithmeticFunction.vonMangoldt_apply_one]

/-- Exact actual coefficient, including k=0; no real rpow estimate is involved. -/
theorem vonMangoldt_term_two_eq (k : ℕ) :
    LSeries.term (fun j => (Λ j : ℂ)) (2 : ℂ) k = (mangoldtSquareCoeff k : ℂ) := by
  rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_two]
  simp only [mangoldtSquareCoeff, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]

/-- An instantiated actual arithmetic summability provider, not a new hypothesis. -/
theorem summable_mangoldtSquareCoeff : Summable mangoldtSquareCoeff := by
  have hs : LSeriesSummable (fun j => (Λ j : ℂ)) (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hns : Summable (fun k : ℕ =>
      ‖LSeries.term (fun j => (Λ j : ℂ)) (2 : ℂ) k‖) :=
    summable_norm_iff.mpr hs
  refine hns.congr fun k => ?_
  rw [vonMangoldt_term_two_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mangoldtSquareCoeff_nonneg k)]

/-- Full signed actual coefficient total on Re s=2. -/
theorem tsum_mangoldtSquareCoeff_eq :
    (∑' k : ℕ, mangoldtSquareCoeff k : ℝ) =
      (-(logDeriv riemannZeta (2 : ℂ))).re := by
  have hactual : -logDeriv riemannZeta (2 : ℂ) =
      LSeries (fun j => (Λ j : ℂ)) (2 : ℂ) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by norm_num : 1 < (2 : ℂ).re)
    rw [logDeriv, Pi.div_apply, h]
    ring
  have hcast : (∑' k : ℕ, (mangoldtSquareCoeff k : ℂ)) =
      -logDeriv riemannZeta (2 : ℂ) := by
    rw [hactual, LSeries]
    exact tsum_congr fun k => (vonMangoldt_term_two_eq k).symm
  have h := congrArg Complex.re hcast
  rw [← Complex.ofReal_tsum mangoldtSquareCoeff] at h
  simpa only [Complex.ofReal_re] using h

/-- Exact phase factorization of the actual Dirichlet-series term on Re s=2. -/
theorem vonMangoldt_term_two_line (k : ℕ) (t : ℝ) :
    LSeries.term (fun j => (Λ j : ℂ)) ((2 : ℂ) + t * I) k =
      (mangoldtSquareCoeff k : ℂ) *
        Complex.exp (-I * (t : ℂ) * (Real.log k : ℂ)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hsplit : -((2 : ℂ) + t * I) = -(2 : ℂ) + -(I * t) := by ring
  have htwo : (k : ℂ) ^ (-(2 : ℂ)) = ((k : ℂ) ^ 2)⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_two]
  have hphase : (k : ℂ) ^ (-(I * t)) =
      Complex.exp (-I * (t : ℂ) * (Real.log k : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hkC]
    congr 1
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hk0.le]
    ring
  rw [LSeries.term_of_ne_zero hk, div_eq_mul_inv, ← Complex.cpow_neg,
    hsplit, Complex.cpow_add _ _ hkC, htwo, hphase]
  have hc : (mangoldtSquareCoeff k : ℂ) = (Λ k : ℂ) / (k : ℂ) ^ 2 := by
    simp only [mangoldtSquareCoeff, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast]
  rw [hc, div_eq_mul_inv]
  ring

/-- Exact centered exponential on the right vertical line. -/
theorem centered_exp_two_line (u t : ℝ) :
    Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) =
      (Real.exp (3 * u / 2) : ℂ) * Complex.exp (((u : ℂ) * I) * (t : ℂ)) := by
  have he : (u : ℂ) * ((2 : ℂ) + t * I - 1 / 2) =
      ((3 * u / 2 : ℝ) : ℂ) + ((u : ℂ) * I) * (t : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]

/-- Exact weighted per-k integrand, with its future resonance frequency visible. -/
theorem centered_exp_mul_vonMangoldt_term_two_line (u t : ℝ) (k : ℕ) :
    Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) *
        LSeries.term (fun j => (Λ j : ℂ)) ((2 : ℂ) + t * I) k =
      (Real.exp (3 * u / 2) : ℂ) * (mangoldtSquareCoeff k : ℂ) *
        Complex.exp ((((u - Real.log k : ℝ) : ℂ) * I) * (t : ℂ)) := by
  rw [centered_exp_two_line, vonMangoldt_term_two_line]
  have he : ((u : ℂ) * I) * (t : ℂ) +
      (-I * (t : ℂ) * (Real.log k : ℂ)) =
      (((u - Real.log k : ℝ) : ℂ) * I) * (t : ℂ) := by
    push_cast
    ring
  calc
    _ = (Real.exp (3 * u / 2) : ℂ) * (mangoldtSquareCoeff k : ℂ) *
        (Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          Complex.exp (-I * (t : ℂ) * (Real.log k : ℂ))) := by ring
    _ = _ := by rw [← Complex.exp_add, he]

/-- Actual zeta identification, before integration. -/
theorem centered_two_neg_logDeriv_eq_tsum (u t : ℝ) :
    Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) *
        (-logDeriv riemannZeta ((2 : ℂ) + t * I)) =
      ∑' k : ℕ, (Real.exp (3 * u / 2) : ℂ) * (mangoldtSquareCoeff k : ℂ) *
        Complex.exp ((((u - Real.log k : ℝ) : ℂ) * I) * (t : ℂ)) := by
  have hactual : -logDeriv riemannZeta ((2 : ℂ) + t * I) =
      LSeries (fun j => (Λ j : ℂ)) ((2 : ℂ) + t * I) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by simp : 1 < ((2 : ℂ) + t * I).re)
    rw [logDeriv, Pi.div_apply, h]
    ring
  rw [hactual, LSeries, ← tsum_mul_left]
  exact tsum_congr fun k => centered_exp_mul_vonMangoldt_term_two_line u t k

/-- Genuine finite signed-interval interchange for the actual right zeta line.
No ordering of the endpoints and no compact-test hypothesis are needed. -/
theorem integral_centered_two_neg_logDeriv_eq_kernel_tsum (A B u : ℝ) :
    (∫ t in A..B,
      Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) *
        (-logDeriv riemannZeta ((2 : ℂ) + t * I))) =
      (Real.exp (3 * u / 2) : ℂ) *
        ∑' k : ℕ, (mangoldtSquareCoeff k : ℂ) *
          finitePhaseKernel A B (u - Real.log k) := by
  let M : ℝ := Real.exp (3 * u / 2)
  let F : ℕ → ℝ → ℂ := fun k t =>
    (M : ℂ) * (mangoldtSquareCoeff k : ℂ) *
      Complex.exp ((((u - Real.log k : ℝ) : ℂ) * I) * (t : ℂ))
  have hM : 0 < M := Real.exp_pos _
  have hphase : ∀ (ω t : ℝ), ‖Complex.exp (((ω : ℂ) * I) * (t : ℂ))‖ = 1 := by
    intro ω t
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ (k : ℕ) (t : ℝ), ‖F k t‖ = M * mangoldtSquareCoeff k := by
    intro k t
    simp only [F, norm_mul, hphase, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hM, abs_of_nonneg (mangoldtSquareCoeff_nonneg k), mul_one]
  have hsum : Summable (fun k : ℕ => M * mangoldtSquareCoeff k) :=
    summable_mangoldtSquareCoeff.mul_left M
  have hsumF : ∀ t : ℝ, Summable (fun k : ℕ => F k t) := by
    intro t
    exact hsum.of_norm_bounded (fun k => (hnorm k t).le)
  have hswap : HasSum (fun k : ℕ => ∫ t in A..B, F k t)
      (∫ t in A..B, ∑' k : ℕ, F k t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k (_ : ℝ) => M * mangoldtSquareCoeff k)
      (fun k => (show Continuous (F k) by dsimp [F]; fun_prop).aestronglyMeasurable)
    · intro k
      exact Filter.Eventually.of_forall fun t _ => (hnorm k t).le
    · exact Filter.Eventually.of_forall fun _ _ => hsum
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => (hsumF t).hasSum
  have heval : ∀ k : ℕ, (∫ t in A..B, F k t) =
      (M : ℂ) * (mangoldtSquareCoeff k : ℂ) *
        finitePhaseKernel A B (u - Real.log k) := by
    intro k
    dsimp [F]
    rw [intervalIntegral.integral_const_mul,
      integral_phase_eq_finitePhaseKernel]
  calc
    _ = ∫ t in A..B, ∑' k : ℕ, F k t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact centered_two_neg_logDeriv_eq_tsum u t
    _ = ∑' k : ℕ, ∫ t in A..B, F k t := hswap.tsum_eq.symm
    _ = _ := by
      simp_rw [heval, mul_assoc]
      rw [tsum_mul_left]

/-- The signed right vertical side in the zeta argument principle. -/
def rightLandauLine (A B u : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in A..B,
      Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) *
        logDeriv riemannZeta ((2 : ℂ) + t * I)

/-- Exact signed right-line formula. The minus sign of the prime contribution
is retained for subsequent contour assembly. -/
theorem rightLandauLine_eq_kernel_tsum (A B u : ℝ) :
    rightLandauLine A B u =
      -((Real.exp (3 * u / 2) / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' k : ℕ, (mangoldtSquareCoeff k : ℂ) *
          finitePhaseKernel A B (u - Real.log k) := by
  have he : (fun t : ℝ =>
      Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) *
        logDeriv riemannZeta ((2 : ℂ) + t * I)) =
    fun t : ℝ => -(Complex.exp ((u : ℂ) * ((2 : ℂ) + t * I - 1 / 2)) *
        (-logDeriv riemannZeta ((2 : ℂ) + t * I))) := by
    funext t
    ring
  rw [rightLandauLine, he, intervalIntegral.integral_neg,
    integral_centered_two_neg_logDeriv_eq_kernel_tsum]
  push_cast
  ring

/-- The rational kernel series term before its exact resonance split. -/
def rationalMangoldtPhaseTerm (n m : ℕ) (A B : ℝ) (k : ℕ) : ℂ :=
  (mangoldtSquareCoeff k : ℂ) * finitePhaseKernel A B
    (Real.log ((n : ℝ) / (m : ℝ)) - Real.log (k : ℝ))

/-- Actual resonance is n=m*k; it is not the floor index unless m divides n. -/
def rationalMangoldtResonantTerm (n m : ℕ) (A B : ℝ) (k : ℕ) : ℂ :=
  if n = m * k then (mangoldtSquareCoeff k : ℂ) * ((B - A : ℝ) : ℂ) else 0

def rationalMangoldtNonresonantTerm (n m : ℕ) (A B : ℝ) (k : ℕ) : ℂ :=
  if n = m * k then 0 else rationalMangoldtPhaseTerm n m A B k

theorem norm_rationalMangoldtNonresonantTerm_le {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) (k : ℕ) :
    ‖rationalMangoldtNonresonantTerm n m A B k‖ ≤
      (4 * (n : ℝ)) * mangoldtSquareCoeff k := by
  classical
  by_cases hr : n = m * k
  · simp only [rationalMangoldtNonresonantTerm, if_pos hr, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (mangoldtSquareCoeff_nonneg k)
  · by_cases hk : k = 0
    · subst k
      simp [rationalMangoldtNonresonantTerm, rationalMangoldtPhaseTerm]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hc : ‖(mangoldtSquareCoeff k : ℂ)‖ = mangoldtSquareCoeff k := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mangoldtSquareCoeff_nonneg k)]
      rw [rationalMangoldtNonresonantTerm, if_neg hr,
        rationalMangoldtPhaseTerm, norm_mul, hc]
      calc
        _ ≤ mangoldtSquareCoeff k * (4 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (norm_finitePhaseKernel_rational_le hn hm hk1 hr A B)
            (mangoldtSquareCoeff_nonneg k)
        _ = (4 * (n : ℝ)) * mangoldtSquareCoeff k := mul_comm _ _

theorem summable_rationalMangoldtNonresonantTerm {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    Summable (rationalMangoldtNonresonantTerm n m A B) :=
  (summable_mangoldtSquareCoeff.mul_left (4 * (n : ℝ))).of_norm_bounded
    (norm_rationalMangoldtNonresonantTerm_le hn hm A B)

theorem norm_tsum_rationalMangoldtNonresonantTerm_le {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    ‖∑' k, rationalMangoldtNonresonantTerm n m A B k‖ ≤
      (4 * (n : ℝ)) * ∑' k, mangoldtSquareCoeff k :=
  tsum_of_norm_bounded
    (summable_mangoldtSquareCoeff.hasSum.mul_left (4 * (n : ℝ)))
    (norm_rationalMangoldtNonresonantTerm_le hn hm A B)

theorem summable_rationalMangoldtResonantTerm (n m : ℕ) (A B : ℝ) :
    Summable (rationalMangoldtResonantTerm n m A B) := by
  classical
  have hc : Summable (fun k : ℕ =>
      (mangoldtSquareCoeff k : ℂ) * ((B - A : ℝ) : ℂ)) :=
    (Complex.summable_ofReal.mpr summable_mangoldtSquareCoeff).mul_right
      ((B - A : ℝ) : ℂ)
  refine (hc.indicator {k : ℕ | n = m * k}).congr fun k => ?_
  by_cases hr : n = m * k
  · simp [Set.indicator, rationalMangoldtResonantTerm, hr]
  · simp [Set.indicator, rationalMangoldtResonantTerm, hr]

theorem rationalMangoldtPhaseTerm_eq_split {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) (k : ℕ) :
    rationalMangoldtPhaseTerm n m A B k =
      rationalMangoldtResonantTerm n m A B k +
        rationalMangoldtNonresonantTerm n m A B k := by
  classical
  by_cases hr : n = m * k
  · have hk0 : k ≠ 0 := by
      intro hk
      exact (Nat.one_le_iff_ne_zero.mp hn) (by simpa [hk] using hr)
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    simp only [rationalMangoldtResonantTerm, rationalMangoldtNonresonantTerm,
      if_pos hr, add_zero]
    rw [rationalMangoldtPhaseTerm,
      finitePhaseKernel_rational_resonance hn hm hk1 hr A B]
  · simp [rationalMangoldtResonantTerm, rationalMangoldtNonresonantTerm, hr]

theorem summable_rationalMangoldtPhaseTerm {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    Summable (rationalMangoldtPhaseTerm n m A B) :=
  ((summable_rationalMangoldtResonantTerm n m A B).add
    (summable_rationalMangoldtNonresonantTerm hn hm A B)).congr
    (fun k => (rationalMangoldtPhaseTerm_eq_split hn hm A B k).symm)

theorem tsum_rationalMangoldtPhaseTerm_eq_split {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    (∑' k, rationalMangoldtPhaseTerm n m A B k) =
      (∑' k, rationalMangoldtResonantTerm n m A B k) +
        ∑' k, rationalMangoldtNonresonantTerm n m A B k := by
  calc
    _ = ∑' k, (rationalMangoldtResonantTerm n m A B k +
        rationalMangoldtNonresonantTerm n m A B k) :=
      tsum_congr (rationalMangoldtPhaseTerm_eq_split hn hm A B)
    _ = _ := (summable_rationalMangoldtResonantTerm n m A B).tsum_add
      (summable_rationalMangoldtNonresonantTerm hn hm A B)

theorem tsum_rationalMangoldtResonantTerm_eq {n m : ℕ}
    (hm : 1 ≤ m) (A B : ℝ) :
    (∑' k, rationalMangoldtResonantTerm n m A B k) =
      if m ∣ n then (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ)
      else 0 := by
  classical
  by_cases hd : m ∣ n
  · rw [if_pos hd]
    let q : ℕ := n / m
    have hnq : n = m * q := by
      simpa [q, Nat.mul_comm] using (Nat.div_mul_cancel hd).symm
    have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    have hunique : ∀ k : ℕ, k ≠ q → n ≠ m * k := by
      intro k hk hr
      apply hk
      exact Nat.eq_of_mul_eq_mul_left hm0 (hr.symm.trans hnq)
    change (∑' k, rationalMangoldtResonantTerm n m A B k) =
      (mangoldtSquareCoeff q : ℂ) * ((B - A : ℝ) : ℂ)
    calc
      _ = rationalMangoldtResonantTerm n m A B q :=
        tsum_eq_single q (by
          intro k hk
          simp [rationalMangoldtResonantTerm, hunique k hk])
      _ = _ := by simp [rationalMangoldtResonantTerm, hnq]
  · rw [if_neg hd]
    have hz : rationalMangoldtResonantTerm n m A B = (fun _ : ℕ => (0 : ℂ)) := by
      funext k
      have hr : n ≠ m * k := fun h => hd ⟨k, h⟩
      simp [rationalMangoldtResonantTerm, hr]
    rw [hz]
    simp only [tsum_zero]

theorem tsum_rationalMangoldtPhaseTerm_eq_divisor_split {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    (∑' k, rationalMangoldtPhaseTerm n m A B k) =
      (if m ∣ n then
        (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ) else 0) +
        ∑' k, rationalMangoldtNonresonantTerm n m A B k := by
  rw [tsum_rationalMangoldtPhaseTerm_eq_split hn hm A B,
    tsum_rationalMangoldtResonantTerm_eq hm A B]

theorem norm_tsum_rationalMangoldtPhaseTerm_sub_resonance_le {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    ‖(∑' k, rationalMangoldtPhaseTerm n m A B k) -
      (if m ∣ n then
        (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ) else 0)‖ ≤
      (4 * (n : ℝ)) * ∑' k, mangoldtSquareCoeff k := by
  rw [tsum_rationalMangoldtPhaseTerm_eq_divisor_split hn hm A B,
    add_sub_cancel_left]
  exact norm_tsum_rationalMangoldtNonresonantTerm_le hn hm A B

/-- Actual signed right line with complete resonant and nonresonant summands. -/
theorem rightLandauLine_rational_eq_split {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) =
      -((Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) /
          (2 * Real.pi) : ℝ) : ℂ) *
        ((if m ∣ n then
          (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ) else 0) +
          ∑' k, rationalMangoldtNonresonantTerm n m A B k) := by
  rw [rightLandauLine_eq_kernel_tsum]
  congr 1
  exact tsum_rationalMangoldtPhaseTerm_eq_divisor_split hn hm A B

/-- An actual right-line error estimate uniform in both height endpoints.
No zero-density, full-contour Landau, or RH hypothesis appears. -/
theorem norm_rightLandauLine_rational_add_resonance_le {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    ‖rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) +
      ((Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) /
          (2 * Real.pi) : ℝ) : ℂ) *
        (if m ∣ n then
          (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ) else 0)‖ ≤
      (Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) / (2 * Real.pi)) *
        ((4 * (n : ℝ)) * ∑' k, mangoldtSquareCoeff k) := by
  let c : ℝ := Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) / (2 * Real.pi)
  have hc : 0 ≤ c := div_nonneg (Real.exp_pos _).le (by positivity)
  have he : rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) +
      (c : ℂ) * (if m ∣ n then
        (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ) else 0) =
      -(c : ℂ) * ∑' k, rationalMangoldtNonresonantTerm n m A B k := by
    rw [rightLandauLine_rational_eq_split hn hm A B]
    dsimp [c]
    ring
  change ‖rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) +
    (c : ℂ) * (if m ∣ n then
      (mangoldtSquareCoeff (n / m) : ℂ) * ((B - A : ℝ) : ℂ) else 0)‖ ≤
      c * ((4 * (n : ℝ)) * ∑' k, mangoldtSquareCoeff k)
  rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (norm_tsum_rationalMangoldtNonresonantTerm_le hn hm A B) hc

end RiemannResearch.Analysis.ZeroOrdinate
