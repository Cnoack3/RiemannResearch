import RiemannResearch.Analysis.RationalFrequencyHeightSeparation
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fourier estimates for a dyadic prime-orbit trace

The numerator and denominator of a mode have prime factors in the prescribed set.
The repository's integer-log separation therefore also separates these modes from
both signs of the logarithm of every outside prime.  The bound applies to the
whole finite Selberg prime polynomial, with constants uniform in the test.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open PrimeTorusHaar ZeroOrdinate

/-- Goldston, Theorem 8 (10.5), with moment parameter eight at height 2U. -/
def bandwidth (U : ℝ) : ℕ := ⌊(2 * U) ^ (1 / 8 : ℝ)⌋₊

def primesTo (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter Nat.Prime

def primeWeight (q : ℕ) : ℝ := Real.log q / (Real.pi * Real.sqrt q)

def frequency (r : ℕ × ℕ) : ℝ := Real.log r.1 - Real.log r.2

def probe (U : ℝ) (H : ℝ → ℝ) (v : ℝ) : ℂ :=
  ∫ t in U..2 * U, (H t : ℂ) * phase v t

/-- The transform of one height-dependent Fourier coefficient. -/
def coefficientIntegral (U : ℝ) (b : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ t in U..2 * U, b ((t - U) / U) * phase v t

def Supported (P : Finset ℕ) (n : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ n → q ∈ P

/-- The finite Fourier data of a real trace. All conditions involve the continuous
orbit and its coefficients. There is no sampling measure in these data. -/
structure FourierTrace (P : Finset ℕ) (U A : ℝ) (X : ℕ := bandwidth U) where
  modes : Finset (ℕ × ℕ)
  coeff : (ℕ × ℕ) → ℝ → ℂ
  H : ℝ → ℝ
  continuousH : Continuous H
  boundH : ∀ t ∈ Icc U (2 * U), |H t| ≤ A
  derivative : ℝ → ℝ
  continuousDerivative : Continuous derivative
  derives : ∀ t, HasDerivAt H (derivative t) t
  boundDerivative : ∀ t ∈ Icc U (2 * U), |derivative t| ≤ A
  size : modes.card ≤ X
  support : ∀ r ∈ modes, 0 < r.1 ∧ 0 < r.2 ∧ r.1 ≤ X ∧ r.2 ≤ X ∧
      Supported P r.1 ∧ Supported P r.2
  synthesis : ∀ v, probe U H v =
      ∑ r ∈ modes, coefficientIntegral U (coeff r) (frequency r + v)
  decay : ∀ r ∈ modes, ∀ v : ℝ, v ≠ 0 →
      ‖coefficientIntegral U (coeff r) v‖ ≤ A / |v|

def FourierTrace.zeroMode {P U A X} (b : FourierTrace P U A X) : ℂ :=
  ∑ r ∈ b.modes, if r.1 = r.2 then coefficientIntegral U (b.coeff r) 0 else 0

def FourierTrace.enlarge {P U A A' X Y} (b : FourierTrace P U A X)
    (hA : A ≤ A') (hX : X ≤ Y) : FourierTrace P U A' Y where
  modes := b.modes
  coeff := b.coeff
  H := b.H
  continuousH := b.continuousH
  boundH := fun t ht => (b.boundH t ht).trans hA
  derivative := b.derivative
  continuousDerivative := b.continuousDerivative
  derives := b.derives
  boundDerivative := fun t ht => (b.boundDerivative t ht).trans hA
  size := b.size.trans hX
  support := fun r hr => by
    obtain ⟨hn, hm, hnx, hmx, hnp, hmp⟩ := b.support r hr
    exact ⟨hn, hm, hnx.trans hX, hmx.trans hX, hnp, hmp⟩
  synthesis := b.synthesis
  decay := fun r hr v hv => (b.decay r hr v hv).trans
    (div_le_div_of_nonneg_right hA (abs_nonneg _))

theorem outside_log_gaps {P : Finset ℕ} {X n m q : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnX : n ≤ X) (hmX : m ≤ X)
    (hq : q.Prime) (hqX : q ≤ X) (hout : q ∉ P)
    (hnP : Supported P n) (hmP : Supported P m) :
    1 / (X : ℝ) ^ 2 ≤ |frequency (n, m) + Real.log q| ∧
      1 / (X : ℝ) ^ 2 ≤ |frequency (n, m) - Real.log q| := by
  have hx : 1 ≤ X := hn.trans_le hnX
  have ha : n * q ≠ m := by
    intro h
    exact hout (hmP q hq (h ▸ dvd_mul_left q n))
  have hb : n ≠ m * q := by
    intro h
    exact hout (hnP q hq (h ▸ dvd_mul_left q m))
  have h1 := RiemannResearch.Fourier.integerLog_separation_of_le
    (M := X * X) (Nat.mul_pos hn hq.pos) hm (Nat.mul_le_mul hnX hqX)
    (hmX.trans (by nlinarith)) ha
  have h2 := RiemannResearch.Fourier.integerLog_separation_of_le
    (M := X * X) hn (Nat.mul_pos hm hq.pos) (hnX.trans (by nlinarith))
    (Nat.mul_le_mul hmX hqX) hb
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  simp only [Nat.cast_mul, Real.log_mul hnr hqr, Real.log_mul hmr hqr] at h1 h2
  unfold frequency
  constructor
  · convert h1 using 1 <;> congr 1 <;> ring
  · convert h2 using 1 <;> congr 1 <;> ring

theorem probe_zero_error {P U A} (b : FourierTrace P U A) (hA : 0 ≤ A)
    (hX : 0 < bandwidth U) :
    ‖probe U b.H 0 - b.zeroMode‖ ≤ A * (bandwidth U : ℝ) ^ 2 := by
  classical
  rw [b.synthesis, FourierTrace.zeroMode, ← Finset.sum_sub_distrib]
  have hx : 0 < (bandwidth U : ℝ) := by exact_mod_cast hX
  calc
    _ ≤ ∑ r ∈ b.modes, ‖coefficientIntegral U (b.coeff r) (frequency r + 0) -
          (if r.1 = r.2 then coefficientIntegral U (b.coeff r) 0 else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ b.modes, A * (bandwidth U : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hn, hm, hnX, hmX, _, _⟩ := b.support r hr
      by_cases he : r.1 = r.2
      · simp [he, frequency, mul_nonneg hA hx.le]
      · have hg := RiemannResearch.Fourier.integerLog_separation_of_le hn hm hnX hmX he
        have hp : 0 < |frequency r| := lt_of_lt_of_le (one_div_pos.mpr hx) hg
        simp only [if_neg he, sub_zero, add_zero]
        apply (b.decay r hr _ (abs_pos.mp hp)).trans
        rw [div_le_iff₀ hp]
        have hh := (div_le_iff₀ hx).mp hg
        dsimp [frequency] at *
        nlinarith [mul_le_mul_of_nonneg_left hh hA]
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hsize : (b.modes.card : ℝ) ≤ bandwidth U := by exact_mod_cast b.size
      nlinarith [mul_le_mul_of_nonneg_right hsize (mul_nonneg hA hx.le)]

theorem probe_outside {P U A} (b : FourierTrace P U A) (hA : 0 ≤ A)
    {q : ℕ} (hq : q.Prime) (hqX : q ≤ bandwidth U) (hout : q ∉ P) :
    ‖probe U b.H (Real.log q)‖ ≤ A * (bandwidth U : ℝ) ^ 3 := by
  have hx : 0 < (bandwidth U : ℝ) := by exact_mod_cast hq.pos.trans_le hqX
  rw [b.synthesis]
  calc
    _ ≤ ∑ r ∈ b.modes, ‖coefficientIntegral U (b.coeff r) (frequency r + Real.log q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ b.modes, A * (bandwidth U : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hn, hm, hnX, hmX, hnP, hmP⟩ := b.support r hr
      have hg := (outside_log_gaps hn hm hnX hmX hq hqX hout hnP hmP).1
      have hp : 0 < |frequency r + Real.log q| := lt_of_lt_of_le (by positivity) hg
      apply (b.decay r hr _ (abs_pos.mp hp)).trans
      rw [div_le_iff₀ hp]
      have hh := (div_le_iff₀ (sq_pos_of_pos hx)).mp hg
      nlinarith [mul_le_mul_of_nonneg_left hh hA]
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hsize : (b.modes.card : ℝ) ≤ bandwidth U := by exact_mod_cast b.size
      nlinarith [mul_le_mul_of_nonneg_right hsize (mul_nonneg hA (sq_nonneg (bandwidth U : ℝ)))]

theorem probe_bound {U A : ℝ} {H : ℝ → ℝ} (hu : 0 ≤ U)
    (hb : ∀ t ∈ Icc U (2 * U), |H t| ≤ A) (v : ℝ) : ‖probe U H v‖ ≤ A * U := by
  have hle : U ≤ 2 * U := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := U) (b := 2 * U) (C := A) (f := fun t : ℝ => (H t : ℂ) * phase v t) (by
      intro t ht
      simpa [phase, Complex.norm_exp, Set.uIoc_of_le hle] using
        (hb t ⟨(Set.uIoc_of_le hle ▸ ht).1.le, (Set.uIoc_of_le hle ▸ ht).2⟩))
  simpa [probe, abs_of_nonneg hu, show 2 * U - U = U by ring] using h

theorem primeWeight_bounds {q X : ℕ} (hq : q.Prime) (hqX : q ≤ X) :
    0 ≤ primeWeight q ∧ primeWeight q ≤ X := by
  have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  have hs : 1 ≤ Real.sqrt (q : ℝ) := by simpa using Real.sqrt_le_sqrt h1
  have hd : 1 ≤ Real.pi * Real.sqrt (q : ℝ) :=
    one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) hs
  have hl := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1)
  have hx : (q : ℝ) ≤ X := by exact_mod_cast hqX
  constructor
  · exact div_nonneg (Real.log_nonneg h1) (by positivity)
  · unfold primeWeight
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).2
    have h := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ X by positivity)
    linarith

/-- The in-set primes are estimated before expanding the test. This costs a
fixed constant depending on P. Every outside prime has an arithmetic gap. -/
theorem prime_polynomial_bound {P U A} (b : FourierTrace P U A)
    (hu : 0 ≤ U) (hA : 0 ≤ A) :
    |∑ q ∈ primesTo (bandwidth U), primeWeight q * (probe U b.H (Real.log q)).re| ≤
      (∑ q ∈ P, |primeWeight q|) * (A * U) + A * (bandwidth U : ℝ) ^ 5 := by
  classical
  let Q := primesTo (bandwidth U)
  let g := fun q : ℕ => primeWeight q * (probe U b.H (Real.log q)).re
  have hin : ∑ q ∈ Q ∩ P, |g q| ≤ (∑ q ∈ P, |primeWeight q|) * (A * U) := by
    rw [Finset.sum_mul]
    apply (Finset.sum_le_sum (s := Q ∩ P) (g := fun q => |primeWeight q| * (A * U)) _).trans
    · apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro i hi hi'
      positivity
    · intro q hq
      dsimp only [g]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans (probe_bound hu b.boundH _)) (abs_nonneg _)
  have hc : (Q \ P).card ≤ bandwidth U := by
    apply (Finset.card_le_card (Finset.sdiff_subset : Q \ P ⊆ Q)).trans
    dsimp [Q, primesTo]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hout : ∑ q ∈ Q \ P, |g q| ≤ A * (bandwidth U : ℝ) ^ 5 := by
    calc
      _ ≤ ∑ _q ∈ Q \ P, (bandwidth U : ℝ) * (A * (bandwidth U : ℝ) ^ 3) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hqQ, hqP⟩ := Finset.mem_sdiff.mp hq
        obtain ⟨hqI, hprime⟩ := Finset.mem_filter.mp hqQ
        have hqX := (Finset.mem_Icc.mp hqI).2
        obtain ⟨hw, hwb⟩ := primeWeight_bounds hprime hqX
        dsimp only [g]
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul hwb ((Complex.abs_re_le_norm _).trans (probe_outside b hA hprime hqX hqP))
          (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hcr : ((Q \ P).card : ℝ) ≤ bandwidth U := by exact_mod_cast hc
        nlinarith [mul_le_mul_of_nonneg_right hcr (show
          0 ≤ (bandwidth U : ℝ) * (A * (bandwidth U : ℝ) ^ 3) by positivity)]
  calc
    _ ≤ ∑ q ∈ Q, |g q| := Finset.abs_sum_le_sum_abs _ _
    _ = (∑ q ∈ Q ∩ P, |g q|) + ∑ q ∈ Q \ P, |g q| := (Finset.sum_inter_add_sum_sdiff Q P _).symm
    _ ≤ _ := add_le_add hin hout

/-- The short prime cutoff absorbs five powers, leaving ample room for the log
in the main zero-count density. -/
theorem bandwidth_budget : ∀ᶠ U : ℝ in atTop,
    0 < bandwidth U ∧ (bandwidth U : ℝ) ^ 5 ≤ 2 * U ∧
    Real.log U * (bandwidth U : ℝ) ^ 2 ≤ 8 * (2 * U) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  let Y := (2 * U) ^ (1 / 8 : ℝ)
  have hu : 0 < 2 * U := by linarith
  have hy : 1 ≤ Y := Real.one_le_rpow (by linarith) (by norm_num)
  have hx : (bandwidth U : ℝ) ≤ Y := Nat.floor_le (zero_le_one.trans hy)
  have hone : 1 ≤ bandwidth U := (Nat.le_floor_iff (zero_le_one.trans hy)).2 (by simpa using hy)
  have hy8 : Y ^ 8 = 2 * U := by
    dsimp [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hlog : Real.log U ≤ 8 * Y := by
    have hly : Real.log Y = (1 / 8 : ℝ) * Real.log (2 * U) := Real.log_rpow hu _
    have hm := Real.log_le_log (by linarith : 0 < U) (by linarith : U ≤ 2 * U)
    linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hy)]
  have h58 : Y ^ 5 ≤ Y ^ 8 := pow_le_pow_right₀ hy (by decide)
  have h38 : Y ^ 3 ≤ Y ^ 8 := pow_le_pow_right₀ hy (by decide)
  refine ⟨hone, (pow_le_pow_left₀ (by positivity) hx 5).trans (h58.trans_eq hy8), ?_⟩
  calc
    _ ≤ (8 * Y) * Y ^ 2 := mul_le_mul hlog (pow_le_pow_left₀ (by positivity) hx 2)
      (sq_nonneg _) (by linarith)
    _ = 8 * Y ^ 3 := by ring
    _ ≤ _ := by rw [←hy8]; exact mul_le_mul_of_nonneg_left h38 (by norm_num)

end RiemannResearch.Analysis.DyadicZeroWasserstein
