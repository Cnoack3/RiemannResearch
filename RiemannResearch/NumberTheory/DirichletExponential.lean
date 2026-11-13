import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic Dirichlet exponentials of bounded residues

Source: the user-provided Pareto Nyman--Beurling argument. All products and
powers below are Mathlib's genuine Dirichlet-convolution products on arithmetic
functions. In particular the zeroth power is the convolution unit `δ₁`.

This module proves scalar coefficient convergence and arithmetic unboundedness.
It makes no assertion about membership in the Pareto Hilbert space or in the
closed linear span of its normalized residue atoms.
-/

noncomputable section

namespace RiemannResearch.NumberTheory.DirichletExponential

open scoped BigOperators

/-- The exponential series for actual Dirichlet convolution, evaluated at one
arithmetic coefficient. Source: the user's definition of `exp⋆`. -/
def convolutionExp (f : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  ∑' r : ℕ, (f ^ r) n / (r.factorial : ℝ)

/-- The zeroth convolution power is `δ₁`, not the constant sequence. -/
theorem convolutionPower_zero (f : ArithmeticFunction ℝ) (n : ℕ) :
    (f ^ 0) n = if n = 1 then 1 else 0 := by
  simp only [pow_zero, ArithmeticFunction.one_apply]

/-- Powers preserve nonnegative arithmetic coefficients. -/
theorem convolutionPower_nonneg (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (r n : ℕ) : 0 ≤ (f ^ r) n := by
  induction r generalizing n with
  | zero =>
      simp only [convolutionPower_zero]
      split_ifs <;> norm_num
  | succ r ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply]
      exact Finset.sum_nonneg fun d _ => mul_nonneg (ih d.1) (hf d.2)

/-- Dirichlet powers are coefficientwise monotone on nonnegative inputs. -/
theorem convolutionPower_mono {f g : ArithmeticFunction ℝ}
    (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n) (r n : ℕ) :
    (f ^ r) n ≤ (g ^ r) n := by
  have hg : ∀ n, 0 ≤ g n := fun n => (hf n).trans (hfg n)
  induction r generalizing n with
  | zero => exact le_rfl
  | succ r ih =>
      rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul (ih d.1) (hfg d.2) (hf d.2)
        (convolutionPower_nonneg g hg r d.1)

/-- A coarse coefficient bound sufficient to justify every scalar exponential
series for a bounded input. The induction is uniform over `m ≤ N`.
Source: the elementary divisor-sum estimate in the user's argument. -/
theorem convolutionPower_abs_le (f : ArithmeticFunction ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ m, |f m| ≤ C) (r N : ℕ) :
    ∀ m ≤ N, |(f ^ r) m| ≤ (C * ((N : ℝ) + 1)) ^ r := by
  have hA : 0 ≤ C * ((N : ℝ) + 1) := mul_nonneg hC (by positivity)
  induction r with
  | zero =>
      intro m hm
      simp only [pow_zero, ArithmeticFunction.one_apply]
      split_ifs <;> norm_num
  | succ r ih =>
      intro m hm
      rw [pow_succ, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun d e => (f ^ r) d * f e)]
      calc
        |∑ d ∈ m.divisors, (f ^ r) d * f (m / d)|
            ≤ ∑ d ∈ m.divisors, |(f ^ r) d * f (m / d)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ m.divisors, (C * ((N : ℝ) + 1)) ^ r * C := by
          apply Finset.sum_le_sum
          intro d hd
          rw [abs_mul]
          exact mul_le_mul (ih d ((Nat.divisor_le hd).trans hm)) (hf (m / d))
            (abs_nonneg _) (pow_nonneg hA r)
        _ = (m.divisors.card : ℝ) * ((C * ((N : ℝ) + 1)) ^ r * C) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((N : ℝ) + 1) * ((C * ((N : ℝ) + 1)) ^ r * C) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg hA r) hC)
          exact_mod_cast (Nat.card_divisors_le_self m).trans (by omega : m ≤ N + 1)
        _ = (C * ((N : ℝ) + 1)) ^ (r + 1) := by
          rw [pow_succ]
          ring

/-- Bounded arithmetic inputs have an absolutely convergent exponential series
at every coefficient. This is independent of any Hilbert-space assertion. -/
theorem convolutionExp_summable (f : ArithmeticFunction ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ m, |f m| ≤ C) (n : ℕ) :
    Summable (fun r : ℕ => (f ^ r) n / (r.factorial : ℝ)) := by
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (C * ((n : ℝ) + 1)))
  intro r
  rw [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (r.factorial : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right
    (convolutionPower_abs_le f hC hf r n n le_rfl) (Nat.cast_nonneg _)

/-- Every exponential coefficient is nonnegative for nonnegative input. -/
theorem convolutionExp_nonneg (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (n : ℕ) : 0 ≤ convolutionExp f n := by
  exact tsum_nonneg fun r =>
    div_nonneg (convolutionPower_nonneg f hf r n) (Nat.cast_nonneg _)

/-- The exponential is coefficientwise monotone on nonnegative bounded inputs. -/
theorem convolutionExp_mono {f g : ArithmeticFunction ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n)
    (hgC : ∀ n, |g n| ≤ C) (n : ℕ) :
    convolutionExp f n ≤ convolutionExp g n := by
  have hfC : ∀ n, |f n| ≤ C := by
    intro n
    rw [abs_of_nonneg (hf n)]
    exact (hfg n).trans ((le_abs_self _).trans (hgC n))
  apply Summable.tsum_le_tsum _ (convolutionExp_summable f hC hfC n)
    (convolutionExp_summable g hC hgC n)
  intro r
  exact div_le_div_of_nonneg_right (convolutionPower_mono hf hfg r n)
    (Nat.cast_nonneg _)

/-- The quadratic term alone is a lower bound for a nonnegative, bounded input.
Source: retain the `r = 2` summand of the user's exponential series. -/
theorem convolutionExp_quadratic_lower (f : ArithmeticFunction ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ m, |f m| ≤ C) (hf0 : ∀ m, 0 ≤ f m) (n : ℕ) :
    (f * f) n / 2 ≤ convolutionExp f n := by
  have hs := convolutionExp_summable f hC hf n
  have h := hs.le_tsum 2 (fun r _ =>
    div_nonneg (convolutionPower_nonneg f hf0 r n) (Nat.cast_nonneg _))
  simpa [convolutionExp, pow_two] using h

/-- The first coefficient of a convolution power is the ordinary scalar power. -/
theorem convolutionPower_one (f : ArithmeticFunction ℝ) (r : ℕ) :
    (f ^ r) 1 = (f 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply_one, ih, pow_succ]

/-- The first coefficient of the convolution exponential is the scalar
exponential series at `f 1`. -/
theorem convolutionExp_one_series (f : ArithmeticFunction ℝ) :
    convolutionExp f 1 = ∑' r : ℕ, (f 1) ^ r / (r.factorial : ℝ) := by
  simp only [convolutionExp, convolutionPower_one]

@[simp] theorem convolutionExp_zero (f : ArithmeticFunction ℝ) :
    convolutionExp f 0 = 0 := by
  simp [convolutionExp]

/-- The arithmetic-function embedding of the normalized residue
`g_p(n) = (n % p) / p`. Source: the user's normalized Pareto atom. -/
def residueAF (p : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => ((n % p : ℕ) : ℝ) / (p : ℝ), by simp⟩

@[simp] theorem residueAF_apply (p n : ℕ) :
    residueAF p n = ((n % p : ℕ) : ℝ) / (p : ℝ) := rfl

theorem residueAF_nonneg (p n : ℕ) : 0 ≤ residueAF p n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem residueAF_abs_le_one (p n : ℕ) : |residueAF p n| ≤ 1 := by
  rw [abs_of_nonneg (residueAF_nonneg p n)]
  by_cases hp : p = 0
  · simp [hp]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    change ((n % p : ℕ) : ℝ) / (p : ℝ) ≤ 1
    apply (div_le_iff₀ hpR).2
    simpa only [one_mul] using
      (show ((n % p : ℕ) : ℝ) ≤ (p : ℝ) by exact_mod_cast (Nat.mod_lt n hp0).le)

@[simp] theorem residueAF_one {p : ℕ} (hp : 1 < p) :
    residueAF p 1 = 1 / (p : ℝ) := by
  simp [residueAF, Nat.mod_eq_of_lt hp]

/-- The exponential coefficient series of every normalized residue converges. -/
theorem residueAF_exp_summable (p n : ℕ) :
    Summable (fun r : ℕ => ((residueAF p) ^ r) n / (r.factorial : ℝ)) :=
  convolutionExp_summable (residueAF p) (C := 1) (by norm_num)
    (residueAF_abs_le_one p) n

/-- Along the powers of a distinct prime, every normalized residue is at least
`1 / p`. Source: a nonzero residue modulo the prime `p` is at least one. -/
theorem residueAF_prime_pow_lower {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (a : ℕ) : 1 / (p : ℝ) ≤ residueAF p (q ^ a) := by
  have hnot : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).1 h with h | h
    · exact hp.ne_one h
    · exact hpq h
  have hnotpow : ¬ p ∣ q ^ a := fun h => hnot (hp.dvd_of_dvd_pow h)
  have hmod : 1 ≤ q ^ a % p := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    exact hnotpow (Nat.dvd_of_mod_eq_zero h)
  change 1 / (p : ℝ) ≤ ((q ^ a % p : ℕ) : ℝ) / (p : ℝ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmod) (Nat.cast_nonneg _)

/-- The actual Dirichlet square grows at least linearly along another prime's
powers. Source: the `a + 1` divisors `1,q,...,q^a` each contribute `≥ 1/p²`. -/
theorem residueAF_square_prime_pow_lower {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (a : ℕ) :
    ((a : ℝ) + 1) / (p : ℝ) ^ 2 ≤ (residueAF p * residueAF p) (q ^ a) := by
  calc
    ((a : ℝ) + 1) / (p : ℝ) ^ 2
        = ∑ _j ∈ Finset.range (a + 1), (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, div_mul_div_comm, one_mul, pow_two]
      ring
    _ ≤ ∑ j ∈ Finset.range (a + 1),
        residueAF p (q ^ j) * residueAF p (q ^ a / q ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hja : j ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hpower : q ^ a = q ^ j * q ^ (a - j) := by
        rw [← pow_add, Nat.add_sub_of_le hja]
      have hquot : q ^ a / q ^ j = q ^ (a - j) := by
        rw [hpower, Nat.mul_div_cancel_left _ (pow_pos hq.pos j)]
      rw [hquot]
      exact mul_le_mul (residueAF_prime_pow_lower hp hq hpq j)
        (residueAF_prime_pow_lower hp hq hpq (a - j)) (by positivity)
        (residueAF_nonneg p (q ^ j))
    _ = (residueAF p * residueAF p) (q ^ a) := by
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun d e => residueAF p d * residueAF p e),
        Nat.sum_divisors_prime_pow hq]

/-- A concrete lower bound proving that `exp⋆(g_p)` is unbounded.
Source: combine the Dirichlet square estimate with the quadratic series term. -/
theorem residueAF_exp_prime_pow_lower {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (a : ℕ) :
    ((a : ℝ) + 1) / (2 * (p : ℝ) ^ 2) ≤ convolutionExp (residueAF p) (q ^ a) := by
  calc
    ((a : ℝ) + 1) / (2 * (p : ℝ) ^ 2)
        = (((a : ℝ) + 1) / (p : ℝ) ^ 2) / 2 := by
      rw [div_div]
      congr 1
      ring
    _ ≤ (residueAF p * residueAF p) (q ^ a) / 2 :=
      div_le_div_of_nonneg_right (residueAF_square_prime_pow_lower hp hq hpq a)
        (by norm_num)
    _ ≤ convolutionExp (residueAF p) (q ^ a) :=
      convolutionExp_quadratic_lower (residueAF p) (C := 1) (by norm_num)
        (residueAF_abs_le_one p) (residueAF_nonneg p) (q ^ a)

/-- The normalized-residue convolution exponential exceeds every real bound.
Source: choose a distinct prime and let the exponent in its prime powers grow. -/
theorem residueAF_exp_unbounded {p : ℕ} (hp : p.Prime) :
    ∀ M : ℝ, ∃ n : ℕ, M < convolutionExp (residueAF p) n := by
  obtain ⟨q, hpq_le, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hpq : p ≠ q := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hden : 0 < 2 * (p : ℝ) ^ 2 := by positivity
  intro M
  obtain ⟨a, ha⟩ := exists_nat_gt ((2 * (p : ℝ) ^ 2) * M)
  refine ⟨q ^ a, lt_of_lt_of_le ?_ (residueAF_exp_prime_pow_lower hp hq hpq a)⟩
  apply (lt_div_iff₀ hden).2
  nlinarith

/-- In particular, no uniform absolute bound exists for the exponential. -/
theorem residueAF_exp_not_bounded {p : ℕ} (hp : p.Prime) :
    ¬ ∃ M : ℝ, ∀ n : ℕ, |convolutionExp (residueAF p) n| ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := residueAF_exp_unbounded hp M
  exact (not_lt_of_ge ((le_abs_self _).trans (hM n))) hn

/-- A finite linear combination of normalized residues is uniformly bounded. -/
theorem residueAF_finite_sum_abs_le (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) :
    |∑ k ∈ s, c k * residueAF k n| ≤ ∑ k ∈ s, |c k| := by
  calc
    |∑ k ∈ s, c k * residueAF k n|
        ≤ ∑ k ∈ s, |c k * residueAF k n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, |c k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (residueAF_abs_le_one k n) (abs_nonneg (c k))

/-- The convolution exponential of a normalized prime residue is never exactly
a finite linear combination of normalized residues. This statement does not
exclude membership in their closed Hilbert-space span. -/
theorem residueAF_exp_ne_finite_sum {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    ¬ ∀ n : ℕ, convolutionExp (residueAF p) n = ∑ k ∈ s, c k * residueAF k n := by
  intro h
  apply residueAF_exp_not_bounded hp
  refine ⟨∑ k ∈ s, |c k|, ?_⟩
  intro n
  rw [h n]
  exact residueAF_finite_sum_abs_le s c n

end RiemannResearch.NumberTheory.DirichletExponential
