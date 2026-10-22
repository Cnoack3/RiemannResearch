import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Two radical-invariant backward differences have trivial common kernel

The argument uses the full exact identity at arbitrarily large powers. No
squarefreeness restriction on the base is needed: radical invariance at both
`a` and `a^(k+1)` supplies the required power invariance.

Source: independently developed extension of the user-directed exact
optimizer research continuation, 8 October 2026.

The analytic hypothesis is only `f(n)/n -> 0`; inverse-square summability
provides it. This module is an abstract sequence theorem and makes no claim
that either family separately solves an RH approximation problem.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.RadicalDifferenceTotality

/-- Backward difference, with the natural predecessor convention at zero. -/
def backwardDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n - f (n - 1)

/-- Backward difference after division by the integer index. -/
def quotientDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n / (n : ℝ) - f (n - 1) / ((n - 1 : ℕ) : ℝ)

/-- Recover the complete normalized value from the two differences. -/
theorem normalized_value_of_two_differences
    {x y m A B : ℝ} (hm : m ≠ 0) (hm1 : m - 1 ≠ 0)
    (hA : x - y = A) (hB : x / m - y / (m - 1) = B) :
    x / m = A - (m - 1) * B := by
  have hy : y = x - A := by linarith
  rw [hy] at hB
  field_simp [hm, hm1] at hB
  apply (div_eq_iff hm).2
  nlinarith [hB]

/-- Both adjacent normalized values, retaining every affine term. -/
theorem adjacent_values_of_two_differences
    {x y m A B : ℝ} (hm : m ≠ 0) (hm1 : m - 1 ≠ 0)
    (hA : x - y = A) (hB : x / m - y / (m - 1) = B) :
    x / m = A - (m - 1) * B ∧ y / (m - 1) = A - m * B := by
  have hx := normalized_value_of_two_differences hm hm1 hA hB
  exact ⟨hx, by nlinarith [hx, hB]⟩

/-- A decaying sequence cannot be a nonconstant affine function of a
diverging real sequence. The constant part also vanishes. -/
theorem affine_power_amplification
    {q r : ℕ → ℝ} {A B : ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hr : Tendsto r atTop atTop)
    (h : ∀ k, q k = A - (r k - 1) * B) :
    A = 0 ∧ B = 0 := by
  have hinv : Tendsto (fun k => (r k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hr
  have hnum : Tendsto (fun k => A + B - q k) atTop (𝓝 (A + B)) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A + B) atTop
        (𝓝 (A + B))).sub hq
  have hprod : Tendsto (fun k => (A + B - q k) * (r k)⁻¹)
      atTop (𝓝 0) := by
    simpa using hnum.mul hinv
  have heq : (fun k => (A + B - q k) * (r k)⁻¹) =ᶠ[atTop]
      (fun _ => B) := by
    filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    have hne : r k ≠ 0 := ne_of_gt hk
    have hkform := h k
    field_simp [hne]
    nlinarith [hkform]
  have hB : B = 0 :=
    (tendsto_nhds_unique (hprod.congr' heq) tendsto_const_nhds).symm
  have heqA : q =ᶠ[atTop] (fun _ => A) :=
    Eventually.of_forall (fun k => by simpa [hB] using h k)
  have hA : A = 0 :=
    (tendsto_nhds_unique (hq.congr' heqA) tendsto_const_nhds).symm
  exact ⟨hA, hB⟩

/-- Squared inverse-index summability supplies the only decay input. -/
theorem normalized_tendsto_zero_of_summable
    {f : ℕ → ℝ} (hs : Summable (fun n => (f n / (n : ℝ)) ^ 2)) :
    Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0) := by
  have hsq := hs.tendsto_atTop_zero
  have hroot : Tendsto (fun n => Real.sqrt ((f n / (n : ℝ)) ^ 2))
      atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun n => ‖f n / (n : ℝ)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hroot
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Power invariance of both differences forces every sequence value to
vanish when the normalized values tend to zero. -/
theorem zero_of_power_invariant_differences
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0))
    (hpower : ∀ a : ℕ, 2 ≤ a → ∀ k : ℕ,
      backwardDifference f (a ^ (k + 1)) = backwardDifference f a)
    (hqpower : ∀ a : ℕ, 2 ≤ a → ∀ k : ℕ,
      quotientDifference f (a ^ (k + 1)) = quotientDifference f a) :
    ∀ n, f n = 0 := by
  have hdiff : ∀ a : ℕ, 2 ≤ a →
      backwardDifference f a = 0 ∧ quotientDifference f a = 0 := by
    intro a ha
    let m : ℕ → ℕ := fun k => a ^ (k + 1)
    have hm : Tendsto m atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < a)).comp
        (tendsto_add_atTop_nat 1)
    have hr : Tendsto (fun k => (m k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hm
    have hq : Tendsto (fun k => f (m k) / (m k : ℝ)) atTop (𝓝 0) :=
      hf.comp hm
    apply affine_power_amplification hq hr
    intro k
    have hmk : 2 ≤ m k :=
      le_trans ha (le_self_pow (by omega : 1 ≤ a) (Nat.succ_ne_zero k))
    have hmkR : (2 : ℝ) ≤ (m k : ℝ) := by exact_mod_cast hmk
    have hA : f (m k) - f (m k - 1) = backwardDifference f a :=
      hpower a ha k
    have hB : f (m k) / (m k : ℝ) -
        f (m k - 1) / ((m k - 1 : ℕ) : ℝ) = quotientDifference f a :=
      hqpower a ha k
    rw [Nat.cast_sub (by omega : 1 ≤ m k), Nat.cast_one] at hB
    exact normalized_value_of_two_differences (by linarith) (by linarith) hA hB
  have hf1 : f 1 = 0 := by
    have hA := (hdiff 2 (by omega)).1
    have hB := (hdiff 2 (by omega)).2
    norm_num [backwardDifference, quotientDifference] at hA hB
    linarith
  intro n
  induction n with
  | zero => exact hf0
  | succ n ih =>
      by_cases hn : n = 0
      · simpa [hn] using hf1
      · have hA : f (n + 1) - f n = 0 := by
          simpa [backwardDifference] using (hdiff (n + 1) (by omega)).1
        linarith

/-- Concrete radical invariance supplies power invariance exactly. -/
theorem zero_of_radical_invariant_differences
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0))
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (UniqueFactorizationMonoid.radical n))
    (hqrad : ∀ n : ℕ, 2 ≤ n → quotientDifference f n =
      quotientDifference f (UniqueFactorizationMonoid.radical n)) :
    ∀ n, f n = 0 := by
  apply zero_of_power_invariant_differences hf0 hf
  · intro a ha k
    have hm : 2 ≤ a ^ (k + 1) :=
      le_trans ha (le_self_pow (by omega : 1 ≤ a) (Nat.succ_ne_zero k))
    calc
      backwardDifference f (a ^ (k + 1)) =
          backwardDifference f (UniqueFactorizationMonoid.radical (a ^ (k + 1))) :=
        hrad _ hm
      _ = backwardDifference f (UniqueFactorizationMonoid.radical a) := by
        rw [UniqueFactorizationMonoid.radical_pow a (Nat.succ_ne_zero k)]
      _ = backwardDifference f a := (hrad a ha).symm
  · intro a ha k
    have hm : 2 ≤ a ^ (k + 1) :=
      le_trans ha (le_self_pow (by omega : 1 ≤ a) (Nat.succ_ne_zero k))
    calc
      quotientDifference f (a ^ (k + 1)) =
          quotientDifference f (UniqueFactorizationMonoid.radical (a ^ (k + 1))) :=
        hqrad _ hm
      _ = quotientDifference f (UniqueFactorizationMonoid.radical a) := by
        rw [UniqueFactorizationMonoid.radical_pow a (Nat.succ_ne_zero k)]
      _ = quotientDifference f a := (hqrad a ha).symm

/-- Inverse-square version of the concrete common-kernel theorem. -/
theorem zero_of_summable_radical_invariant_differences
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hs : Summable (fun n => (f n / (n : ℝ)) ^ 2))
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (UniqueFactorizationMonoid.radical n))
    (hqrad : ∀ n : ℕ, 2 ≤ n → quotientDifference f n =
      quotientDifference f (UniqueFactorizationMonoid.radical n)) :
    ∀ n, f n = 0 :=
  zero_of_radical_invariant_differences hf0
    (normalized_tendsto_zero_of_summable hs) hrad hqrad

open UniqueFactorizationMonoid

/-- The reciprocal difference is needed only at squarefree base sites.
Without an analytic hypothesis, the complete common kernel consists of
linear sequences. -/
theorem linear_of_radical_differences_and_squarefree_quotient_bases
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (radical n))
    (hbase : ∀ n : ℕ, 2 ≤ n → Squarefree n → quotientDifference f n = 0) :
    ∀ n, f n = (n : ℝ) * f 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simp [hn0, hf0]
      by_cases hn1 : n = 1
      · simp [hn1]
      have hn2 : 2 ≤ n := by omega
      have hprev : f (n - 1) = ((n - 1 : ℕ) : ℝ) * f 1 :=
        ih (n - 1) (by omega)
      by_cases hs : Squarefree n
      · have hB := hbase n hn2 hs
        unfold quotientDifference at hB
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
        have hprevR : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (show n - 1 ≠ 0 by omega)
        have hq : f n / (n : ℝ) = f 1 := by
          calc
            f n / (n : ℝ) = f (n - 1) / ((n - 1 : ℕ) : ℝ) :=
              sub_eq_zero.mp hB
            _ = f 1 := by
              rw [hprev]
              exact mul_div_cancel_left₀ (f 1) hprevR
        simpa [mul_comm] using (div_eq_iff hnR).mp hq
      · have ha2 : 2 ≤ radical n := Nat.two_le_radical_iff.mpr hn2
        have hale : radical n ≤ n := Nat.radical_le_self_iff.mpr hn0
        have hane : radical n ≠ n := by
          intro he
          apply hs
          rw [← he]
          exact squarefree_radical
        have halt : radical n < n := by omega
        have ha : f (radical n) = ((radical n : ℕ) : ℝ) * f 1 :=
          ih (radical n) halt
        have haprev : f (radical n - 1) = ((radical n - 1 : ℕ) : ℝ) * f 1 :=
          ih (radical n - 1) (by omega)
        have hA := hrad n hn2
        unfold backwardDifference at hA
        rw [hprev, ha, haprev,
          Nat.cast_sub (by omega : 1 ≤ n),
          Nat.cast_sub (by omega : 1 ≤ radical n)] at hA
        norm_num only [Nat.cast_one] at hA
        nlinarith [hA]

/-- Inverse-index decay removes the linear common-kernel direction. -/
theorem zero_of_radical_differences_and_squarefree_quotient_bases
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0))
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (radical n))
    (hbase : ∀ n : ℕ, 2 ≤ n → Squarefree n → quotientDifference f n = 0) :
    ∀ n, f n = 0 := by
  have hlinear := linear_of_radical_differences_and_squarefree_quotient_bases
    hf0 hrad hbase
  have heq : (fun n => f n / (n : ℝ)) =ᶠ[atTop] (fun _ => f 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    rw [hlinear n]
    exact mul_div_cancel_left₀ (f 1) hnR
  have hf1 : f 1 = 0 :=
    (tendsto_nhds_unique (hf.congr' heq) tendsto_const_nhds).symm
  intro n
  simp [hlinear n, hf1]

/-- The inverse-square-summable version of squarefree-base totality. -/
theorem zero_of_summable_radical_differences_and_squarefree_quotient_bases
    {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hs : Summable (fun n => (f n / (n : ℝ)) ^ 2))
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (radical n))
    (hbase : ∀ n : ℕ, 2 ≤ n → Squarefree n → quotientDifference f n = 0) :
    ∀ n, f n = 0 :=
  zero_of_radical_differences_and_squarefree_quotient_bases hf0
    (normalized_tendsto_zero_of_summable hs) hrad hbase

/-- Finite stability of squarefree-base rigidity. The signed derivative
and coordinate errors are controlled simultaneously; no tail hypothesis
or norm bound is used. -/
theorem finite_rigidity_of_squarefree_quotient_bound
    {f : ℕ → ℝ} {J : ℕ} {ε : ℝ}
    (hf0 : f 0 = 0) (hε : 0 ≤ ε)
    (hrad : ∀ n : ℕ, 2 ≤ n → backwardDifference f n =
      backwardDifference f (radical n))
    (hbase : ∀ a : ℕ, 2 ≤ a → a ≤ J → Squarefree a →
      |quotientDifference f a| ≤ ε) :
    ∀ n : ℕ, 1 ≤ n → n ≤ J →
      |f n - (n : ℝ) * f 1| ≤ (n : ℝ) * ((n : ℝ) - 1) * ε ∧
      |backwardDifference f n - f 1| ≤ 2 * ((n : ℝ) - 1) * ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn1 hnJ
      by_cases hn : n = 1
      · subst n
        simp [backwardDifference, hf0]
      have hn2 : 2 ≤ n := by omega
      have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hnRpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
      have hprevpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < n - 1 by omega)
      have hcastprev : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have hprev := ih (n - 1) (by omega) (by omega) (by omega)
      have hprev_error :
          |f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1| ≤
            ((n : ℝ) - 1) * ((n : ℝ) - 2) * ε := by
        calc
          |f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1| ≤
              ((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) - 1) * ε := hprev.1
          _ = ((n : ℝ) - 1) * ((n : ℝ) - 2) * ε := by
            rw [hcastprev]
            ring
      have hdiff : |backwardDifference f n - f 1| ≤
          2 * ((n : ℝ) - 1) * ε := by
        by_cases hs : Squarefree n
        · have hstep : backwardDifference f n - f 1 =
              (f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1) /
                ((n - 1 : ℕ) : ℝ) +
              (n : ℝ) * quotientDifference f n := by
            unfold backwardDifference quotientDifference
            rw [hcastprev]
            have hpredne : (n : ℝ) - 1 ≠ 0 := by linarith
            field_simp [hnRne, hpredne]
            ring
          have hfirst :
              |(f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1) /
                ((n - 1 : ℕ) : ℝ)| ≤ ((n : ℝ) - 2) * ε := by
            rw [abs_div, abs_of_pos hprevpos]
            apply (div_le_iff₀ hprevpos).2
            calc
              |f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1| ≤
                  ((n : ℝ) - 1) * ((n : ℝ) - 2) * ε := hprev_error
              _ = ((n : ℝ) - 2) * ε * ((n - 1 : ℕ) : ℝ) := by
                rw [hcastprev]
                ring
          have hsecond : |(n : ℝ) * quotientDifference f n| ≤
              (n : ℝ) * ε := by
            rw [abs_mul, abs_of_pos hnRpos]
            exact mul_le_mul_of_nonneg_left (hbase n hn2 hnJ hs)
              (le_of_lt hnRpos)
          calc
            |backwardDifference f n - f 1| =
                |(f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1) /
                  ((n - 1 : ℕ) : ℝ) +
                  (n : ℝ) * quotientDifference f n| := congrArg abs hstep
            _ ≤ |(f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1) /
                  ((n - 1 : ℕ) : ℝ)| +
                  |(n : ℝ) * quotientDifference f n| := abs_add_le _ _
            _ ≤ ((n : ℝ) - 2) * ε + (n : ℝ) * ε :=
              add_le_add hfirst hsecond
            _ = 2 * ((n : ℝ) - 1) * ε := by ring
        · have ha2 : 2 ≤ radical n := Nat.two_le_radical_iff.mpr hn2
          have hale : radical n ≤ n :=
            Nat.radical_le_self_iff.mpr (by omega : n ≠ 0)
          have hane : radical n ≠ n := by
            intro he
            apply hs
            rw [← he]
            exact squarefree_radical
          have halt : radical n < n := by omega
          have ha := ih (radical n) halt (by omega) (by omega)
          have haRle : ((radical n : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hale
          have hmul : (((radical n : ℕ) : ℝ) - 1) * ε ≤
              ((n : ℝ) - 1) * ε :=
            mul_le_mul_of_nonneg_right (sub_le_sub_right haRle 1) hε
          calc
            |backwardDifference f n - f 1| =
                |backwardDifference f (radical n) - f 1| := by
                  rw [hrad n hn2]
            _ ≤ 2 * (((radical n : ℕ) : ℝ) - 1) * ε := ha.2
            _ ≤ 2 * ((n : ℝ) - 1) * ε := by nlinarith [hmul]
      have herror : f n - (n : ℝ) * f 1 =
          (f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1) +
          (backwardDifference f n - f 1) := by
        unfold backwardDifference
        rw [hcastprev]
        ring
      refine ⟨?_, hdiff⟩
      calc
        |f n - (n : ℝ) * f 1| =
            |(f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1) +
              (backwardDifference f n - f 1)| := congrArg abs herror
        _ ≤ |f (n - 1) - ((n - 1 : ℕ) : ℝ) * f 1| +
              |backwardDifference f n - f 1| := abs_add_le _ _
        _ ≤ ((n : ℝ) - 1) * ((n : ℝ) - 2) * ε +
              2 * ((n : ℝ) - 1) * ε := add_le_add hprev_error hdiff
        _ = (n : ℝ) * ((n : ℝ) - 1) * ε := by ring

end RiemannResearch.Analysis.RadicalDifferenceTotality
