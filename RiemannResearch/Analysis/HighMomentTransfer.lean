import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Interval high-moment transfer

This module proves only the analytic transfer from an approximating function and
its two shifted remainders to a moment bound for increments.  It neither asserts
nor assumes that the zeta argument has already been approximated by a prime sum.

Source for the decomposition and its application: Simonič, Trudgian and
Turnage-Butterbaugh, *Some explicit and unconditional results on gaps between
zeroes of the Riemann zeta-function*, Sections 3--4,
https://arxiv.org/abs/2010.10675.  The convexity proof below is elementary.

`TsangHighMomentAsymptotic` records the exact dyadic analytic target as a
proposition.  There is deliberately no declaration asserting that proposition
for the actual zeta argument.  In particular, the Selberg approximation,
zero-density estimate, and prime variance asymptotic remain separate analytic
obligations.  Principal `Complex.arg` must not be substituted for the continuously
continued argument used in the cited theorem.

-/

open MeasureTheory

namespace RiemannResearch.HighMomentTransfer

/-- Convexity for a sum of three nonnegative real numbers, with its exact
cardinality factor. -/
theorem three_add_pow_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    (a + b + c) ^ n ≤ (3 : ℝ) ^ (n - 1) * (a ^ n + b ^ n + c ^ n) := by
  have hhalf : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    have h := (convexOn_pow (𝕜 := ℝ) n).2 ha hb
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simp only [smul_eq_mul] at h
    rw [show (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 by ring,
      show (1 / 2 : ℝ) * a ^ n + (1 / 2 : ℝ) * b ^ n =
        (a ^ n + b ^ n) / 2 by ring] at h
    exact h
  have hthird := (convexOn_pow (𝕜 := ℝ) n).2
    (by positivity : 0 ≤ (a + b) / 2) hc
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (2 / 3 : ℝ) + 1 / 3 = 1)
  simp only [smul_eq_mul] at hthird
  rw [show (2 / 3 : ℝ) * ((a + b) / 2) + (1 / 3 : ℝ) * c =
    (a + b + c) / 3 by ring] at hthird
  have havg : ((a + b + c) / 3) ^ n ≤ (a ^ n + b ^ n + c ^ n) / 3 := by
    calc
      ((a + b + c) / 3) ^ n ≤
          (2 / 3 : ℝ) * ((a + b) / 2) ^ n + (1 / 3 : ℝ) * c ^ n := hthird
      _ ≤ (2 / 3 : ℝ) * ((a ^ n + b ^ n) / 2) + (1 / 3 : ℝ) * c ^ n := by
        linarith [hhalf]
      _ = (a ^ n + b ^ n + c ^ n) / 3 := by ring
  have hthree : (3 : ℝ) ^ n = (3 : ℝ) ^ (n - 1) * 3 := by
    calc
      (3 : ℝ) ^ n = (3 : ℝ) ^ ((n - 1) + 1) := by congr 1; omega
      _ = (3 : ℝ) ^ (n - 1) * 3 := pow_succ _ _
  calc
    (a + b + c) ^ n = (3 : ℝ) ^ n * ((a + b + c) / 3) ^ n := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (3 : ℝ) ^ n * ((a ^ n + b ^ n + c ^ n) / 3) :=
      mul_le_mul_of_nonneg_left havg (pow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (n - 1) * (a ^ n + b ^ n + c ^ n) := by
      rw [hthree]
      ring

/-- The scalar estimate also works in every seminormed additive group. -/
theorem norm_add_sub_pow_le {E : Type*} [SeminormedAddCommGroup E]
    (x y z : E) (n : ℕ) (hn : 1 ≤ n) :
    ‖x + y - z‖ ^ n ≤ (3 : ℝ) ^ (n - 1) * (‖x‖ ^ n + ‖y‖ ^ n + ‖z‖ ^ n) := by
  have htriangle : ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ :=
    (norm_sub_le (x + y) z).trans
      (_root_.add_le_add (norm_add_le x y) (le_refl ‖z‖))
  exact (pow_le_pow_left₀ (norm_nonneg _) htriangle n).trans
    (three_add_pow_le (norm_nonneg x) (norm_nonneg y) (norm_nonneg z) n hn)

/-- Actual interval integral of the even norm power. -/
noncomputable def evenMoment (f : ℝ → ℝ) (k : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖f t‖ ^ (2 * k)

/-- Integrability is stated explicitly, allowing this result to be used for
functions with jumps, including the actual zeta argument. -/
theorem increment_evenMoment_le
    (S P R : ℝ → ℝ) (h a b : ℝ) (hab : a ≤ b) (k : ℕ) (hk : 1 ≤ k)
    (hS : IntervalIntegrable (fun t => ‖S (t + h) - S t‖ ^ (2 * k)) volume a b)
    (hP : IntervalIntegrable (fun t => ‖P t‖ ^ (2 * k)) volume a b)
    (hRh : IntervalIntegrable (fun t => ‖R (t + h)‖ ^ (2 * k)) volume a b)
    (hR : IntervalIntegrable (fun t => ‖R t‖ ^ (2 * k)) volume a b)
    (hdecomp : ∀ t ∈ Set.Icc a b, S (t + h) - S t = P t + R (t + h) - R t) :
    evenMoment (fun t => S (t + h) - S t) k a b ≤
      (3 : ℝ) ^ (2 * k - 1) *
        (evenMoment P k a b + evenMoment (fun t => R (t + h)) k a b +
          evenMoment R k a b) := by
  calc
    evenMoment (fun t => S (t + h) - S t) k a b ≤
        ∫ t in a..b, (3 : ℝ) ^ (2 * k - 1) *
          (‖P t‖ ^ (2 * k) + ‖R (t + h)‖ ^ (2 * k) + ‖R t‖ ^ (2 * k)) := by
      apply intervalIntegral.integral_mono_on hab hS
        (((hP.add hRh).add hR).const_mul _)
      intro t ht
      rw [hdecomp t ht]
      exact norm_add_sub_pow_le _ _ _ _ (by omega)
    _ = (3 : ℝ) ^ (2 * k - 1) *
        (evenMoment P k a b + evenMoment (fun t => R (t + h)) k a b +
          evenMoment R k a b) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hP.add hRh) hR,
        intervalIntegral.integral_add hP hRh]
      rfl

/-- Convenient continuous special case.  Continuity is not imposed on the
primary theorem above, because the actual zeta argument has jumps. -/
theorem increment_evenMoment_le_of_continuous
    (S P R : ℝ → ℝ) (hS : Continuous S) (hP : Continuous P) (hR : Continuous R)
    (h a b : ℝ) (hab : a ≤ b) (k : ℕ) (hk : 1 ≤ k)
    (hdecomp : ∀ t ∈ Set.Icc a b, S (t + h) - S t = P t + R (t + h) - R t) :
    evenMoment (fun t => S (t + h) - S t) k a b ≤
      (3 : ℝ) ^ (2 * k - 1) *
        (evenMoment P k a b + evenMoment (fun t => R (t + h)) k a b +
          evenMoment R k a b) := by
  apply increment_evenMoment_le S P R h a b hab k hk
    ((((hS.comp (continuous_id.add continuous_const)).sub hS).norm.pow _).intervalIntegrable a b)
    ((hP.norm.pow _).intervalIntegrable a b)
    (((hR.comp (continuous_id.add continuous_const)).norm.pow _).intervalIntegrable a b)
    ((hR.norm.pow _).intervalIntegrable a b) hdecomp

/-- Combining a polynomial variance budget `U` and a remainder budget `V`
requires no zeta-specific assumption. -/
theorem increment_evenMoment_le_of_budgets
    (S P R : ℝ → ℝ) (h a b T U V : ℝ) (hab : a ≤ b)
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (k : ℕ) (hk : 1 ≤ k)
    (hS : IntervalIntegrable (fun t => ‖S (t + h) - S t‖ ^ (2 * k)) volume a b)
    (hP : IntervalIntegrable (fun t => ‖P t‖ ^ (2 * k)) volume a b)
    (hRh : IntervalIntegrable (fun t => ‖R (t + h)‖ ^ (2 * k)) volume a b)
    (hR : IntervalIntegrable (fun t => ‖R t‖ ^ (2 * k)) volume a b)
    (hdecomp : ∀ t ∈ Set.Icc a b, S (t + h) - S t = P t + R (t + h) - R t)
    (hpoly : evenMoment P k a b ≤ T * U ^ k)
    (hshift : evenMoment (fun t => R (t + h)) k a b ≤ T * V ^ k)
    (hrem : evenMoment R k a b ≤ T * V ^ k) :
    evenMoment (fun t => S (t + h) - S t) k a b ≤ T * (9 * (U + V)) ^ k := by
  have hUpow : U ^ k ≤ (U + V) ^ k :=
    pow_le_pow_left₀ hU (le_add_of_nonneg_right hV) k
  have hVpow : V ^ k ≤ (U + V) ^ k :=
    pow_le_pow_left₀ hV (le_add_of_nonneg_left hU) k
  have hp := hpoly.trans (mul_le_mul_of_nonneg_left hUpow hT)
  have hh := hshift.trans (mul_le_mul_of_nonneg_left hVpow hT)
  have hr := hrem.trans (mul_le_mul_of_nonneg_left hVpow hT)
  have hthree : (3 : ℝ) ^ (2 * k - 1) * 3 = (9 : ℝ) ^ k := by
    calc
      (3 : ℝ) ^ (2 * k - 1) * 3 = (3 : ℝ) ^ ((2 * k - 1) + 1) :=
        (pow_succ _ _).symm
      _ = (3 : ℝ) ^ (2 * k) := by congr 1; omega
      _ = (9 : ℝ) ^ k := by rw [pow_mul]; norm_num
  calc
    evenMoment (fun t => S (t + h) - S t) k a b ≤
        (3 : ℝ) ^ (2 * k - 1) *
          (evenMoment P k a b + evenMoment (fun t => R (t + h)) k a b +
            evenMoment R k a b) :=
      increment_evenMoment_le S P R h a b hab k hk hS hP hRh hR hdecomp
    _ ≤ (3 : ℝ) ^ (2 * k - 1) *
        (T * (U + V) ^ k + T * (U + V) ^ k + T * (U + V) ^ k) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hp hh) hr) (by positivity)
    _ = T * ((3 : ℝ) ^ (2 * k - 1) * 3) * (U + V) ^ k := by ring
    _ = T * (9 * (U + V)) ^ k := by rw [hthree, mul_pow]; ring

/-- The upper-bound assembly appropriate to Tsang's theorem.  The polynomial
and Selberg remainder estimates are explicit hypotheses, not claimed results. -/
theorem coarse_tsang_upper_of_component_bounds
    (S P R : ℝ → ℝ) (h T C L : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (k : ℕ) (hk : 1 ≤ k)
    (hS : IntervalIntegrable (fun t => ‖S (t + h) - S t‖ ^ (2 * k)) volume T (2 * T))
    (hP : IntervalIntegrable (fun t => ‖P t‖ ^ (2 * k)) volume T (2 * T))
    (hRh : IntervalIntegrable (fun t => ‖R (t + h)‖ ^ (2 * k)) volume T (2 * T))
    (hR : IntervalIntegrable (fun t => ‖R t‖ ^ (2 * k)) volume T (2 * T))
    (hdecomp : ∀ t ∈ Set.Icc T (2 * T), S (t + h) - S t = P t + R (t + h) - R t)
    (hpoly : evenMoment P k T (2 * T) ≤ T * (C * (k : ℝ) * L) ^ k)
    (hshift : evenMoment (fun t => R (t + h)) k T (2 * T) ≤
      T * (C * (k : ℝ) * (k : ℝ)) ^ k)
    (hrem : evenMoment R k T (2 * T) ≤ T * (C * (k : ℝ) * (k : ℝ)) ^ k) :
    evenMoment (fun t => S (t + h) - S t) k T (2 * T) ≤
      T * (9 * C * (k : ℝ) * (L + (k : ℝ))) ^ k := by
  have hbound := increment_evenMoment_le_of_budgets S P R h T (2 * T) T
    (C * (k : ℝ) * L) (C * (k : ℝ) * (k : ℝ)) (by linarith)
    hT (by positivity) (by positivity) k hk hS hP hRh hR hdecomp hpoly hshift hrem
  rw [show 9 * (C * (k : ℝ) * L + C * (k : ℝ) * (k : ℝ)) =
    9 * C * (k : ℝ) * (L + (k : ℝ)) by ring] at hbound
  exact hbound

/-- Exact dyadic form of Tsang's high-moment theorem, stated as an unproved
research target.  The order is uniform: `C` and `T₀` precede `T`, `k`, and `h`.
Specializing `S` requires its correct continuously continued argument semantics.
Source for the statement: Tsang (1986), Theorem 4; STTB (2020), Theorem 2. -/
def TsangHighMomentAsymptotic (S : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 3 ≤ T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ k : ℕ, 1 ≤ k → ∀ h : ℝ, 0 < h → h < 1 →
      |evenMoment (fun t => S (t + h) - S t) k T (2 * T) -
        ((Nat.factorial (2 * k) : ℝ) /
          ((2 : ℝ) ^ k * Real.pi ^ (2 * k) * (Nat.factorial k : ℝ))) *
          T * (Real.log (2 + h * Real.log T)) ^ k| ≤
      T * (C * (k : ℝ)) ^ k *
        ((k : ℝ) ^ k + Real.rpow (Real.log (2 + h * Real.log T)) ((k : ℝ) - 1 / 2))

end RiemannResearch.HighMomentTransfer
