import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Signed Fejer remainders and prefix cancellation

The complete triangular Fourier remainder is rewritten exactly as a sum
of signed prefixes before any norm is taken. The prefix L1, prefix L2,
uniform-prefix, and sharp uniform-mode estimates give different sufficient
criteria. The alternating example shows that cancellation of a one-point
remainder does not remove its positive square contribution to a pair statistic.

Source: elementary finite summation by parts, derived for the November 11,
2026 FMZ microscopic-budget investigation. The concrete actual-zero
consumer is ActualFejerMovingFMZ. The normalization corresponds to the
nonconstant modes of the squared equal-weight prime-power probe. No
mathematical priority claim or actual-zero cancellation input is asserted.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Analysis.FejerSignedRemainder

def partialSum (e : ℕ → ℂ) (k : ℕ) : ℂ := ∑ d ∈ Finset.range k, e d

def remainder (N : ℕ) (e : ℕ → ℂ) : ℂ :=
  (2 : ℂ) / ((N : ℂ) + 1)^2 *
    ∑ d ∈ Finset.range N, ((N : ℂ) - d) * e d

theorem triangular_eq_prefix (N : ℕ) (e : ℕ → ℂ) :
    (∑ d ∈ Finset.range N, ((N : ℂ) - d) * e d) =
      ∑ k ∈ Finset.range N, partialSum e (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    have hs : (∑ d ∈ Finset.range N, ((N : ℂ) + 1 - d) * e d) =
        (∑ d ∈ Finset.range N, ((N : ℂ) - d) * e d) + partialSum e N := by
      unfold partialSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rw [hs, ih]
    simp only [partialSum, Finset.sum_range_succ]
    ring

theorem remainder_eq_prefix (N : ℕ) (e : ℕ → ℂ) :
    remainder N e = (2 : ℂ) / ((N : ℂ) + 1)^2 *
      ∑ k ∈ Finset.range N, partialSum e (k + 1) := by
  rw [remainder, triangular_eq_prefix]

theorem norm_remainder_le_prefix (N : ℕ) (e : ℕ → ℂ) :
    ‖remainder N e‖ ≤ 2 / ((N : ℝ) + 1)^2 *
      ∑ k ∈ Finset.range N, ‖partialSum e (k + 1)‖ := by
  rw [remainder_eq_prefix, norm_mul, norm_div, norm_pow]
  have he : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
    have hc : (N : ℂ) + 1 = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [he, htwo]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem norm_remainder_le_uniform_prefix (N : ℕ) (e : ℕ → ℂ) (B : ℝ)
    (hB : ∀ k < N, ‖partialSum e (k + 1)‖ ≤ B) :
    ‖remainder N e‖ ≤ 2 * (N : ℝ) * B / ((N : ℝ) + 1)^2 := by
  calc
    _ ≤ 2 / ((N : ℝ) + 1)^2 * ∑ k ∈ Finset.range N, ‖partialSum e (k + 1)‖ :=
      norm_remainder_le_prefix N e
    _ ≤ 2 / ((N : ℝ) + 1)^2 * ∑ _k ∈ Finset.range N, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk =>
        hB k (Finset.mem_range.mp hk))) (by positivity)
    _ = _ := by simp; ring

theorem norm_remainder_le_prefix_ratio (N : ℕ) (e : ℕ → ℂ) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ k < N, ‖partialSum e (k + 1)‖ ≤ B) :
    ‖remainder N e‖ ≤ 2 * (B / ((N : ℝ) + 1)) := by
  apply (norm_remainder_le_uniform_prefix N e B hB).trans
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  field_simp
  nlinarith

theorem tendsto_remainder_of_prefix {α : Type*} {l : Filter α}
    (N : α → ℕ) (e : α → ℕ → ℂ) (B : α → ℝ)
    (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a k, k < N a → ‖partialSum (e a) (k + 1)‖ ≤ B a)
    (hsmall : Tendsto (fun a => B a / ((N a : ℝ) + 1)) l (𝓝 0)) :
    Tendsto (fun a => remainder (N a) (e a)) l (𝓝 0) := by
  have hl := hsmall.const_mul 2
  simp only [mul_zero] at hl
  exact squeeze_zero_norm (fun a => norm_remainder_le_prefix_ratio
    (N a) (e a) (B a) (hB0 a) (hB a)) hl

theorem prefix_difference (f : ℕ → ℂ) (k : ℕ) :
    partialSum (fun d => f (d + 1) - f d) k = f k - f 0 := by
  induction k with
  | zero => simp [partialSum]
  | succ k ih =>
    simp only [partialSum, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    ring

theorem norm_remainder_difference (N : ℕ) (f : ℕ → ℂ) (B : ℝ)
    (hf : ∀ k ≤ N, ‖f k - f 0‖ ≤ B) :
    ‖remainder N (fun d => f (d + 1) - f d)‖ ≤
      2 * (N : ℝ) * B / ((N : ℝ) + 1)^2 := by
  apply norm_remainder_le_uniform_prefix
  intro k hk
  rw [prefix_difference]
  exact hf (k + 1) (by omega)

theorem remainder_add (N : ℕ) (e f : ℕ → ℂ) :
    remainder N (fun d => e d + f d) = remainder N e + remainder N f := by
  simp only [remainder, mul_add, Finset.sum_add_distrib]

theorem sum_weights (N : ℕ) :
    (∑ d ∈ Finset.range N, ((N : ℝ) - d)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have he : (∑ d ∈ Finset.range N, ((N : ℝ) + 1 - d)) =
        (∑ d ∈ Finset.range N, ((N : ℝ) - d)) + (N : ℝ) := by
      simp_rw [show ∀ d : ℕ, (N : ℝ) + 1 - d = ((N : ℝ) - d) + 1 by intro d; ring]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
    rw [he, ih]
    ring

theorem remainder_const (N : ℕ) (z : ℂ) :
    remainder N (fun _ => z) = (N : ℂ) / ((N : ℂ) + 1) * z := by
  have hs : (∑ d ∈ Finset.range N, ((N : ℂ) - d)) =
      (N : ℂ) * ((N : ℂ) + 1) / 2 := by
    have hh := congrArg Complex.ofReal (sum_weights N)
    push_cast at hh
    exact hh
  rw [remainder, ← Finset.sum_mul, hs]
  have hn : (N : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
  field_simp

theorem norm_remainder_le_modes (N : ℕ) (e : ℕ → ℂ) (ε : ℝ)
    (he : ∀ d < N, ‖e d‖ ≤ ε) :
    ‖remainder N e‖ ≤ (N : ℝ) / ((N : ℝ) + 1) * ε := by
  have hcoef : ‖(2 : ℂ) / ((N : ℂ) + 1)^2‖ = 2 / ((N : ℝ) + 1)^2 := by
    have hc : (N : ℂ) + 1 = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [norm_div, norm_pow, hc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    norm_num
  have hw (d : ℕ) (hd : d < N) : ‖(N : ℂ) - d‖ = (N : ℝ) - d := by
    have hdn : (d : ℝ) ≤ N := by exact_mod_cast hd.le
    rw [← Complex.ofReal_natCast N, ← Complex.ofReal_natCast d,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hdn)]
  rw [remainder, norm_mul, hcoef]
  calc
    _ ≤ 2 / ((N : ℝ) + 1)^2 * ∑ d ∈ Finset.range N, ‖((N : ℂ) - d) * e d‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ 2 / ((N : ℝ) + 1)^2 * ∑ d ∈ Finset.range N, ((N : ℝ) - d) * ε := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro d hd
      have hdN := Finset.mem_range.mp hd
      rw [norm_mul, hw d hdN]
      exact mul_le_mul_of_nonneg_left (he d hdN)
        (sub_nonneg.mpr (by exact_mod_cast hdN.le))
    _ = _ := by
      rw [← Finset.sum_mul, sum_weights]
      have hn : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp

/-- A mean-square prefix alternative, retaining cancellation inside each prefix. -/
theorem norm_remainder_sq_le_prefix_energy (N : ℕ) (e : ℕ → ℂ) :
    ‖remainder N e‖^2 ≤ 4 * (N : ℝ) / ((N : ℝ) + 1)^4 *
      ∑ k ∈ Finset.range N, ‖partialSum e (k+1)‖^2 := by
  have hs := mul_self_le_mul_self (norm_nonneg _) (norm_remainder_le_prefix N e)
  rw [← sq, ← sq] at hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun _ => (1 : ℝ)) (fun k => ‖partialSum e (k+1)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ (2 / ((N : ℝ) + 1)^2 * ∑ k ∈ Finset.range N, ‖partialSum e (k+1)‖)^2 := hs
    _ = 4 / ((N : ℝ) + 1)^4 * (∑ k ∈ Finset.range N, ‖partialSum e (k+1)‖)^2 := by
      field_simp
      <;> ring
    _ ≤ 4 / ((N : ℝ) + 1)^4 *
        ((N : ℝ) * ∑ k ∈ Finset.range N, ‖partialSum e (k+1)‖^2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

theorem partialSum_alternating (k : ℕ) :
    partialSum (fun d => (-1 : ℂ)^d) k = (1 - (-1 : ℂ)^k) / 2 := by
  induction k with
  | zero => simp [partialSum]
  | succ k ih =>
    simp only [partialSum, Finset.sum_range_succ] at ih ⊢
    rw [ih, pow_succ]
    ring

theorem alternating_prefix_bound (k : ℕ) :
    ‖partialSum (fun d => (-1 : ℂ)^d) k‖ ≤ 1 := by
  rw [partialSum_alternating, norm_div]
  have ht : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [ht]
  calc
    _ ≤ (‖(1 : ℂ)‖ + ‖(-1 : ℂ)^k‖) / 2 :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = 1 := by simp

theorem norm_remainder_alternating_le (N : ℕ) :
    ‖remainder N (fun d => (-1 : ℂ)^d)‖ ≤ 2 * (N : ℝ) / ((N : ℝ)+1)^2 := by
  simpa only [mul_one] using norm_remainder_le_uniform_prefix N
    (fun d => (-1 : ℂ)^d) 1 (fun k _ => alternating_prefix_bound (k+1))

/-- Signed one-point cancellation does not remove the positive pair-square error. -/
theorem alternating_square_remainder (N : ℕ) :
    remainder N (fun d => ((‖(-1 : ℂ)^d‖^2 : ℝ) : ℂ)) =
      (N : ℂ) / ((N : ℂ)+1) := by
  simp only [norm_pow, norm_neg, norm_one, one_pow, Complex.ofReal_one]
  simpa using remainder_const N 1

#print axioms triangular_eq_prefix
#print axioms tendsto_remainder_of_prefix
end RiemannResearch.Analysis.FejerSignedRemainder
