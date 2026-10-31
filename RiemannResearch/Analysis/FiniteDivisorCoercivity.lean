/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite divisor coercivity with an improved head factor

Source: SquarefreeShortHeadSchurResearch20261030.md, sections 2--3,
and the subsequent user-requested Lean improvement, 31 October 2026.
The finite dilation contraction and Mobius convolution retain all divisors.
The normalized difference estimate improves the paper factor 4 to
(2 - 1/H)^2 at every positive cutoff. No RH estimate is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteDivisorCoercivity

def energy (H : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), f n ^ 2

def backward (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f (n - 1)

theorem energy_nonneg (H : ℕ) (f : ℕ → ℝ) : 0 ≤ energy H f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem backward_energy_exact (H : ℕ) (f : ℕ → ℝ) :
    energy H (backward f) = ∑ n ∈ Finset.range H, f n ^ 2 := by
  induction H with
  | zero => simp [energy, backward]
  | succ H ih =>
      change (∑ n ∈ Finset.range (H + 1 + 1), backward f n ^ 2) = _
      rw [Finset.sum_range_succ]
      change energy H (backward f) + backward f (H + 1) ^ 2 = _
      rw [ih, Finset.sum_range_succ]
      simp [backward]

theorem backward_energy_le (H : ℕ) (f : ℕ → ℝ) :
    energy H (backward f) ≤ energy H f := by
  rw [backward_energy_exact]
  unfold energy
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Scalar weighted Young inequality retaining its exact nonnegative square. -/
theorem difference_square_exact (x y t : ℝ) :
    (1 + t) * (x ^ 2 + t * y ^ 2) - (x - t * y) ^ 2 =
      t * (x + y) ^ 2 := by ring

theorem difference_square_le (x y t a : ℝ)
    (ht : 0 ≤ t) (hta : t ≤ a) :
    (x - t * y) ^ 2 ≤ (1 + a) * (x ^ 2 + a * y ^ 2) := by
  have ha : 0 ≤ a := ht.trans hta
  have hfirst : (x - t * y) ^ 2 ≤ (1 + t) * (x ^ 2 + t * y ^ 2) := by
    have h := difference_square_exact x y t
    nlinarith [mul_nonneg ht (sq_nonneg (x + y))]
  apply hfirst.trans
  exact mul_le_mul (by linarith) (by nlinarith [sq_nonneg y])
    (by positivity) (by positivity)

/-- A finite weighted backward shift gives the sharper factor (1+a)^2. -/
theorem finite_difference_energy_le (H : ℕ) (f t : ℕ → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (ht : ∀ n ∈ Finset.range (H + 1), 0 ≤ t n ∧ t n ≤ a) :
    energy H (fun n => f n - t n * backward f n) ≤
      (1 + a) ^ 2 * energy H f := by
  calc
    _ ≤ ∑ n ∈ Finset.range (H + 1),
        (1 + a) * (f n ^ 2 + a * backward f n ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact difference_square_le _ _ _ _ (ht n hn).1 (ht n hn).2
    _ = (1 + a) * (energy H f + a * energy H (backward f)) := by
      simp only [energy, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ (1 + a) * (energy H f + a * energy H f) := by
      gcongr
      exact backward_energy_le H f
    _ = _ := by ring

def dilation (a : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if a ∣ n then f (n / a) else 0

/-- Exact positive-divisor reindexing; the zero coordinate is retained. -/
theorem sum_dilation (a H : ℕ) (ha : 0 < a) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.range (H + 1), if a ∣ n then F (n / a) else 0) =
      ∑ r ∈ Finset.range (H / a + 1), F r := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun n _ => n / a) ?_ ?_ ?_ ?_
  · intro n hn
    have hnH : n ≤ H := Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right hnH))
  · intro n hn m hm he
    have hn' := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hm' := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    calc
      n = (n / a) * a := hn'.symm
      _ = (m / a) * a := by rw [he]
      _ = m := hm'
  · intro r hr
    have hrH : r * a ≤ H := (Nat.le_div_iff_mul_le ha).mp
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    have hd : a ∣ r * a := ⟨r, by ring⟩
    have hq : (r * a) / a = r := by
      apply Nat.eq_of_mul_eq_mul_left ha
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hd
    exact ⟨r * a, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hrH), hd⟩, hq⟩
  · intro n hn
    rfl

theorem dilation_energy_le (a H : ℕ) (ha : 0 < a) (f : ℕ → ℝ) :
    energy H (dilation a f) ≤ energy H f := by
  unfold energy dilation
  simp only [ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [sum_dilation a H ha (fun n => f n ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self H a)))
    (fun _ _ _ => sq_nonneg _)

/-- Finite real Young inequality for a family of energy contractions. -/
theorem finite_combination_energy_le {ι : Type*} (s : Finset ι)
    (H : ℕ) (a : ι → ℝ) (X : ι → ℕ → ℝ) (E : ℝ)
    (hX : ∀ i ∈ s, energy H (X i) ≤ E) :
    energy H (fun n => ∑ i ∈ s, a i * X i n) ≤
      (∑ i ∈ s, |a i|) ^ 2 * E := by
  have hw : 0 ≤ ∑ i ∈ s, |a i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp (n : ℕ) :
      (∑ i ∈ s, a i * X i n) ^ 2 ≤
        (∑ i ∈ s, |a i|) * ∑ i ∈ s, |a i| * (X i n) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun _ _ => abs_nonneg _) (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro i hi
    have he : (a i * X i n) ^ 2 = |a i| * (|a i| * (X i n) ^ 2) := by
      rw [mul_pow, ← sq_abs (a i)]
      ring
    exact he.le
  calc
    _ ≤ ∑ n ∈ Finset.range (H + 1),
        (∑ i ∈ s, |a i|) * ∑ i ∈ s, |a i| * (X i n) ^ 2 :=
      Finset.sum_le_sum (fun n _ => hp n)
    _ = (∑ i ∈ s, |a i|) * ∑ i ∈ s, |a i| * energy H (X i) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      rfl
    _ ≤ (∑ i ∈ s, |a i|) * ∑ i ∈ s, |a i| * E := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hX i hi) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

def mobiusMass (H : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 H, |(ArithmeticFunction.moebius a : ℝ)| / (a : ℝ)

def mobiusDilation (H : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 H,
    ((ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) * dilation a f n

theorem mobius_dilation_energy_le (H : ℕ) (f : ℕ → ℝ) :
    energy H (mobiusDilation H f) ≤ mobiusMass H ^ 2 * energy H f := by
  have h := finite_combination_energy_le (Finset.Icc 1 H) H
    (fun a => (ArithmeticFunction.moebius a : ℝ) / (a : ℝ))
    (fun a => dilation a f) (energy H f)
    (fun a ha => dilation_energy_le a H (by
      have := (Finset.mem_Icc.mp ha).1
      omega) f)
  have habs (a : ℕ) : |(a : ℝ)| = (a : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg a)
  dsimp only [mobiusDilation, energy]
  dsimp only [energy] at h
  simpa only [mobiusDilation, mobiusMass, abs_div, habs] using h

def normalizedDifference (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (f n - f (n - 1)) / (n : ℝ)

def headDifferenceFactor (H : ℕ) : ℝ :=
  2 - 1 / (H : ℝ)

theorem normalized_difference_energy_le (H : ℕ) (hH : 1 ≤ H)
    (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    energy H (normalizedDifference f) ≤
      headDifferenceFactor H ^ 2 * energy H (fun n => f n / (n : ℝ)) := by
  let a : ℝ := ((H - 1 : ℕ) : ℝ) / (H : ℝ)
  let t : ℕ → ℝ := fun n => ((n - 1 : ℕ) : ℝ) / (n : ℝ)
  let u : ℕ → ℝ := fun n => f n / (n : ℝ)
  have hHR : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht : ∀ n ∈ Finset.range (H + 1), 0 ≤ t n ∧ t n ≤ a := by
    intro n hn
    refine ⟨by dsimp [t]; positivity, ?_⟩
    by_cases hn0 : n = 0
    · subst n
      simpa [t] using ha
    have hn1 : 1 ≤ n := by omega
    have hnH : n ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    dsimp [t, a]
    rw [Nat.cast_sub hn1, Nat.cast_sub hH]
    push_cast
    apply (div_le_div_iff₀ hnR hHR).mpr
    have hle : (n : ℝ) ≤ H := by exact_mod_cast hnH
    nlinarith
  have he : normalizedDifference f = fun n => u n - t n * backward u n := by
    funext n
    by_cases hn0 : n = 0
    · subst n
      simp [normalizedDifference, u, t, backward]
    by_cases hn1 : n = 1
    · subst n
      simp [normalizedDifference, u, t, backward, hf0]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hnprev : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    simp only [normalizedDifference, u, t, backward, if_neg hn0]
    field_simp [hnR, hnprev]
  have hc : 1 + a = headDifferenceFactor H := by
    dsimp [a, headDifferenceFactor]
    rw [Nat.cast_sub hH]
    push_cast
    field_simp [hHR.ne']
    ring
  rw [he]
  simpa only [hc] using finite_difference_energy_le H u t a ha ht


theorem mobiusMass_nonneg (H : ℕ) : 0 ≤ mobiusMass H := by
  unfold mobiusMass
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem reciprocal_Icc_eq_harmonic (H : ℕ) :
    (∑ a ∈ Finset.Icc 1 H, 1 / (a : ℝ)) = (harmonic H : ℝ) := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring

theorem mobiusMass_le_harmonic (H : ℕ) :
    mobiusMass H ≤ (harmonic H : ℝ) := by
  rw [← reciprocal_Icc_eq_harmonic]
  apply Finset.sum_le_sum
  intro a ha
  have hmu : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
  exact div_le_div_of_nonneg_right hmu (Nat.cast_nonneg a)

theorem mobiusMass_le_log (H : ℕ) :
    mobiusMass H ≤ 1 + Real.log (H : ℝ) :=
  (mobiusMass_le_harmonic H).trans (harmonic_le_one_add_log H)

theorem one_le_mobiusMass (H : ℕ) (hH : 1 ≤ H) : 1 ≤ mobiusMass H := by
  have h := Finset.single_le_sum
    (f := fun a : ℕ => |(ArithmeticFunction.moebius a : ℝ)| / (a : ℝ))
    (fun a ha => by positivity)
    (Finset.mem_Icc.mpr ⟨le_rfl, hH⟩)
  simpa [mobiusMass] using h

theorem headDifferenceFactor_bounds (H : ℕ) (hH : 1 ≤ H) :
    1 ≤ headDifferenceFactor H ∧ headDifferenceFactor H < 2 := by
  have hHR : (0 : ℝ) < H := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hq : 1 / (H : ℝ) ≤ 1 := (div_le_one hHR).mpr hH1
  have hqp : 0 < 1 / (H : ℝ) := one_div_pos.mpr hHR
  dsimp only [headDifferenceFactor]
  constructor <;> linarith

/-- The finite-head improvement is strict at every positive cutoff. -/
theorem improved_constant_lt_four (H : ℕ) (hH : 1 ≤ H) :
    (headDifferenceFactor H * mobiusMass H) ^ 2 < 4 * mobiusMass H ^ 2 := by
  have hf := headDifferenceFactor_bounds H hH
  have hm := one_le_mobiusMass H hH
  have hsq : headDifferenceFactor H ^ 2 < 4 := by nlinarith
  have hpos : 0 < mobiusMass H ^ 2 := by nlinarith
  have h := mul_lt_mul_of_pos_right hsq hpos
  simpa only [mul_pow] using h


end RiemannResearch.Analysis.FiniteDivisorCoercivity
