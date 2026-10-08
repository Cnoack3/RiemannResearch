/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTPolygammaSigns
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-!
# Exact polygamma residue weights for the inverse-square law

Source: user-provided optimizer-cancellation argument, 8 October 2026.
The special-function identification uses the actual iterated derivatives of
the real restriction of `Complex.digamma`, as established in
`CRTPolygammaSigns`; the classical series is DLMF 5.15.1,
https://dlmf.nist.gov/5.15#E1. The scale and normalization are retained at
every order. Exact prefix/tail decompositions do not discard any atom.

The representative `a = L` is included: it represents residue zero while
keeping every argument strictly positive. No limiting approximation or RH
assumption enters these identities.
-/

open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoProbability
noncomputable section
open CRTBlock

/-- The complete arithmetic progression mass for the order-`s` reciprocal
coordinate moment of the inverse-square probability law. -/
def residuePowerWeight (s : ℕ) (L a : ℝ) : ℝ :=
  ∑' j : ℕ, 1 / (zetaTwo * (a + (j : ℝ) * L) ^ (s + 2))

theorem residuePowerTerm_scale (s : ℕ) (L a k : ℝ) (hL : L ≠ 0) :
    1 / (zetaTwo * (a + k * L) ^ (s + 2)) =
      (1 / (zetaTwo * L ^ (s + 2))) *
        (1 / (k + a / L) ^ (s + 2)) := by
  have he : a + k * L = L * (k + a / L) := by field_simp; ring
  rw [he, mul_pow]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem residuePowerWeight_summable (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    Summable (fun j : ℕ =>
      1 / (zetaTwo * (a + (j : ℝ) * L) ^ (s + 2))) := by
  have h := (reciprocalPowerSeries_summable s (div_pos ha hL)).mul_left
    (1 / (zetaTwo * L ^ (s + 2)))
  exact h.congr (fun j => (residuePowerTerm_scale s L a j (ne_of_gt hL)).symm)

theorem residuePowerWeight_eq_series (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    residuePowerWeight s L a =
      reciprocalPowerSeries s (a / L) / (zetaTwo * L ^ (s + 2)) := by
  simp_rw [residuePowerWeight, residuePowerTerm_scale s L a _ (ne_of_gt hL)]
  rw [tsum_mul_left]
  unfold reciprocalPowerSeries
  ring

/-- The exact all-order residue formula in actual polygamma derivatives. -/
theorem residuePowerWeight_eq_polygamma (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    residuePowerWeight s L a =
      (-1 : ℝ) ^ (s + 2) * iteratedDeriv (s + 1) realDigamma (a / L) /
        (zetaTwo * ((s + 1).factorial : ℝ) * L ^ (s + 2)) := by
  have hsign : (-1 : ℝ) ^ s * (-1 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have hsign2 : (-1 : ℝ) ^ (s + 2) = (-1 : ℝ) ^ s := by
    rw [pow_add]
    norm_num
  have hfac : ((s + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [residuePowerWeight_eq_series s hL ha, hsign2,
    iteratedDeriv_digamma_series s (div_pos ha hL)]
  have he : (-1 : ℝ) ^ s *
      ((-1 : ℝ) ^ s * ((s + 1).factorial : ℝ) *
        reciprocalPowerSeries s (a / L)) =
      ((s + 1).factorial : ℝ) * reciprocalPowerSeries s (a / L) := by
    calc
      _ = ((-1 : ℝ) ^ s * (-1 : ℝ) ^ s) *
        ((s + 1).factorial : ℝ) * reciprocalPowerSeries s (a / L) := by ring
      _ = _ := by rw [hsign]; ring
  rw [he]
  field_simp [hfac, ne_of_gt hL, ne_of_gt zetaTwo_pos]
  <;> ring

/-- In order zero the progression mass is the actual trigamma divided by
the complete normalization and scale. -/
theorem residueSquareWeight_eq_trigamma {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    residuePowerWeight 0 L a = trigamma (a / L) / (zetaTwo * L ^ 2) := by
  rw [residuePowerWeight_eq_series 0 hL ha]
  simp only [reciprocalPowerSeries, Nat.zero_add,
    trigamma_eq_series (div_pos ha hL)]

theorem residuePowerWeight_pos (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    0 < residuePowerWeight s L a := by
  exact (residuePowerWeight_summable s hL ha).tsum_pos
    (fun j => by have hz := zetaTwo_pos; positivity) 0
    (by have hz := zetaTwo_pos; positivity)

/-- The exact finite prefix and the identical shifted infinite tail. -/
theorem residuePowerWeight_prefix_exact (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) (N : ℕ) :
    residuePowerWeight s L a =
      (∑ j ∈ Finset.range N,
        1 / (zetaTwo * (a + (j : ℝ) * L) ^ (s + 2))) +
      residuePowerWeight s L (a + (N : ℝ) * L) := by
  have h := (residuePowerWeight_summable s hL ha).sum_add_tsum_nat_add N
  simpa only [residuePowerWeight, Nat.cast_add, add_mul,
    add_assoc, add_left_comm, add_comm] using h.symm

/-- One-step recurrence retains the first progression atom exactly. -/
theorem residuePowerWeight_shift (s : ℕ) {L a : ℝ}
    (hL : 0 < L) (ha : 0 < a) :
    residuePowerWeight s L a =
      1 / (zetaTwo * a ^ (s + 2)) + residuePowerWeight s L (a + L) := by
  simpa using residuePowerWeight_prefix_exact s hL ha 1

/-- Literal inverse-power expectation, indexed by all positive integers. -/
def inversePowerMean (s : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, f (k + 1) / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ (s + 2))

theorem inversePowerMean_summable_of_bounded (s : ℕ) (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) :
    Summable (fun k : ℕ =>
      f (k + 1) / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ (s + 2))) := by
  have hw : Summable (fun k : ℕ =>
      1 / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ (s + 2))) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using
      residuePowerWeight_summable s (by norm_num : (0 : ℝ) < 1)
        (by norm_num : (0 : ℝ) < 1)
  have hC : Summable (fun k : ℕ =>
      C / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ (s + 2))) := by
    exact (hw.mul_left C).congr (fun k => by ring)
  apply Summable.of_norm_bounded hC
  intro k
  have hz := zetaTwo_pos
  have hzden : 0 < zetaTwo * ((k + 1 : ℕ) : ℝ) ^ (s + 2) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hzden]
  exact div_le_div_of_nonneg_right (hf (k + 1)) hzden.le

/-- The exact positive-integer expectation is its finite residue sum.
The zero congruence class is retained by the representative `L`. -/
theorem periodic_inversePowerMean (s L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ k, |f k| ≤ C)
    (hp : ∀ k, f (k + L) = f k) :
    inversePowerMean s f =
      ∑ r : Fin L, residuePowerWeight s L (r.val + 1) * f (r.val + 1) := by
  cases L with
  | zero => omega
  | succ n =>
    let g : ℕ → ℝ := fun k =>
      f (k + 1) / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ (s + 2))
    have hg : Summable g := inversePowerMean_summable_of_bounded s f hf
    calc
      inversePowerMean s f = ∑' k, g k := rfl
      _ = ∑ r : Fin (n + 1), ∑' j : ℕ, g (r.val + (n + 1) * j) :=
        Nat.sumByResidueClasses hg (n + 1)
      _ = ∑ r : Fin (n + 1),
          residuePowerWeight s ((n + 1 : ℕ) : ℝ) (r.val + 1) * f (r.val + 1) := by
        apply Finset.sum_congr rfl
        intro r _
        have he (j : ℕ) : g (r.val + (n + 1) * j) =
            (1 / (zetaTwo * (((r.val + 1 : ℕ) : ℝ) +
              (j : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ (s + 2))) * f (r.val + 1) := by
          change f (r.val + (n + 1) * j + 1) /
            (zetaTwo * ((r.val + (n + 1) * j + 1 : ℕ) : ℝ) ^ (s + 2)) = _
          have hh : r.val + (n + 1) * j + 1 =
              r.val + 1 + (n + 1) * j := by omega
          rw [hh, Pareto.periodic_add_mul (n + 1) f hp]
          push_cast
          ring
        simp_rw [he]
        rw [tsum_mul_right]
        simp only [residuePowerWeight, Nat.cast_add, Nat.cast_one]

/-- The physical mixed moment retains every signed cross term after residue
regrouping. This applies directly to periodic residue atoms and optimizers. -/
theorem periodic_inversePowerMean_mul (s L : ℕ) (hL : 0 < L)
    (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hpf : ∀ k, f (k + L) = f k) (hpg : ∀ k, g (k + L) = g k) :
    inversePowerMean s (fun k => f k * g k) =
      ∑ r : Fin L, residuePowerWeight s L (r.val + 1) *
        (f (r.val + 1) * g (r.val + 1)) := by
  exact periodic_inversePowerMean s L hL (fun k => f k * g k)
    (Pareto.bounded_product hf hg) (by intro k; rw [hpf, hpg])

/-- The literal arithmetic moment as a finite sum of actual polygamma
derivatives. In particular the residue `L` is not omitted. -/
theorem periodic_inversePowerMean_eq_polygamma (s L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ k, |f k| ≤ C)
    (hp : ∀ k, f (k + L) = f k) :
    inversePowerMean s f =
      ∑ r : Fin L,
        ((-1 : ℝ) ^ (s + 2) *
          iteratedDeriv (s + 1) realDigamma (((r.val + 1 : ℕ) : ℝ) / L) /
          (zetaTwo * ((s + 1).factorial : ℝ) * (L : ℝ) ^ (s + 2))) *
        f (r.val + 1) := by
  rw [periodic_inversePowerMean s L hL f hf hp]
  apply Finset.sum_congr rfl
  intro r _
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [residuePowerWeight_eq_polygamma s hLr (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]

end
end RiemannResearch.RH.ZetaTwoProbability
