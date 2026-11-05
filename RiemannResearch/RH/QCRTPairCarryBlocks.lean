/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # A signed primitive for the centered two-prime CRT carry

After centering in both prime coordinates under uniform residues, the CRT
interaction has an explicitly nonpositive primitive. Summation by parts
therefore controls it against decreasing physical weights on complete
periods. The signed statement concerns a single interaction. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPairCarryBlocks
open ArithmeticCumulative

/-- The two-variable component of the residue fraction for coprime conductors. -/
def pairInteraction (p q n : ℕ) : ℝ :=
  residueFraction (p * q) n - residueFraction p n / q - residueFraction q n / p -
    (((p : ℝ) - 1) * ((q : ℝ) - 1)) / (2 * p * q)

private def quad (d k : ℕ) : ℝ :=
  ((k % d : ℕ) : ℝ) ^ 2 - (d : ℝ) * (k % d : ℕ)

private theorem quad_step (d k : ℕ) (hd : 2 ≤ d) :
    quad d (k + 1) - quad d k = 2 * ((k % d : ℕ) : ℝ) - d + 1 := by
  have hd' : 0 < d := by omega
  have hr := Nat.mod_lt k hd'
  have hmod : (k + 1) % d = (k % d + 1) % d := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < d)]
  by_cases h : k % d + 1 < d
  · simp only [quad, hmod, Nat.mod_eq_of_lt h, Nat.cast_add, Nat.cast_one]
    ring
  · have h' : k % d + 1 = d := by omega
    have hR : ((k % d : ℕ) : ℝ) + 1 = d := by exact_mod_cast h'
    simp only [quad, hmod, h', Nat.mod_self, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_self]
    rw [← hR]
    ring

/-- The physical prefix through n−1, periodically extended. -/
def pairPrimitive (p q n : ℕ) : ℝ :=
  (quad (p * q) n - quad p n - quad q n) / (2 * (p : ℝ) * q)

theorem pairPrimitive_step (p q k : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    pairPrimitive p q (k + 1) - pairPrimitive p q k = pairInteraction p q k := by
  have hpq : 2 ≤ p * q := by nlinarith
  have hs := quad_step (p * q) k hpq
  have h₁ := quad_step p k hp
  have h₂ := quad_step q k hq
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  simp only [pairPrimitive, pairInteraction, residueFraction, Nat.cast_mul] at *
  field_simp [hp', hq']
  linarith [hs, h₁, h₂]

theorem pairInteraction_prefix (p q t : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∑ n ∈ Finset.range t, pairInteraction p q n = pairPrimitive p q t := by
  induction t with
  | zero => simp [pairPrimitive, quad]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, ← pairPrimitive_step p q t hp hq]
    ring

/-- A nonzero residue has at least as much space before the right endpoint
of a full period as before the end of its own residue interval. -/
private theorem residue_at_right (d t k : ℕ) (hd : 0 < d) (hk : k < d * t) :
    (d : ℝ) - (k % d : ℕ) ≤ ((d * t : ℕ) : ℝ) - k := by
  have hh : k / d < t := (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using hk)
  have hi := Nat.mul_le_mul_left d (show k / d + 1 ≤ t by omega)
  rw [Nat.mul_add, Nat.mul_one] at hi
  have he := Nat.mod_add_div k d
  have hab : d + k ≤ d * t + k % d := by omega
  have hab' : (d : ℝ) + k ≤ ((d * t : ℕ) : ℝ) + (k % d : ℕ) := by exact_mod_cast hab
  linarith

private theorem subperiod_quad_bound (d t k : ℕ) (hd : 0 < d) (hk : k < d * t) :
    -quad d k ≤ ((d : ℝ) - 1) * min (k : ℝ) (((d * t : ℕ) : ℝ) - k) := by
  let u : ℝ := (k % d : ℕ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hud : u ≤ (d : ℝ) - 1 := by
    have h : k % d + 1 ≤ d := Nat.mod_lt k hd
    have hh : u + 1 ≤ d := by dsimp [u]; exact_mod_cast h
    linarith
  have hdu : 0 ≤ (d : ℝ) - u := by linarith
  have hur : u ≤ k := by dsimp [u]; exact_mod_cast Nat.mod_le k d
  have hurt : (d : ℝ) - u ≤ ((d * t : ℕ) : ℝ) - k := residue_at_right d t k hd hk
  have hbase : 0 ≤ (d : ℝ) - 1 := by linarith
  have hkR : (k : ℝ) ≤ ((d * t : ℕ) : ℝ) := by exact_mod_cast hk.le
  change - (u ^ 2 - (d : ℝ) * u) ≤ _
  by_cases hzero : k % d = 0
  · have hz : u = 0 := by simp [u, hzero]
    rw [hz]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self, neg_zero]
    exact mul_nonneg hbase (le_min (Nat.cast_nonneg k) (by linarith))
  · have hnat : 1 ≤ k % d := by omega
    have h1 : 1 ≤ u := by dsimp [u]; exact_mod_cast hnat
    apply le_trans (le_of_eq (by ring : -(u ^ 2 - (d : ℝ) * u) = u * ((d : ℝ) - u)))
    rcases le_total (k : ℝ) (((d * t : ℕ) : ℝ) - k) with h | h
    · rw [min_eq_left h, mul_comm ((d : ℝ) - 1)]
      exact mul_le_mul hur (by linarith) hdu (Nat.cast_nonneg k)
    · rw [min_eq_right h]
      exact mul_le_mul hud hurt hdu hbase

private theorem quad_reduce (d s n : ℕ) (h : d ∣ s) : quad d (n % s) = quad d n := by
  simp only [quad, Nat.mod_mod_of_dvd n h]

theorem pairPrimitive_nonpos (p q n : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    pairPrimitive p q n ≤ 0 := by
  let k := n % (p * q)
  have hp' : 0 < p := by omega
  have hq' : 0 < q := by omega
  have hk : k < p * q := Nat.mod_lt _ (Nat.mul_pos hp' hq')
  have hpB := subperiod_quad_bound p q k hp' hk
  have hqB := subperiod_quad_bound q p k hq' (by simpa [Nat.mul_comm] using hk)
  rw [Nat.mul_comm q p] at hqB
  let l : ℝ := min (k : ℝ) (((p * q : ℕ) : ℝ) - k)
  have hnon : 0 ≤ l := le_min (Nat.cast_nonneg k) (sub_nonneg.mpr (by exact_mod_cast hk.le))
  have hscale : (p : ℝ) + q - 2 ≤ ((p * q : ℕ) : ℝ) / 2 := by
    have hp2 : 0 ≤ (p : ℝ) - 2 := sub_nonneg.mpr (by exact_mod_cast hp)
    have hq2 : 0 ≤ (q : ℝ) - 2 := sub_nonneg.mpr (by exact_mod_cast hq)
    push_cast
    nlinarith [mul_nonneg hp2 hq2]
  have hpqB : ((p * q : ℕ) : ℝ) / 2 * l ≤ (k : ℝ) * (((p * q : ℕ) : ℝ) - k) := by
    dsimp only [l]
    rcases le_total (k : ℝ) (((p * q : ℕ) : ℝ) - k) with h | h
    · rw [min_eq_left h, mul_comm (k : ℝ)]
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg k)
    · rw [min_eq_right h]
      exact mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr (by exact_mod_cast hk.le))
  have hcoef := mul_le_mul_of_nonneg_right hscale hnon
  change - quad p k ≤ ((p : ℝ) - 1) * l at hpB
  change - quad q k ≤ ((q : ℝ) - 1) * l at hqB
  unfold pairPrimitive
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  rw [← quad_reduce p (p * q) n (dvd_mul_right p q), ← quad_reduce q (p * q) n (dvd_mul_left q p)]
  change (k : ℝ) ^ 2 - ((p * q : ℕ) : ℝ) * k - quad p k - quad q k ≤ _
  nlinarith [hpqB, hcoef, hpB, hqB]

theorem pairPrimitive_lower (p q n : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    -((p * q : ℕ) : ℝ) / 8 ≤ pairPrimitive p q n := by
  have hquad (d : ℕ) (hd : 0 < d) : quad d n ≤ 0 := by
    have hle : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
    have hnon : 0 ≤ ((n % d : ℕ) : ℝ) := by positivity
    dsimp [quad]
    nlinarith [mul_nonneg hnon (sub_nonneg.mpr hle)]
  have hp' : 0 < p := by omega
  have hq' : 0 < q := by omega
  have hpR : (0 : ℝ) < p := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  have hs := sq_nonneg (2 * ((n % (p * q) : ℕ) : ℝ) - ((p * q : ℕ) : ℝ))
  unfold pairPrimitive
  apply (le_div_iff₀ (by positivity)).mpr
  dsimp only [quad] at *
  push_cast at *
  nlinarith [hquad p hp', hquad q hq']

theorem pairPrimitive_zero_of_dvd (p q n : ℕ) (h : p * q ∣ n) :
    pairPrimitive p q n = 0 := by
  have h₁ : p ∣ n := (dvd_mul_right p q).trans h
  have h₂ : q ∣ n := (dvd_mul_left q p).trans h
  simp [pairPrimitive, quad, Nat.mod_eq_zero_of_dvd h, Nat.mod_eq_zero_of_dvd h₁,
    Nat.mod_eq_zero_of_dvd h₂]

theorem summation_by_parts (f w : ℕ → ℝ) (A t : ℕ) :
    (∑ k ∈ Finset.range t, (f (A + k + 1) - f (A + k)) * w (A + k)) =
      f (A + t) * w (A + t) - f A * w A +
        ∑ k ∈ Finset.range t, f (A + k + 1) * (w (A + k) - w (A + k + 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [Finset.sum_range_succ]
    rw [ih, ← Nat.add_assoc A t 1]
    ring

theorem sum_decrements (w : ℕ → ℝ) (A t : ℕ) :
    (∑ k ∈ Finset.range t, (w (A + k) - w (A + k + 1))) = w A - w (A + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, ← Nat.add_assoc A t 1]
    ring

/-- For any decreasing weights, the signed block interaction is one-sided
and controlled by the change of the weight across the block. -/
theorem weighted_pairInteraction_block (p q A t : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hA : p * q ∣ A) (hB : p * q ∣ A + t) (w : ℕ → ℝ) (hw : Antitone w) :
    -((p * q : ℕ) : ℝ) / 8 * (w A - w (A + t)) ≤
        ∑ k ∈ Finset.range t, pairInteraction p q (A + k) * w (A + k) ∧
      (∑ k ∈ Finset.range t, pairInteraction p q (A + k) * w (A + k)) ≤ 0 := by
  have he :
      (∑ k ∈ Finset.range t, pairInteraction p q (A + k) * w (A + k)) =
        ∑ k ∈ Finset.range t, pairPrimitive p q (A + k + 1) * (w (A + k) - w (A + k + 1)) := by
    simp only [← pairPrimitive_step p q _ hp hq]
    rw [summation_by_parts, pairPrimitive_zero_of_dvd p q A hA,
      pairPrimitive_zero_of_dvd p q (A + t) hB]
    ring
  rw [he]
  have hdec (k : ℕ) : 0 ≤ w (A + k) - w (A + k + 1) := sub_nonneg.mpr (hw (by omega))
  constructor
  · rw [← sum_decrements w A t, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
      (pairPrimitive_lower p q (A + k + 1) hp hq) (hdec k)
  · exact Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonpos_of_nonneg (pairPrimitive_nonpos p q (A + k + 1) hp hq) (hdec k)

/-- For the physical inverse-square weights this gives a negative signed
interaction and a loss at most pq / 8 times the change of the weight. -/
theorem inverseSquare_pairInteraction_block (p q A t : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpos : 0 < A) (hA : p * q ∣ A) (hB : p * q ∣ A + t) :
    -((p * q : ℕ) : ℝ) / 8 * (1 / (A : ℝ) ^ 2 - 1 / ((A + t : ℕ) : ℝ) ^ 2) ≤
        ∑ k ∈ Finset.range t, pairInteraction p q (A + k) / ((A + k : ℕ) : ℝ) ^ 2 ∧
      (∑ k ∈ Finset.range t, pairInteraction p q (A + k) / ((A + k : ℕ) : ℝ) ^ 2) ≤ 0 := by
  let w (j : ℕ) : ℝ := 1 / (max (1 : ℝ) (j : ℝ)) ^ 2
  have hw : Antitone w := by
    intro i j hij
    have hi : 0 < max (1 : ℝ) (i : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    apply one_div_le_one_div_of_le (sq_pos_of_pos hi)
    have hmax : max (1 : ℝ) (i : ℝ) ≤ max 1 (j : ℝ) :=
      max_le_max_left 1 (by exact_mod_cast hij)
    exact pow_le_pow_left₀ hi.le hmax 2
  have hW (k : ℕ) : w (A + k) = 1 / ((A + k : ℕ) : ℝ) ^ 2 := by
    have hk : (1 : ℝ) ≤ ((A + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ A + k by omega)
    simp only [w, max_eq_right hk]
  have hWA : w A = 1 / (A : ℝ) ^ 2 := by simpa only [Nat.add_zero] using hW 0
  simpa only [hW, hWA, mul_one_div] using weighted_pairInteraction_block p q A t hp hq hA hB w hw

end RiemannResearch.RH.QCRTPairCarryBlocks
