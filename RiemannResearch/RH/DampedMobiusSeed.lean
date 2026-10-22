import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.MertensElementary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic of the damped Möbius seed

Source: user-provided argument, `norm_obligation_proved.md`, §3--4,
and the September 10 continuation of
`RH_Two_Seed_Signed_Tail_Repair_Handoff_2026-09-09.md`.

This file proves the finite arithmetic identity used before equation (N16)
of `norm_obligation_proved.md`, with the actual `Pareto.dilation` and
`Pareto.residue` definitions and Mathlib's Möbius function.

No quantitative Mertens bound or infinite quotient-norm estimate is asserted.
In particular, the results below do not supply the uniform estimates (N9)--(N15).
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The locally finite floor convolution of an arithmetic coefficient sequence. -/
def arithmeticFloorPrefix (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (k + 1), w m * (k / m : ℕ)

/-- The same convolution can be evaluated with any larger finite cutoff. -/
theorem arithmeticFloorPrefix_eq_sum {w : ℕ → ℝ} {k N : ℕ} (hkN : k ≤ N) :
    arithmeticFloorPrefix w k =
      ∑ m ∈ Finset.range (N + 1), w m * (k / m : ℕ) := by
  unfold arithmeticFloorPrefix
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkN))
  intro m hm hmk
  have hkm : k < m := by
    simp only [Finset.mem_range] at hmk
    omega
  simp [Nat.div_eq_of_lt hkm]

/-- The residue of a quotient is an exact difference of two integer floors. -/
theorem residue_div_eq_floor_sub (p m k : ℕ) :
    residue p (k / m) =
      (k / m : ℕ) - (p : ℝ) * ((k / p) / m : ℕ) := by
  have h : k / m % p + p * ((k / m) / p) = k / m :=
    Nat.mod_add_div (k / m) p
  have hR : ((k / m % p : ℕ) : ℝ) +
      (p : ℝ) * (((k / m) / p : ℕ) : ℝ) = (k / m : ℕ) := by
    exact_mod_cast h
  have hd : (k / m) / p = (k / p) / m := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm m p]
  rw [hd] at hR
  unfold residue
  linarith

/-- Exact pointwise cancellation of the normalization of an integer dilation. -/
theorem normalized_dilation_residue (w : ℕ → ℝ) (p m k : ℕ) :
    (w m / (m : ℝ)) * dilation m (residue p) k =
      w m * residue p (k / m) := by
  by_cases hm : m = 0
  · simp [hm, dilation, residue]
  · have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    unfold dilation
    field_simp

/-- Exact single-seed inverse, including the complete signed floor subtraction. -/
theorem arithmeticFloorPrefix_seed_identity (w : ℕ → ℝ) (p k : ℕ) :
    (∑ m ∈ Finset.range (k + 1),
      (w m / (m : ℝ)) * dilation m (residue p) k) =
      arithmeticFloorPrefix w k -
        (p : ℝ) * arithmeticFloorPrefix w (k / p) := by
  rw [arithmeticFloorPrefix_eq_sum (Nat.div_le_self k p)]
  unfold arithmeticFloorPrefix
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [normalized_dilation_residue, residue_div_eq_floor_sub]
  ring

/-- The exact discrepancy after subtraction of an arbitrary linear density. -/
def arithmeticFloorDefect (w : ℕ → ℝ) (κ : ℝ) (k : ℕ) : ℝ :=
  arithmeticFloorPrefix w k - κ * k

/-- Linear density cancellation leaves precisely the residue term. -/
theorem arithmeticFloorPrefix_centered_seed_identity
    (w : ℕ → ℝ) (κ : ℝ) (p k : ℕ) :
    (∑ m ∈ Finset.range (k + 1),
      (w m / (m : ℝ)) * dilation m (residue p) k) =
      κ * residue p k + arithmeticFloorDefect w κ k -
        dilation p (arithmeticFloorDefect w κ) k := by
  rw [arithmeticFloorPrefix_seed_identity]
  unfold arithmeticFloorDefect dilation
  have hres := residue_div_eq_floor_sub p 1 k
  simp only [Nat.div_one] at hres
  rw [hres]
  ring

/-- Divisor summation equals the locally finite floor convolution.
This is the exact finite regrouping defining the arithmetic prefix `Aε`. -/
theorem arithmeticFloorPrefix_eq_sum_divisors
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (N : ℕ) :
    arithmeticFloorPrefix w N =
      ∑ n ∈ Finset.range (N + 1), ∑ m ∈ n.divisors, w m := by
  let F : ℕ → ℕ → ℝ := fun k l => if l = 0 then 0 else w k
  have hF0 : ∀ l, F 0 l = 0 := by intro l; simp [F, hw0]
  have hF1 : ∀ k, F k 0 = 0 := by intro k; simp [F]
  have hlocal (n : ℕ) :
      (∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2) =
        ∑ m ∈ n.divisors, w m := by
    calc
      _ = ∑ p ∈ n.divisorsAntidiagonal, w p.1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp2 : p.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
        simp [F, hp2]
      _ = _ := Nat.sum_divisorsAntidiagonal (fun k _ => w k)
  symm
  simp_rw [← hlocal]
  rw [Nat.sum_divisorsAntidiagonal_range N F hF0 hF1]
  unfold arithmeticFloorPrefix
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0, F, hw0]
  · simpa only [F, mul_comm] using RiemannResearch.RH.sum_floor_weight N k hk0 (w k)

/-- The actual Möbius weight with real damping; zero is automatically harmless. -/
def dampedMobiusWeight (ε : ℝ) (m : ℕ) : ℝ :=
  (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) ^ (-ε)

@[simp] theorem dampedMobiusWeight_zero (ε : ℝ) : dampedMobiusWeight ε 0 = 0 := by
  simp [dampedMobiusWeight]

@[simp] theorem dampedMobiusWeight_at_zero (m : ℕ) :
    dampedMobiusWeight 0 m = (ArithmeticFunction.moebius m : ℝ) := by
  simp [dampedMobiusWeight]

/-- Identification with the precise coefficient `μ(m)/m^(1+ε)` in the handoff. -/
theorem dampedMobiusWeight_div (ε : ℝ) (m : ℕ) :
    dampedMobiusWeight ε m / (m : ℝ) =
      (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ (1 + ε) := by
  by_cases hm : m = 0
  · simp [hm]
  · have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [dampedMobiusWeight, Real.rpow_neg (le_of_lt hmR), Real.rpow_add hmR,
      Real.rpow_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The prefix from the ordinary proof, using genuine Möbius coefficients. -/
def dampedMobiusPrefix (ε : ℝ) (k : ℕ) : ℝ :=
  arithmeticFloorPrefix (dampedMobiusWeight ε) k

theorem dampedMobiusPrefix_eq_sum_divisors (ε : ℝ) (k : ℕ) :
    dampedMobiusPrefix ε k =
      ∑ n ∈ Finset.range (k + 1), ∑ m ∈ n.divisors,
        (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) ^ (-ε) := by
  exact arithmeticFloorPrefix_eq_sum_divisors _ (dampedMobiusWeight_zero ε) k

/-- The raw finite identity underlying (N16), without any analytic hypothesis. -/
theorem dampedMobius_seed_identity (ε : ℝ) (p k : ℕ) :
    (∑ m ∈ Finset.range (k + 1),
      ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ (1 + ε)) *
        dilation m (residue p) k) =
      dampedMobiusPrefix ε k - (p : ℝ) * dampedMobiusPrefix ε (k / p) := by
  simp_rw [← dampedMobiusWeight_div]
  exact arithmeticFloorPrefix_seed_identity (dampedMobiusWeight ε) p k

/-- The signed linear-density compensation is exact for every finite coordinate. -/
theorem dampedMobius_centered_seed_identity (ε κ : ℝ) (p k : ℕ) :
    (∑ m ∈ Finset.range (k + 1),
      ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ (1 + ε)) *
        dilation m (residue p) k) =
      κ * residue p k + arithmeticFloorDefect (dampedMobiusWeight ε) κ k -
        dilation p (arithmeticFloorDefect (dampedMobiusWeight ε) κ) k := by
  simp_rw [← dampedMobiusWeight_div]
  exact arithmeticFloorPrefix_centered_seed_identity (dampedMobiusWeight ε) κ p k

/-- The divisor sum of the genuine Möbius function, including the zero index. -/
theorem moebius_real_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have hi := (mobius_inversion
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun k => (if k = 0 then 0 else 1 : ℝ) -
      (if k - 1 = 0 then 0 else 1 : ℝ))).mpr
      (fun d hd => mobiusDifference_one d hd)
  have hh := hi n (Nat.pos_of_ne_zero hn0)
  simpa [hn0, hn1, show n - 1 ≠ 0 by omega] using hh

/-- At zero damping the actual arithmetic prefix is exactly the target step. -/
theorem dampedMobiusPrefix_at_zero (k : ℕ) :
    dampedMobiusPrefix 0 k = if k = 0 then 0 else 1 := by
  rw [dampedMobiusPrefix_eq_sum_divisors]
  simp only [neg_zero, Real.rpow_zero, mul_one, moebius_real_divisor_sum]
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : 1 < k + 1 := by omega
    simp [hk, hk1]

end
end RiemannResearch.RH.Pareto
