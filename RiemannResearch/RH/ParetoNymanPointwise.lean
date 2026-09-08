import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Pointwise Pareto–Nyman identity
Source: user-provided argument, RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md,
Section 5. These equalities precede the probability-space norm identification.
-/

namespace RiemannResearch.RH.Pareto

theorem fract_div_sub_fract_div_eq_floor_mod
    (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n) :
    Int.fract (x / (n : ℝ)) - Int.fract x / (n : ℝ) =
      ((⌊x⌋₊ % n : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hklo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hkhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hdecomp : (n : ℝ) * ((⌊x⌋₊ / n : ℕ) : ℝ) +
      ((⌊x⌋₊ % n : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) := by
    exact_mod_cast (Nat.div_add_mod ⌊x⌋₊ n)
  have hrlo : (0 : ℝ) ≤ ((⌊x⌋₊ % n : ℕ) : ℝ) := by positivity
  have hrhi : ((⌊x⌋₊ % n : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mod_lt ⌊x⌋₊ hn))
  have hfloor : ⌊x⌋ = (⌊x⌋₊ : ℤ) := by
    apply Int.floor_eq_iff.mpr
    change (⌊x⌋₊ : ℝ) ≤ x ∧ x < (⌊x⌋₊ : ℝ) + 1
    exact ⟨hklo, hkhi⟩
  have hfloor_div : ⌊x / (n : ℝ)⌋ = ((⌊x⌋₊ / n : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    change ((⌊x⌋₊ / n : ℕ) : ℝ) ≤ x / (n : ℝ) ∧
      x / (n : ℝ) < ((⌊x⌋₊ / n : ℕ) : ℝ) + 1
    constructor
    · apply (le_div_iff₀ hnR).mpr
      nlinarith
    · apply (div_lt_iff₀ hnR).mpr
      nlinarith
  simp only [Int.fract, hfloor, hfloor_div, Int.cast_natCast]
  field_simp [ne_of_gt hnR]
  nlinarith

theorem pareto_nyman_pointwise
    (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : 0 < n) :
    Int.fract (1 / ((n : ℝ) * u)) -
        (1 / (n : ℝ)) * Int.fract (1 / u) =
      ((⌊1 / u⌋₊ % n : ℕ) : ℝ) / (n : ℝ) := by
  have h := fract_div_sub_fract_div_eq_floor_mod
    (1 / u) (by positivity) n hn
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end RiemannResearch.RH.Pareto
