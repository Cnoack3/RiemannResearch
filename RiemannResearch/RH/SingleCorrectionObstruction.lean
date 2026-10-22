import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A finite lower bound for the one-divisor repair

A repair can be exact on the initial interval and still have large energy
immediately afterwards. The bound below uses only a counting-function upper
bound and elementary inequalities; it does not assume RH or a prime asymptotic.
-/

namespace RiemannResearch.RH.ArithmeticCumulative
noncomputable section
open scoped BigOperators

def singleRepair (R : ℕ → ℝ) (D : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  R n - β * (n / D : ℕ)

def windowError (F : ℕ → ℝ) (D L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (L + 1), weight (D + j) * (F (D + j) - 1) ^ 2

theorem singleRepair_head (R : ℕ → ℝ) (D n : ℕ) (β : ℝ)
    (hn : n < D) (hR : R n = 1) : singleRepair R D β n = 1 := by
  simp [singleRepair, Nat.div_eq_of_lt hn, hR]

theorem singleRepair_window_value (R : ℕ → ℝ) (D j : ℕ) (β : ℝ)
    (hD : 0 < D) (hj : j < D) :
    singleRepair R D β (D + j) = R (D + j) - β := by
  have hq : (D + j) / D = 1 := by
    rw [Nat.add_div hD]
    simp [Nat.div_self hD, Nat.mod_self,
      Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, not_le_of_gt hj]
  simp [singleRepair, hq]

theorem singleRepair_overshoot (R : ℕ → ℝ) (D j : ℕ) (β : ℝ)
    (hD : 0 < D) (hj : j < D) (hβ : 8 ≤ β)
    (hjβ : (j : ℝ) ≤ β / 4) (hR : R (D + j) ≤ (j : ℝ) + 2) :
    singleRepair R D β (D + j) ≤ -β / 2 := by
  rw [singleRepair_window_value R D j β hD hj]
  linarith

/-- A whole window contributes at least beta^3/(64 D^2) to the squared error. -/
theorem singleRepair_window_lower_bound
    (R : ℕ → ℝ) (D L : ℕ) (β : ℝ)
    (hD : 0 < D) (hβ : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (hL : (L : ℝ) ≤ β / 4) (hLlow : β / 4 ≤ ((L + 1 : ℕ) : ℝ))
    (hR : ∀ j ≤ L, R (D + j) ≤ (j : ℝ) + 2) :
    β ^ 3 / (64 * (D : ℝ) ^ 2) ≤ windowError (singleRepair R D β) D L := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (L + 1)) :
      β ^ 2 / (16 * (D : ℝ) ^ 2) ≤
        weight (D + j) * (singleRepair R D β (D + j) - 1) ^ 2 := by
    have hjL : j ≤ L := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have hjβ : (j : ℝ) ≤ β / 4 := le_trans (by exact_mod_cast hjL) hL
    have hjD : j < D := by
      have : (j : ℝ) < (D : ℝ) := by nlinarith
      exact_mod_cast this
    have hneg := singleRepair_overshoot R D j β hD hjD hβ hjβ (hR j hjL)
    have he : β ^ 2 / 4 ≤ (singleRepair R D β (D + j) - 1) ^ 2 := by
      nlinarith [mul_nonneg
        (show 0 ≤ 1 - singleRepair R D β (D + j) - β / 2 by linarith)
        (show 0 ≤ 1 - singleRepair R D β (D + j) + β / 2 by linarith)]
    have hx : (0 : ℝ) < ((D + j : ℕ) : ℝ) := by positivity
    have hxle : ((D + j : ℕ) : ℝ) + 1 ≤ 2 * (D : ℝ) := by
      exact_mod_cast (show D + j + 1 ≤ 2 * D by omega)
    have hden : ((D + j : ℕ) : ℝ) * (((D + j : ℕ) : ℝ) + 1) ≤
        4 * (D : ℝ) ^ 2 := by
      calc
        _ ≤ (2 * (D : ℝ)) * (2 * (D : ℝ)) :=
          mul_le_mul (by linarith) hxle (by positivity) (by positivity)
        _ = _ := by ring
    have hw : 1 / (4 * (D : ℝ) ^ 2) ≤ weight (D + j) := by
      exact one_div_le_one_div_of_le (by positivity) hden
    have hm := mul_le_mul hw he (by positivity : 0 ≤ β ^ 2 / 4)
      (weight_nonneg (D + j))
    calc
      _ = (1 / (4 * (D : ℝ) ^ 2)) * (β ^ 2 / 4) := by ring
      _ ≤ _ := hm
  have hs : ((L + 1 : ℕ) : ℝ) * (β ^ 2 / (16 * (D : ℝ) ^ 2)) ≤
      windowError (singleRepair R D β) D L := by
    simpa only [windowError, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum hterm)
  have hc := mul_le_mul_of_nonneg_right hLlow
    (show 0 ≤ β ^ 2 / (16 * (D : ℝ) ^ 2) by positivity)
  calc
    _ = (β / 4) * (β ^ 2 / (16 * (D : ℝ) ^ 2)) := by ring
    _ ≤ _ := le_trans hc hs

theorem cumulative_increment_upper_bound (a : ℕ → ℝ) (n k : ℕ)
    (ha : ∀ m, a m ≤ 1) :
    cumulative a (n + k) ≤ cumulative a n + (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, cumulative_succ]
    push_cast
    linarith [ha (n + k + 1)]

/-- Counting functions with an exact initial count satisfy the window hypothesis. -/
theorem counting_source_window_bound (a : ℕ → ℝ) (D j : ℕ)
    (hD : 0 < D) (ha : ∀ m, a m ≤ 1) (hhead : cumulative a (D - 1) = 1) :
    cumulative a (D + j) ≤ (j : ℝ) + 2 := by
  have h := cumulative_increment_upper_bound a (D - 1) (j + 1) ha
  have he : D - 1 + (j + 1) = D + j := by omega
  rw [he, hhead] at h
  push_cast at h
  linarith

/-- The counting-source obstruction with the canonical window length. -/
theorem singleRepair_counting_obstruction (a : ℕ → ℝ) (D : ℕ) (β : ℝ)
    (hD : 0 < D) (hβ : 8 ≤ β) (hβD : β ≤ (D : ℝ))
    (ha : ∀ m, a m ≤ 1) (hhead : cumulative a (D - 1) = 1) :
    β ^ 3 / (64 * (D : ℝ) ^ 2) ≤
      windowError (singleRepair (cumulative a) D β) D ⌊β / 4⌋₊ := by
  apply singleRepair_window_lower_bound (cumulative a) D ⌊β / 4⌋₊ β hD hβ hβD
  · exact Nat.floor_le (by linarith : 0 ≤ β / 4)
  · have h := Nat.lt_floor_add_one (β / 4)
    exact le_of_lt (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  · intro j hj
    exact counting_source_window_bound a D j hD ha hhead

end
end RiemannResearch.RH.ArithmeticCumulative
