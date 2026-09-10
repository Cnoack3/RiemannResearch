import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact dyadic interpolation from midpoint refinement

Source: user-provided DyadicSignedBoundaryAbelVerification20260910(1).md
and the retained DyadicBoundaryFourierResearchNote20260910.md, September 10, 2026.
The present proofs establish the stated bounded continuation targets.

A general interpolation theorem consumed by the actual RH boundary tents.
-/

namespace RiemannResearch
noncomputable section

/-- Pure dyadic midpoint refinement forces exact affine interpolation on
every dyadic subdivision of the interval `[q,q+1]`. -/
theorem dyadicSequence_exact_interpolation
    (f : ℕ → ℝ) (q : ℕ)
    (hdouble : ∀ n, q ≤ n → f (2*n) = f n)
    (hodd : ∀ n, q ≤ n → f (2*n+1) = (1/2 : ℝ) * (f n + f (n+1)))
    (h r : ℕ) (hr : r ≤ 2^h) :
    (2 : ℝ)^h * f (2^h*q+r) =
      ((2 : ℝ)^h - (r : ℝ)) * f q + (r : ℝ) * f (q+1) := by
  induction h generalizing r with
  | zero =>
    have hr01 : r = 0 ∨ r = 1 := by
      have : r ≤ 1 := by simpa using hr
      omega
    rcases hr01 with rfl | rfl <;> simp
  | succ h ih =>
    have hp : 0 < 2^h := pow_pos (by norm_num) h
    have hq : q ≤ 2^h*q := by nlinarith
    have hn : q ≤ 2^h*q+r/2 := by omega
    have hrbound : r ≤ 2*2^h := by
      simpa only [pow_succ, Nat.mul_comm] using hr
    have hrmod := Nat.mod_lt r (by norm_num : 0 < 2)
    have hrdecomp := Nat.mod_add_div r 2
    have hrhalf : r/2 ≤ 2^h := by omega
    by_cases he : r % 2 = 0
    · have hidx : 2^(h+1)*q+r = 2*(2^h*q+r/2) := by
        calc
          2^(h+1)*q+r = 2*(2^h*q)+r := by rw [pow_succ]; ring
          _ = 2*(2^h*q+r/2) := by omega
      have hrreal : (r : ℝ) = 2*(r/2 : ℕ) := by
        exact_mod_cast (show r = 2*(r/2) by omega)
      have hi := ih (r/2) hrhalf
      rw [hidx, hdouble _ hn, pow_succ, hrreal]
      nlinarith only [hi]
    · have hrodd : r % 2 = 1 := by omega
      have hrhalf1 : r/2+1 ≤ 2^h := by omega
      have hidx : 2^(h+1)*q+r = 2*(2^h*q+r/2)+1 := by
        calc
          2^(h+1)*q+r = 2*(2^h*q)+r := by rw [pow_succ]; ring
          _ = 2*(2^h*q+r/2)+1 := by omega
      have hrreal : (r : ℝ) = 2*(r/2 : ℕ)+1 := by
        exact_mod_cast (show r = 2*(r/2)+1 by omega)
      have hi0 := ih (r/2) hrhalf
      have hi1 := ih (r/2+1) hrhalf1
      simp only [Nat.cast_add, Nat.cast_one] at hi1
      rw [hidx, hodd _ hn, pow_succ, hrreal]
      have hshift : 2^h*q+(r/2+1) = 2^h*q+r/2+1 := by omega
      rw [hshift] at hi1
      nlinarith only [hi0, hi1]

end
end RiemannResearch
