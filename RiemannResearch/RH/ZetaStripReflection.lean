import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Reflection of zeta zeros within the open critical strip

Source: the functional-equation lemma is moved verbatim from
`RH/NymanAutocorrelationNullity`, where it was proved from Mathlib's
`riemannZeta_one_sub`. It is independent of the Nyman completion and
autocorrelation constructions.
-/

namespace RiemannResearch.RH

theorem riemannZeta_one_sub_eq_zero_of_strip {s : ℂ}
    (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 := by
  have hneg (n : ℕ) : s ≠ -(n : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at h1
  rw [riemannZeta_one_sub hneg hs1, hz, mul_zero]

end RiemannResearch.RH
