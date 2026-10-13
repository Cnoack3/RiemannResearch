import RiemannResearch.RH.QFloorEulerCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp

/-!
# The von Mangoldt coefficients of the local Q operator logarithm

On a prime power, `Λ(p^k) / log(p^k) = 1/k`. This rewrites the convergent
local Euler logarithm using the same prime-power arithmetic coefficients that
arise from the integrated Ramanujan/Pareto mean duality. The sign is negative
for the logarithm of `I-T_p`.
-/

noncomputable section

namespace RiemannResearch.RH.QFloorEulerVonMangoldt

open ZetaTwoHilbert QFloorDilation QFloorEulerOperators QFloorEulerCalculus

theorem vonMangoldt_div_log_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ArithmeticFunction.vonMangoldt (p ^ k) / Real.log ((p ^ k : ℕ) : ℝ) =
      1 / (k : ℝ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (ne_of_gt hk),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  field_simp [hlog, hk0]

/-- The actual Q Euler logarithm is a convergent von Mangoldt prime-power series. -/
theorem floorLog_vonMangoldt_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ =>
      -((ArithmeticFunction.vonMangoldt (p ^ (k + 1)) /
          Real.log ((p ^ (k + 1) : ℕ) : ℝ)) •
        floorDilation (p ^ (k + 1)) (pow_pos hp.pos (k + 1))))
      (floorLog p hp.one_lt) := by
  simp_rw [vonMangoldt_div_log_prime_pow hp (Nat.succ_pos _)]
  simpa only [floorDilation_pow] using floorLog_hasSum p hp.one_lt

theorem floorLog_eq_vonMangoldt_tsum (p : ℕ) (hp : p.Prime) :
    floorLog p hp.one_lt =
      ∑' k : ℕ,
        -((ArithmeticFunction.vonMangoldt (p ^ (k + 1)) /
            Real.log ((p ^ (k + 1) : ℕ) : ℝ)) •
          floorDilation (p ^ (k + 1)) (pow_pos hp.pos (k + 1))) :=
  (floorLog_vonMangoldt_hasSum p hp).tsum_eq.symm

end RiemannResearch.RH.QFloorEulerVonMangoldt
