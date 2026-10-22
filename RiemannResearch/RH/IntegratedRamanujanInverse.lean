import RiemannResearch.RH.IntegratedRamanujanBasis

/-!
# Explicit inverse from integrated Ramanujan packets to prime-seed dilations

Source: user-provided 19 September 2026 route, "Ramanujan, orthogonal sums,
CRT, von Mangoldt, change back." The finite inverse is proved by the prime
divisor transform and induction on the seed-prime valuation. It applies to
arbitrary other prime factors and includes all prime powers. The repository
dilation is unnormalized: dilation m f(k) = m * f(k / m).
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact finite seed coefficients after the inverse Ramanujan change of coordinates. -/
theorem ramanujanPacket_prime_pow_mul_inverse (p u v k : ℕ)
    (hp : p.Prime) (hu : 0 < u) (hpu : ¬ p ∣ u) :
    ramanujanPacket (p ^ (v + 1) * u) k =
      ∑ d ∈ u.divisors, (ArithmeticFunction.moebius (u / d) : ℝ) *
        dilation (p ^ v * d) (residue p) k := by
  induction v generalizing k with
  | zero =>
    simp only [Nat.zero_add, pow_one, pow_zero, one_mul]
    rw [ramanujanPacket, prime_divisor_transform p u hp hu, if_neg hpu,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [residue_mul_floor, Nat.mul_comm d p]
    ring
  | succ v ih =>
    have hdiv : p ∣ p ^ (v + 1) * u := by
      refine ⟨p ^ v * u, ?_⟩
      rw [pow_succ]
      ring
    have hpos : 0 < p ^ (v + 1) * u :=
      Nat.mul_pos (pow_pos hp.pos _) hu
    have hgt : 1 < p ^ (v + 1) * u :=
      lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdiv)
    have he : p * (p ^ (v + 1) * u) = p ^ (v + 1 + 1) * u := by
      simp only [pow_succ]
      ring
    rw [← he, ramanujanPacket_mul_prime_of_dvd p _ k hp hgt hdiv]
    change (p : ℝ) * ramanujanPacket (p ^ (v + 1) * u) (k / p) = _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hc : dilation p (dilation (p ^ v * d) (residue p)) k =
        dilation (p ^ (v + 1) * d) (residue p) k := by
      rw [dilation_comp]
      rw [show p * (p ^ v * d) = p ^ (v + 1) * d by
        rw [pow_succ]; ring]
    calc
      (p : ℝ) * ((ArithmeticFunction.moebius (u / d) : ℝ) *
          dilation (p ^ v * d) (residue p) (k / p)) =
          (ArithmeticFunction.moebius (u / d) : ℝ) *
            dilation p (dilation (p ^ v * d) (residue p)) k := by
        simp only [dilation]
        ring
      _ = _ := by rw [hc]

end
end RiemannResearch.RH.Pareto
