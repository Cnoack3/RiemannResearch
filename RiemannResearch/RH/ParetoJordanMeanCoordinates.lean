import RiemannResearch.RH.ParetoUniformJordanVariance
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Exact logarithmic normalization in signed divisor coordinates

Source: Christian Noack, September 11, 2026, reflection-pair total variance
discussion. This uses Mathlib's actual von Mangoldt function; no prime-power
contribution or signed coefficient is discarded.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Restricting the divisor incidence to a common period leaves the exact log. -/
theorem vonMangoldt_sum_divisorIncidence (Q L : ℕ) (hQ : 0 < Q)
    (hL : L ∣ Q) :
    (∑ d ∈ Q.divisors,
      ArithmeticFunction.vonMangoldt d * divisorIncidence L d) = Real.log L := by
  have hL0 : L ≠ 0 := by
    intro h
    subst L
    exact (ne_of_gt hQ) (by simpa using hL)
  have hset : Q.divisors.filter (fun d => d ∣ L) = L.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdQ, hQ0⟩, hdL⟩
      exact ⟨hdL, hL0⟩
    · rintro ⟨hdL, hLn⟩
      exact ⟨⟨dvd_trans hdL hL, ne_of_gt hQ⟩, hdL⟩
  calc
    _ = ∑ d ∈ Q.divisors.filter (fun d => d ∣ L),
        ArithmeticFunction.vonMangoldt d := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdl : d ∣ L <;> simp [divisorIncidence, hdl]
    _ = ∑ d ∈ L.divisors, ArithmeticFunction.vonMangoldt d := by rw [hset]
    _ = _ := ArithmeticFunction.vonMangoldt_sum

/-- A single legal generator has normalization log(a) in divisor coordinates. -/
theorem vonMangoldt_sum_seedDivisorIncidence (Q a m : ℕ) (hQ : 0 < Q)
    (ha : 0 < a) (hm : 0 < m) (ham : a * m ∣ Q) (hmQ : m ∣ Q) :
    (∑ d ∈ Q.divisors,
      ArithmeticFunction.vonMangoldt d * seedDivisorIncidence a m d) =
        Real.log a := by
  simp only [seedDivisorIncidence, mul_sub, Finset.sum_sub_distrib]
  rw [vonMangoldt_sum_divisorIncidence Q (a * m) hQ ham,
    vonMangoldt_sum_divisorIncidence Q m hQ hmQ, Nat.cast_mul,
    Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (m : ℝ) ≠ 0)]
  ring

/-- The complete signed mean constraint after exchanging the finite sums. -/
theorem legalPacketDivisorCoordinate_log_mean {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q)
    (hscale : ∀ i ∈ s, m i ∣ Q) :
    (∑ d ∈ Q.divisors,
      ArithmeticFunction.vonMangoldt d * legalPacketDivisorCoordinate s c a m d) =
        ∑ i ∈ s, c i * Real.log (a i) := by
  classical
  unfold legalPacketDivisorCoordinate
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = c i * (∑ d ∈ Q.divisors,
        ArithmeticFunction.vonMangoldt d * seedDivisorIncidence (a i) (m i) d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [vonMangoldt_sum_seedDivisorIncidence Q (a i) (m i) hQ
        (ha i hi) (hm i hi) (hperiod i hi) (hscale i hi)]

/-- A divisor coprime to the seed is unchanged by multiplying the scale. -/
theorem seedDivisorIncidence_eq_zero_of_coprime (a m d : ℕ)
    (hda : Nat.Coprime d a) : seedDivisorIncidence a m d = 0 := by
  have he : d ∣ a * m ↔ d ∣ m := hda.dvd_mul_left
  simp [seedDivisorIncidence, divisorIncidence, he]

/-- Thus only divisors sharing seed primes can carry a nonzero packet coordinate. -/
theorem legalPacketDivisorCoordinate_eq_zero_of_coprime {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a m : ι → ℕ) (d : ℕ)
    (hc : ∀ i ∈ s, Nat.Coprime d (a i)) :
    legalPacketDivisorCoordinate s c a m d = 0 := by
  classical
  unfold legalPacketDivisorCoordinate
  apply Finset.sum_eq_zero
  intro i hi
  rw [seedDivisorIncidence_eq_zero_of_coprime _ _ _ (hc i hi), mul_zero]

end
end RiemannResearch.RH.Pareto
