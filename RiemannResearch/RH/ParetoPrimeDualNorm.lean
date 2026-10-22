import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact Pareto norm of the prime defect functional

Source: `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §3.1.
The representer is an actual sequence supported at `1`, `p-1`, and `p`.
Its full Pareto norm is evaluated exactly. The bound retains the complete
weighted error and applies to every square-summable sequence, not just bounded
packet combinations.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Riesz representer of `f p - f (p-1) - f 1` for the genuine Pareto weights. -/
def primeDualRepresenter (p k : ℕ) : ℝ :=
  if k = 1 then -2 else
  if k = p - 1 then -((p : ℝ) - 1) * p else
  if k = p then (p : ℝ) * (p + 1) else 0

theorem primeDualRepresenter_at_one (p : ℕ) : primeDualRepresenter p 1 = -2 := by
  simp [primeDualRepresenter]

theorem primeDualRepresenter_at_pred (p : ℕ) (hp : 3 ≤ p) :
    primeDualRepresenter p (p - 1) = -((p : ℝ) - 1) * p := by
  have h : p - 1 ≠ 1 := by omega
  simp [primeDualRepresenter, h]

theorem primeDualRepresenter_at_self (p : ℕ) (hp : 3 ≤ p) :
    primeDualRepresenter p p = (p : ℝ) * (p + 1) := by
  have h1 : p ≠ 1 := by omega
  have h2 : p ≠ p - 1 := by omega
  simp [primeDualRepresenter, h1, h2]

/-- The full infinite pairing evaluates to the three-coordinate functional;
the other sequence need not be bounded because the representer has finite support. -/
theorem paretoInner_primeDualRepresenter (p : ℕ) (hp : 3 ≤ p) (f : ℕ → ℝ) :
    paretoInner f (primeDualRepresenter p) = f p - f (p - 1) - f 1 := by
  have hp1 : p ≠ 1 := by omega
  have hm1 : p - 1 ≠ 1 := by omega
  have hmp : p - 1 ≠ p := by omega
  have hple : 1 ≤ p := by omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hm0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpplus : (p : ℝ) + 1 ≠ 0 := by linarith
  unfold paretoInner
  rw [tsum_eq_sum (s := ({1, p - 1, p} : Finset ℕ)) (by
    intro k hk
    have h1 : k ≠ 1 := by intro h; apply hk; simp [h]
    have hm : k ≠ p - 1 := by intro h; apply hk; simp [h]
    have hp' : k ≠ p := by intro h; apply hk; simp [h]
    simp [primeDualRepresenter, h1, hm, hp'])]
  rw [Finset.sum_insert (by simp [hm1, hp1, Ne.symm hm1, Ne.symm hp1]),
    Finset.sum_insert (by simp [hmp]), Finset.sum_singleton,
    primeDualRepresenter_at_one, primeDualRepresenter_at_pred p hp,
    primeDualRepresenter_at_self p hp]
  simp only [positiveWeight, Nat.cast_one, Nat.cast_sub hple, sub_add_cancel]
  field_simp [hp0, hm0, hpplus]
  <;> ring

/-- Exact squared dual norm; primality is unnecessary for this calculation. -/
theorem primeDualRepresenter_norm_sq (p : ℕ) (hp : 3 ≤ p) :
    paretoInner (primeDualRepresenter p) (primeDualRepresenter p) =
      2 * ((p : ℝ)^2 + 1) := by
  rw [paretoInner_primeDualRepresenter p hp,
    primeDualRepresenter_at_one, primeDualRepresenter_at_pred p hp,
    primeDualRepresenter_at_self p hp]
  ring

/-- Exact weighted Lagrange identity underlying the three-coordinate bound. -/
theorem prime_dual_lagrange_identity (p x y z : ℝ) (hp : 1 < p) :
    2 * (p^2 + 1) * (x^2 / 2 + y^2 / ((p-1)*p) + z^2 / (p*(p+1))) -
      (z-y-x)^2 =
      (((p-1)*p*x - 2*y)^2 / (2*(p-1)*p)) +
      ((p*(p+1)*x + 2*z)^2 / (2*p*(p+1))) +
      ((p*(p+1)*y + (p-1)*p*z)^2 / ((p-1)*p*(p*(p+1)))) := by
  have hp0 : p ≠ 0 := by linarith
  have hm0 : p - 1 ≠ 0 := by linarith
  have hplus : p + 1 ≠ 0 := by linarith
  field_simp
  <;> ring

theorem prime_dual_three_coordinate_sq_bound (p x y z : ℝ) (hp : 1 < p) :
    (z-y-x)^2 ≤
      2 * (p^2 + 1) * (x^2 / 2 + y^2 / ((p-1)*p) + z^2 / (p*(p+1))) := by
  have h := prime_dual_lagrange_identity p x y z hp
  have hp0 : 0 < p := by linarith
  have hm0 : 0 < p - 1 := by linarith
  have hplus : 0 < p + 1 := by linarith
  have hnonneg : 0 ≤
      (((p-1)*p*x - 2*y)^2 / (2*(p-1)*p)) +
      ((p*(p+1)*x + 2*z)^2 / (2*p*(p+1))) +
      ((p*(p+1)*y + (p-1)*p*z)^2 / ((p-1)*p*(p*(p+1)))) := by positivity
  linarith

/-- The exact dual constant bounds the complete, untruncated Pareto square sum. -/
theorem prime_dual_full_sq_bound (p : ℕ) (hp : 3 ≤ p) (f : ℕ → ℝ)
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) :
    (f p - f (p-1) - f 1)^2 ≤
      2 * ((p : ℝ)^2 + 1) * paretoInner f f := by
  have hp1 : p ≠ 1 := by omega
  have hm1 : p - 1 ≠ 1 := by omega
  have hmp : p - 1 ≠ p := by omega
  have hple : 1 ≤ p := by omega
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hfinite := hf.sum_le_tsum ({1,p-1,p} : Finset ℕ)
    (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg (f k)))
  rw [Finset.sum_insert (by simp [hm1, hp1, Ne.symm hm1, Ne.symm hp1]),
    Finset.sum_insert (by simp [hmp]), Finset.sum_singleton] at hfinite
  have hw1 : positiveWeight 1 = (1 : ℝ) / 2 := by norm_num [positiveWeight]
  have hwm : positiveWeight (p-1) = 1 / (((p : ℝ)-1)*p) := by
    simp only [positiveWeight, Nat.cast_sub hple, Nat.cast_one, sub_add_cancel]
  have hwp : positiveWeight p = 1 / ((p : ℝ)*(p+1)) := rfl
  have henergy : (f 1)^2 / 2 + (f (p-1))^2 / (((p : ℝ)-1)*p) +
      (f p)^2 / ((p : ℝ)*(p+1)) ≤ paretoInner f f := by
    calc
      _ = positiveWeight 1 * (f 1)^2 +
          (positiveWeight (p-1) * (f (p-1))^2 + positiveWeight p * (f p)^2) := by
        rw [hw1, hwm, hwp]
        ring
      _ ≤ ∑' k, positiveWeight k * (f k)^2 := hfinite
      _ = paretoInner f f := by simp only [paretoInner, pow_two]
  exact (prime_dual_three_coordinate_sq_bound (p : ℝ) (f 1) (f (p-1)) (f p)
    hpR).trans (mul_le_mul_of_nonneg_left henergy (by positivity))

theorem prime_dual_full_abs_bound (p : ℕ) (hp : 3 ≤ p) (f : ℕ → ℝ)
    (hf : Summable (fun k => positiveWeight k * (f k)^2)) :
    |f p - f (p-1) - f 1| ≤
      Real.sqrt (2 * ((p : ℝ)^2 + 1)) * Real.sqrt (paretoInner f f) := by
  have h := Real.sqrt_le_sqrt (prime_dual_full_sq_bound p hp f hf)
  simpa only [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (show 0 ≤ 2 * ((p : ℝ)^2 + 1) by positivity)] using h

/-- The genuine Möbius difference agrees with the representer for prime p,
once the zero coordinate is anchored. -/
theorem mobiusDifference_prime (p : ℕ) (hp : p.Prime) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) :
    mobiusDifference p f = f p - f (p-1) - f 1 := by
  unfold mobiusDifference
  rw [hp.divisors]
  norm_num [Nat.div_self hp.pos, hp.ne_one, Ne.symm hp.ne_one, hp.ne_zero, hf0,
    ArithmeticFunction.moebius_apply_prime hp] <;> ring

theorem mobiusDifference_prime_full_error_bound (p : ℕ) (hp : p.Prime)
    (hp3 : 3 ≤ p) (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun k => positiveWeight k * (1-f k)^2)) :
    |mobiusDifference p f + 1| ≤
      Real.sqrt (2 * ((p : ℝ)^2 + 1)) * Real.sqrt (paretoError f) := by
  have h := prime_dual_full_abs_bound p hp3 (fun k => 1-f k) hf
  rw [mobiusDifference_prime p hp f hf0]
  have heq : (1-f p) - (1-f (p-1)) - (1-f 1) =
      -(f p - f (p-1) - f 1 + 1) := by ring
  rw [heq, abs_neg] at h
  exact h

/-- The coefficient of residue p after expanding an actual finite packet sum. -/
def packetResidueCoefficient (p : ℕ) (Q : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, if p ∣ q then a q * (ArithmeticFunction.moebius (q/p) : ℝ) else 0

theorem packetCombination_prime_defect (p : ℕ) (hp : 1 < p)
    (Q : Finset ℕ) (a : ℕ → ℝ) (hQ : ∀ q ∈ Q, 0 < q) :
    mobiusDifference p (fun k => ∑ q ∈ Q, a q * ramanujanPacket q k) =
      -(p : ℝ) * packetResidueCoefficient p Q a := by
  rw [mobiusDifference_sum]
  unfold packetResidueCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [mobiusDifference_packet p q hp (hQ q hq)]
  split_ifs <;> ring

/-- The report's explicit coefficient estimate for every actual finite packet
combination. All full-tail summability is discharged. -/
theorem packetResidueCoefficient_prime_error_bound (p : ℕ) (hp : p.Prime)
    (hp3 : 3 ≤ p) (Q : Finset ℕ) (a : ℕ → ℝ) (hQ : ∀ q ∈ Q, 0 < q) :
    |(p : ℝ) * packetResidueCoefficient p Q a - 1| ≤
      Real.sqrt (2 * ((p : ℝ)^2 + 1)) *
        Real.sqrt (paretoError (fun k => ∑ q ∈ Q, a q * ramanujanPacket q k)) := by
  have hf0 : (∑ q ∈ Q, a q * ramanujanPacket q 0) = 0 := by
    simp [ramanujanPacket, residue]
  have h := mobiusDifference_prime_full_error_bound p hp hp3
    (fun k => ∑ q ∈ Q, a q * ramanujanPacket q k) hf0
    (packetCombination_error_summable Q a)
  rw [packetCombination_prime_defect p hp.one_lt Q a hQ] at h
  have heq : -(p : ℝ) * packetResidueCoefficient p Q a + 1 =
      -((p : ℝ) * packetResidueCoefficient p Q a - 1) := by ring
  simpa only [heq, abs_neg] using h

end
end RiemannResearch.RH.Pareto
