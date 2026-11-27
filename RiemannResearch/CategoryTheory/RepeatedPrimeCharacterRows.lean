import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! # The repeated prime in the conductor-twelve character row

On the units modulo twelve, the physical packet has only its constant term and
the odd character modulo four. The unnormalized Fourier sum is evaluated for
every Dirichlet character modulo twelve. This verifies the repeated-prime
example in §3 of the CRT packet character note.
-/

namespace RiemannResearch.CategoryTheory.RepeatedPrimeCharacterRows

open RiemannResearch.RH.Pareto ParetoPacketCharacters ValuationCharacterGram
open scoped BigOperators
noncomputable section

/-- Exact integer-valued formula for the packet on the full period. -/
theorem twelve_site (n : ℕ) : ramanujanPacket 12 n =
    6 * (((n / 6) % 2 : ℕ) : ℝ) - 2 * (((n / 2) % 2 : ℕ) : ℝ) := by
  rw [show 12 = 2 * (3 * 2) by decide,
    ramanujanPacket_mul_prime_of_dvd 2 6 n (by decide) (by decide) (by decide)]
  simp only [dilation]
  rw [ramanujanPacket_mul_prime_of_not_dvd 3 2 (n / 2) (by decide) (by decide) (by decide),
    ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
  simp only [dilation, residue, Nat.div_div_eq_div_mul, Nat.cast_ofNat]
  ring

/-- The primitive character of conductor four gives the entire odd component on units. -/
theorem twelve_on_units (n : ℕ) (hn : n.Coprime 12) :
    ramanujanPacket 12 n = 2 - 2 * (ZMod.χ₄ (n : ZMod 4) : ℝ) := by
  have hu : (n % 12).Coprime 12 := by
    change (n%12).gcd 12 = 1
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact hn
  have htable : ∀ r : Fin 12, r.val.Coprime 12 →
      r.val = 1 ∨ r.val = 5 ∨ r.val = 7 ∨ r.val = 11 := by decide
  have hr : n%12 = 1 ∨ n%12 = 5 ∨ n%12 = 7 ∨ n%12 = 11 :=
    htable ⟨n%12, Nat.mod_lt _ (by decide)⟩ hu
  rw [twelve_site, ZMod.χ₄_nat_eq_if_mod_four,
    show n%2 = (n%12)%2 by omega, show n%4 = (n%12)%4 by omega,
    show (n/6)%2 = (n%12)/6 by omega, show (n/2)%2 = ((n%12)/2)%2 by omega]
  rcases hr with h | h | h | h <;> norm_num [h]

private def u12 (a : ℕ) (h : a.Coprime 12) := ZMod.unitOfCoprime a h

private theorem twelve_units : (Finset.univ : Finset (ZMod 12)ˣ) =
    {u12 1 (by decide), u12 5 (by decide), u12 7 (by decide), u12 11 (by decide)} := by
  decide

/-- The Fourier numerator on the four units, using inverse arguments as in the
project's unit Fourier normalization. Dividing by φ(12)=4 gives the coefficient. -/
theorem twelve_fourier_sum (χ : DirichletCharacter ℂ 12) :
    (∑ u : (ZMod 12)ˣ, (ramanujanPacket 12 (u : ZMod 12).val : ℂ) *
      χ ((u : ZMod 12)⁻¹)) = 4 * (1 + χ 5) * χ 7 := by
  have hs : ∀ u : (ZMod 12)ˣ, u*u = 1 := by decide
  have hi (u : (ZMod 12)ˣ) : (u : ZMod 12)⁻¹ = u := by
    rw [ZMod.inv_coe_unit, inv_eq_of_mul_eq_one_right (hs u)]
  simp_rw [hi]
  rw [twelve_units]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h11 : χ 11 = χ 5 * χ 7 := by rw [← map_mul] <;> congr 1
  norm_num [u12, twelve_site,
    show (1 : ZMod 12).val = 1 by rfl, show (5 : ZMod 12).val = 5 by rfl,
    show (7 : ZMod 12).val = 7 by rfl, show (11 : ZMod 12).val = 11 by rfl, h11] <;> ring

/-- The exact coefficient in the project's finite unit Fourier inversion. -/
theorem twelve_unitCoefficient (χ : DirichletCharacter ℂ 12) :
    unitCoefficient (profile 1 12) χ = (1 + χ 5) * χ 7 := by
  unfold unitCoefficient
  have ht : (12 : ℕ).totient = 4 := by decide
  simp only [profile, one_mul, ht, Nat.cast_ofNat, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [twelve_fourier_sum]
  ring

/-- In particular every character taking the sign −1 at 5 has zero coefficient,
including the inflation of the nontrivial character modulo three. -/
theorem twelve_unitCoefficient_zero (χ : DirichletCharacter ℂ 12) (hχ : χ 5 = -1) :
    unitCoefficient (profile 1 12) χ = 0 := by
  rw [twelve_unitCoefficient, hχ]
  ring

end
end RiemannResearch.CategoryTheory.RepeatedPrimeCharacterRows
