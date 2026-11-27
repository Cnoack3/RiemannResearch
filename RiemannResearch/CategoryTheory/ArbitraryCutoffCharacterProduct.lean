import RiemannResearch.CategoryTheory.ValuationCharacterGram
import Mathlib.NumberTheory.Primorial

/-! # Euler product for a physical rough-cofactor character at every cutoff

Equation (5) in the user's CRT character note requires distinct levels in the
numerator and denominator when some character primes are still unrevealed.
The numerator inflates the character to the least common multiple of its
level and the cutoff modulus. The denominator excludes only the cutoff primes.
-/

noncomputable section
open scoped BigOperators LSeries.notation Topology
open Filter
namespace RiemannResearch.CategoryTheory.ValuationCharacterGram

/-- Inflation to the least common multiple inserts exactly the cutoff's
principal-character factor, even on nonunits of the original character level. -/
theorem inflation_eq_revealed_principal {q : ℕ} (R n : ℕ) (χ : DirichletCharacter ℂ q) :
    χ.changeLevel (Nat.dvd_lcm_right R q) n =
      (1 : DirichletCharacter ℂ R) n * χ n := by
  by_cases hR : n.Coprime R
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n R).2 hR), one_mul]
    by_cases hq : n.Coprime q
    · have h := (hR.mul_right hq).coprime_dvd_right (Nat.lcm_dvd_mul R q)
      have hz := χ.changeLevel_eq_cast_of_dvd (Nat.dvd_lcm_right R q) (ZMod.unitOfCoprime n h)
      simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_right R q)] using hz
    · have hL : ¬ IsUnit (n : ZMod (Nat.lcm R q)) :=
        fun hx => hq (((ZMod.isUnit_iff_coprime n _).1 hx).coprime_dvd_right
          (Nat.dvd_lcm_right R q))
      have hQ : ¬ IsUnit (n : ZMod q) := fun hx => hq ((ZMod.isUnit_iff_coprime n q).1 hx)
      rw [MulChar.map_nonunit _ hL, MulChar.map_nonunit _ hQ]
  · have hL : ¬ IsUnit (n : ZMod (Nat.lcm R q)) :=
      fun hx => hR (((ZMod.isUnit_iff_coprime n _).1 hx).coprime_dvd_right (Nat.dvd_lcm_left R q))
    have hR' : ¬ IsUnit (n : ZMod R) := fun hx => hR ((ZMod.isUnit_iff_coprime n R).1 hx)
    rw [MulChar.map_nonunit _ hL, MulChar.map_nonunit _ hR', zero_mul]

private theorem arbitraryLevel_sum_at_two {m : ℕ} (χ : DirichletCharacter ℂ m) :
    (∑' n : ℕ, χ n / (n : ℂ)^2) = LSeries ↗χ 2 := by
  have h : 1 < (2 : ℂ).re := by norm_num
  simpa [dirichletSummandHom, Complex.cpow_neg, div_eq_mul_inv] using
    (tsum_dirichletSummand χ h)

/-- All-cutoff rough ratio for a character of arbitrary modulus q. In
particular an unrevealed prime dividing q retains the factor 1 − p⁻². -/
theorem arbitraryLevel_roughRatio_hasProd {q R b : ℕ} (χ : DirichletCharacter ℂ q)
    (cover : ∀ p : ℕ, p.Prime → (p ∣ R ↔ p ≤ b)) :
    HasProd (fun p : Nat.Primes => if p.val ≤ b then (1 : ℂ) else
      (1 - 1/(p : ℂ)^2)/(1-χ p/(p : ℂ)^2))
      ((∑' n : ℕ, (1 : DirichletCharacter ℂ R) n * χ n / (n : ℂ)^2) / roughMass R) := by
  let ξ := χ.changeLevel (Nat.dvd_lcm_right R q)
  let ε : DirichletCharacter ℂ R := 1
  have h : 1 < (2 : ℂ).re := by norm_num
  have hn : LSeries ↗ε 2 ≠ 0 := by
    rw [← ε.LSeries_eulerProduct_exp_log h]
    exact Complex.exp_ne_zero _
  have he (p : Nat.Primes) : (1-ε p/(p : ℂ)^2)/(1-ξ p/(p : ℂ)^2) =
      if p.val ≤ b then (1 : ℂ) else (1-1/(p : ℂ)^2)/(1-χ p/(p : ℂ)^2) := by
    dsimp only [ξ, ε]
    rw [inflation_eq_revealed_principal]
    by_cases hb : p.val ≤ b
    · have hu : ¬ IsUnit (p.val : ZMod R) :=
        fun hu => (ZMod.isUnit_prime_iff_not_dvd p.property).1 hu ((cover _ p.property).2 hb)
      simp [hb, MulChar.map_nonunit _ hu]
    · have hu : IsUnit (p.val : ZMod R) :=
        (ZMod.isUnit_prime_iff_not_dvd p.property).2 (fun hd => hb ((cover _ p.property).1 hd))
      simp [hb, MulChar.one_apply hu]
  have hm : HasProd (fun p : Nat.Primes => (1-ε p/(p : ℂ)^2)/(1-ξ p/(p : ℂ)^2))
      (LSeries ↗ξ 2 / LSeries ↗ε 2) := by
    have ha := ξ.LSeries_eulerProduct_hasProd h
    have hb := ε.LSeries_eulerProduct_hasProd h
    change Tendsto _ atTop _ at ha hb ⊢
    apply (ha.div hb hn).congr' (Filter.Eventually.of_forall fun s => ?_)
    simp [Pi.div_apply, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      div_eq_mul_inv, Complex.cpow_neg, mul_comm]
  rw [← arbitraryLevel_sum_at_two ξ, ← arbitraryLevel_sum_at_two ε] at hm
  simp only [he] at hm
  simpa only [ξ, ε, inflation_eq_revealed_principal, roughMass] using hm

theorem primorial_roughRatio_tprod {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) :
    (∏' p : Nat.Primes, if p.val ≤ b then (1 : ℂ) else
      (1-1/(p : ℂ)^2)/(1-χ p/(p : ℂ)^2)) =
      (∑' n : ℕ, (1 : DirichletCharacter ℂ (primorial b)) n * χ n / (n : ℂ)^2) /
        roughMass (primorial b) :=
  (arbitraryLevel_roughRatio_hasProd χ (fun _ hp => hp.dvd_primorial_iff)).tprod_eq

open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoProbability

/-- The inverse-square Euler factor belonging to one valuation coordinate. -/
def primeCharacterFactor {q : ℕ} (χ : DirichletCharacter ℂ q) (p : Nat.Primes) : ℂ :=
  (1 - 1/(p : ℂ)^2)/(1 - χ p/(p : ℂ)^2)

/-- All unrevealed Euler factors, with zero-extended Dirichlet characters. -/
def tailCharacterProduct {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∏' p : Nat.Primes, if p.val ≤ b then 1 else primeCharacterFactor χ p

/-- The primes at or below the physical cutoff, as a finite set of primes. -/
def revealedPrimeSet (b : ℕ) : Finset Nat.Primes :=
  ((Set.finite_le_nat b).preimage (f := fun p : Nat.Primes => p.val)
    Subtype.val_injective.injOn).toFinset

@[simp] theorem mem_revealedPrimeSet (b : ℕ) (p : Nat.Primes) :
    p ∈ revealedPrimeSet b ↔ p.val ≤ b := by simp [revealedPrimeSet]

/-- Every tail moment is nonzero by the absolutely convergent Dirichlet
Euler product at two for the inflated numerator and principal denominator. -/
theorem tailCharacterProduct_ne_zero {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) :
    tailCharacterProduct b χ ≠ 0 := by
  let R := primorial b
  let ξ := χ.changeLevel (Nat.dvd_lcm_right R q)
  let ε : DirichletCharacter ℂ R := 1
  have hb : tailCharacterProduct b χ =
      (∑' n : ℕ, ξ n / (n : ℂ)^2) / (∑' n : ℕ, ε n / (n : ℂ)^2) := by
    rw [tailCharacterProduct]
    simpa only [primeCharacterFactor, R, ξ, ε, inflation_eq_revealed_principal, roughMass] using
      primorial_roughRatio_tprod b χ
  have hn {m : ℕ} (ψ : DirichletCharacter ℂ m) : LSeries ↗ψ 2 ≠ 0 := by
    rw [← ψ.LSeries_eulerProduct_exp_log (by norm_num : 1 < (2 : ℂ).re)]
    exact Complex.exp_ne_zero _
  rw [hb, arbitraryLevel_sum_at_two ξ, arbitraryLevel_sum_at_two ε]
  exact div_ne_zero (hn ξ) (hn ε)

theorem fullProduct_eq_head_mul_tail {q : ℕ} (b : ℕ) (χ : DirichletCharacter ℂ q) :
    tailCharacterProduct 0 χ =
      (∏ p ∈ revealedPrimeSet b, primeCharacterFactor χ p) * tailCharacterProduct b χ := by
  classical
  let F := primeCharacterFactor χ
  let head := fun p : Nat.Primes => if p.val ≤ b then F p else 1
  let tail := fun p : Nat.Primes => if p.val ≤ b then 1 else F p
  have hh : HasProd head (∏ p ∈ revealedPrimeSet b, F p) := by
    have h : HasProd head (∏ p ∈ revealedPrimeSet b, head p) :=
      hasProd_prod_of_ne_finset_one (s := revealedPrimeSet b) (f := head)
        (fun p hp => if_neg (fun h => hp ((mem_revealedPrimeSet _ _).2 h)))
    have he : (∏ p ∈ revealedPrimeSet b, head p) = ∏ p ∈ revealedPrimeSet b, F p :=
      Finset.prod_congr rfl (fun p hp => if_pos ((mem_revealedPrimeSet _ _).1 hp))
    rwa [he] at h
  have ht : HasProd tail (tailCharacterProduct b χ) := by
    have h := arbitraryLevel_roughRatio_hasProd χ (fun p hp => hp.dvd_primorial_iff (n := b))
    simpa only [tail, tailCharacterProduct, F, primeCharacterFactor, ← primorial_roughRatio_tprod] using h
  have hprod (p : Nat.Primes) : head p * tail p = F p := by
    by_cases h : p.val ≤ b <;> simp [head, tail, h]
  have hzero (p : Nat.Primes) : ¬ p.val ≤ 0 := by have := p.property.pos; omega
  simpa only [tailCharacterProduct, hzero, if_false, Pi.mul_apply, hprod, F] using (hh.mul ht).tprod_eq

/-- The full physical character moment under Q is the product over all primes. -/
theorem qCharacterMean_eq_fullProduct {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, (positiveQWeight n : ℂ) * χ n) = tailCharacterProduct 0 χ := by
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime n 1).2 (Nat.coprime_one_right n))
  have hmass : roughMass 1 = (zetaTwo : ℂ) := by
    rw [roughMass, zetaTwo_eq_nat_sum, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [hone]
    push_cast
    rfl
  have hterm (n : ℕ) : (positiveQWeight n : ℂ) * χ n =
      (χ n/(n : ℂ)^2)/(zetaTwo : ℂ) := by
    simp [positiveQWeight, div_eq_mul_inv, mul_comm, mul_assoc]
  have hone0 (n : ℕ) : (1 : DirichletCharacter ℂ (primorial 0)) n = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).2 (by simp))
  have hmass0 : roughMass (primorial 0) = (zetaTwo : ℂ) := by simpa using hmass
  rw [tailCharacterProduct]
  simp only [primeCharacterFactor, primorial_roughRatio_tprod, hmass0, hone0, one_mul,
    hterm, tsum_div_const]

end RiemannResearch.CategoryTheory.ValuationCharacterGram
