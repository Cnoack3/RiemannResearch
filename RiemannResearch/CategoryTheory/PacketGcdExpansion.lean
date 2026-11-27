import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-! # Möbius packets on gcd layers

This formalizes the gcd factor in §2 of the supplied CRT character decomposition:
each prime of the gcd absent from the reduced modulus supplies one difference
operator. The formula holds for every site, even before restricting to units.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto

noncomputable def packetGcdExpansion (s : Finset ℕ) (h u : ℕ) : ℝ :=
  ∑ t ∈ s.powerset, (∏ p ∈ t, -(p : ℝ)⁻¹) *
    ramanujanPacket h ((∏ p ∈ t, p) * u)

theorem packetGcdExpansion_insert {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) (h u : ℕ) :
    packetGcdExpansion (insert p s) h u =
      packetGcdExpansion s h u - (p : ℝ)⁻¹ * packetGcdExpansion s h (p*u) := by
  unfold packetGcdExpansion
  rw [Finset.sum_powerset_insert hp, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t := fun ht' => hp (Finset.mem_powerset.mp ht ht')
  rw [Finset.prod_insert hpt, Finset.prod_insert hpt, Nat.mul_right_comm p, Nat.mul_comm p u,
    Nat.mul_comm (∏ p ∈ t, p), Nat.mul_assoc]
  ring

/-- Prime dilation at multiples, including reduced conductor one. -/
theorem ramanujanPacket_prime_at_multiple (p m x : ℕ) (hp : p.Prime) (hm : 0 < m) :
    ramanujanPacket (p*m) (p*x) =
      (p : ℝ) * ramanujanPacket m x - if p ∣ m then 0 else ramanujanPacket m (p*x) := by
  by_cases h : m = 1
  · subst m
    have hz : ramanujanPacket p (p*x) = 0 := by
      unfold ramanujanPacket
      apply Finset.sum_eq_zero
      intro d hd
      have hdpx : d ∣ p*x := dvd_trans (Nat.dvd_of_mem_divisors hd) (dvd_mul_right p x)
      simp [residue, Nat.mod_eq_zero_of_dvd hdpx]
    rw [Nat.mul_one, hz]
    simp [ramanujanPacket, residue, Nat.mod_one, hp.ne_one]
  · rw [ramanujanPacket_mul_prime p m (p*x) hp (by omega)]
    simp [dilation, Nat.mul_div_cancel_left _ hp.pos]

/-- Full pointwise gcd removal, written as an inclusion–exclusion sum.
Only primes in the gcd that are absent from the reduced conductor survive. -/
theorem ramanujanPacket_gcd_expansion (g h u : ℕ) (hh : 0 < h) :
    ramanujanPacket (g*h) (g*u) = (g : ℝ) *
      packetGcdExpansion (g.primeFactors.filter (fun p => ¬ p ∣ h)) h u := by
  revert u
  induction g using induction_on_primes with
  | zero => simp [ramanujanPacket]
  | one => simp [packetGcdExpansion]
  | prime_mul p a hp ih =>
    intro u
    by_cases ha : a = 0
    · subst a
      simp [ramanujanPacket]
    have hfac : (p*a).primeFactors = insert p a.primeFactors := by
      rw [Nat.primeFactors_mul hp.ne_zero ha, hp.primeFactors, Finset.singleton_union]
    have hrec := ramanujanPacket_prime_at_multiple p (a*h) (a*u) hp
      (Nat.mul_pos (Nat.pos_of_ne_zero ha) hh)
    rw [Nat.mul_assoc, Nat.mul_assoc, hrec, ih u, hfac, Nat.cast_mul]
    by_cases hpah : p ∣ a*h
    · rw [if_pos hpah, sub_zero]
      have hset : (insert p a.primeFactors).filter (fun r => ¬ r ∣ h) =
          a.primeFactors.filter (fun r => ¬ r ∣ h) := by
        rcases hp.dvd_mul.mp hpah with hpa | hph
        · rw [Finset.insert_eq_of_mem (Nat.mem_primeFactors.mpr ⟨hp, hpa, ha⟩)]
        · ext r
          simp only [Finset.mem_filter, Finset.mem_insert]
          grind
      rw [hset, mul_assoc]
    · have hpa : ¬ p ∣ a := fun hd => hpah (dvd_mul_of_dvd_left hd h)
      have hph : ¬ p ∣ h := fun hd => hpah (dvd_mul_of_dvd_right hd a)
      have hnew : p ∉ a.primeFactors.filter (fun r => ¬ r ∣ h) :=
        fun hmem => hpa (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hmem).1)
      have hset : (insert p a.primeFactors).filter (fun r => ¬ r ∣ h) =
          insert p (a.primeFactors.filter (fun r => ¬ r ∣ h)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_insert]
        grind
      rw [if_neg hpah, Nat.mul_left_comm p a u, ih (p*u), hset,
        packetGcdExpansion_insert hnew]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp [hp0]

private theorem packetGcdExpansion_of_character_sum {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (χ : ι → ℕ →* ℂ) (h : ℕ)
    (hunit : ∀ v, v.Coprime h → (ramanujanPacket h v : ℂ) = ∑ i, c i * χ i v)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Coprime h) (u : ℕ) (hu : u.Coprime h) :
    (packetGcdExpansion s h u : ℂ) =
      ∑ i, c i * (∏ p ∈ s, (1 - χ i p / (p : ℂ))) * χ i u := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty => simpa [packetGcdExpansion] using hunit u hu
  | @insert p s hp ih =>
    have hs' : ∀ r ∈ s, r.Coprime h := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hpu := (hs p (Finset.mem_insert_self p s)).mul_left hu
    rw [packetGcdExpansion_insert hp, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast, ih hs' u hu, ih hs' (p*u) hpu,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.prod_insert hp, map_mul, div_eq_mul_inv]
    ring

/-- On the reduced units, the gcd correction is diagonal on every multiplicative
mode, with multiplier equal to the finite Euler product from formula (2). -/
theorem ramanujanPacket_gcd_character_product {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (χ : ι → ℕ →* ℂ) (g h u : ℕ) (hh : 0 < h) (hu : u.Coprime h)
    (hunit : ∀ v, v.Coprime h → (ramanujanPacket h v : ℂ) = ∑ i, c i * χ i v) :
    (ramanujanPacket (g*h) (g*u) : ℂ) =
      ∑ i, (g : ℂ) * c i *
        (∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ h), (1 - χ i p / (p : ℂ))) *
        χ i u := by
  let s := g.primeFactors.filter (fun p => ¬ p ∣ h)
  have hs : ∀ p ∈ s, p.Coprime h := by
    intro p hp
    obtain ⟨hpg, hph⟩ := Finset.mem_filter.mp hp
    exact (Nat.prime_of_mem_primeFactors hpg).coprime_iff_not_dvd.mpr hph
  rw [ramanujanPacket_gcd_expansion g h u hh, Complex.ofReal_mul, Complex.ofReal_natCast,
    packetGcdExpansion_of_character_sum c χ h hunit s hs u hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

open RiemannResearch.CategoryTheory.ParetoPacketCharacters
open RiemannResearch.CategoryTheory.ValuationCharacterGram

/-- Unconditional all-gcd Dirichlet synthesis from the *single* reduced-modulus
unit profile. The remaining factor in formula (2) is its primitive-conductor
unit coefficient. -/
theorem ramanujanPacket_gcd_dirichlet_product (g h u : ℕ) [NeZero h] (hu : u.Coprime h) :
    (ramanujanPacket (g*h) (g*u) : ℂ) =
      ∑ χ : DirichletCharacter ℂ h, (g : ℂ) * unitCoefficient (profile 1 h) χ *
        (∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ h), (1 - χ (p : ZMod h) / (p : ℂ))) *
        χ (u : ZMod h) := by
  classical
  let mode := fun χ : DirichletCharacter ℂ h =>
    χ.toMonoidHom.comp (Nat.castRingHom (ZMod h)).toMonoidHom
  apply ramanujanPacket_gcd_character_product (unitCoefficient (profile 1 h)) mode g h u
    (NeZero.pos h) hu
  intro v hv
  have hrec := fibreValue_eq 1 h v (NeZero.ne h) hv
  simpa [fibreValue, NeZero.ne h, mode] using hrec.symm

private theorem unitCoefficient_smul_profile {h : ℕ} [NeZero h] (a : ℂ)
    (F : (ZMod h)ˣ → ℂ) (χ : DirichletCharacter ℂ h) :
    unitCoefficient (fun v => a * F v) χ = a * unitCoefficient F χ := by
  unfold unitCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

open Classical in
private theorem unitCoefficient_of_character {h : ℕ} [NeZero h] (ψ χ : DirichletCharacter ℂ h) :
    unitCoefficient (fun v => ψ (v : ZMod h)) χ = if ψ = χ then 1 else 0 := by
  classical
  split_ifs with he
  · subst ψ
    have hc : (h.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos h)).ne'
    unfold unitCoefficient
    have hterm (v : (ZMod h)ˣ) :
        (χ (v : ZMod h) / h.totient) * χ ((v : ZMod h)⁻¹) = (h.totient : ℂ)⁻¹ := by
      rw [div_mul_eq_mul_div₀, ← map_mul, ZMod.inv_coe_unit, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one, one_div]
    simp only [hterm, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  · obtain ⟨a, ha⟩ : ∃ a : (ZMod h)ˣ, ψ a ≠ χ a := by
      by_contra! hsame
      exact he (MulChar.ext hsame)
    have trans := coefficient_translate (fun v => ψ (v : ZMod h)) a χ
    have e : (fun v : (ZMod h)ˣ => ψ ((a*v : (ZMod h)ˣ) : ZMod h)) =
        fun v : (ZMod h)ˣ => ψ a * ψ (v : ZMod h) := by funext v; rw [Units.val_mul, map_mul]
    rw [e, unitCoefficient_smul_profile] at trans
    exact (mul_eq_zero.mp (show (ψ a - χ a) * unitCoefficient (fun v => ψ (v : ZMod h)) χ = 0 by
      rw [sub_mul, trans, sub_self])).resolve_left (sub_ne_zero.mpr ha)

/-- The gcd-layer contribution in formula (2), as an identity on actual Fourier
coefficients. This factors out every prime removed from the reduced conductor. -/
theorem packet_gcd_unitCoefficient_product (g h : ℕ) [NeZero h] (ψ : DirichletCharacter ℂ h) :
    unitCoefficient (profile g h) ψ = (g : ℂ) * unitCoefficient (profile 1 h) ψ *
      ∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ h), (1 - ψ (p : ZMod h) / (p : ℂ)) := by
  classical
  let a := fun χ : DirichletCharacter ℂ h => (g : ℂ) * unitCoefficient (profile 1 h) χ *
    ∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ h), (1 - χ (p : ZMod h) / (p : ℂ))
  have hF (v : (ZMod h)ˣ) : profile g h v = ∑ χ : DirichletCharacter ℂ h, a χ * χ v := by
    simpa only [profile, a, ZMod.natCast_zmod_val] using
      ramanujanPacket_gcd_dirichlet_product g h (v : ZMod h).val (ZMod.val_coe_unit_coprime v)
  change unitCoefficient (profile g h) ψ = a ψ
  calc
    unitCoefficient (profile g h) ψ =
        ∑ χ : DirichletCharacter ℂ h, a χ * unitCoefficient (fun v => χ (v : ZMod h)) ψ := by
      unfold unitCoefficient
      simp_rw [hF, Finset.sum_div, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = a ψ := by simp [unitCoefficient_of_character, mul_ite]

end RiemannResearch.RH.Pareto
