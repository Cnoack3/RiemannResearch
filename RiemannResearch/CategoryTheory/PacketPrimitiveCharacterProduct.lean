import Mathlib.NumberTheory.MulChar.Lemmas
import RiemannResearch.CategoryTheory.PacketCharacterMoments
import RiemannResearch.CategoryTheory.PacketCharacterCoefficients
import RiemannResearch.CategoryTheory.PacketGcdExpansion
import RiemannResearch.CategoryTheory.PrimitiveConductorMobius

/-! # The full primitive-conductor coefficient of a CRT residue packet

The primitive unit first moment, the squarefree cofactor product and the
removed-gcd product together give formula (2) of the supplied packet note.
The result applies to every nonprincipal primitive character.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.ParetoPacketCharacters
open RiemannResearch.RH.Pareto ValuationCharacterGram

/-- Uniform first moment of the character after induction to any multiple modulus. -/
private def inducedFirstMoment {f : ℕ} (θ : DirichletCharacter ℂ f) (d : ℕ) : ℂ :=
  if hd : 0 < d ∧ f ∣ d then
    letI : NeZero d := ⟨hd.1.ne'⟩
    unitCoefficient (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ))
      (DirichletCharacter.changeLevel hd.2 θ)
  else 0

private theorem inducedFirstMoment_eq {f d : ℕ} [NeZero d] (θ : DirichletCharacter ℂ f)
    (hd : f ∣ d) : inducedFirstMoment θ d =
      unitCoefficient (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ))
        (DirichletCharacter.changeLevel hd θ) := by
  have hpos : 0 < d ∧ f ∣ d := ⟨NeZero.pos d, hd⟩
  simp only [inducedFirstMoment, dif_pos hpos]

private theorem inducedFirstMoment_prime_step {f : ℕ} (θ : DirichletCharacter ℂ f)
    (hnt : θ ≠ 1) (p m : ℕ) (hp : p.Prime) (hm : 0 < m) (hfm : f ∣ m) :
    inducedFirstMoment θ (p*m) = if p ∣ m then inducedFirstMoment θ m
      else ((p : ℂ)*(1-θ⁻¹ (p : ZMod f))/(p-1)) * inducedFirstMoment θ m := by
  let _ : NeZero m := ⟨hm.ne'⟩
  let _ : NeZero (p*m) := ⟨(Nat.mul_pos hp.pos hm).ne'⟩
  let χ := DirichletCharacter.changeLevel hfm θ
  have hχ : χ ≠ 1 := fun he => hnt ((DirichletCharacter.changeLevel_eq_one_iff hfm).mp he)
  have he := least_residue_coefficient_prime_step χ hχ p hp
  have hmp : m ∣ p*m := dvd_mul_left m p
  rw [inducedFirstMoment_eq θ (hfm.trans hmp), inducedFirstMoment_eq θ hfm,
    DirichletCharacter.changeLevel_trans θ hfm hmp]
  by_cases hpdm : p ∣ m
  · simpa only [if_pos hpdm, one_mul, χ] using he
  · have hpc := hp.coprime_iff_not_dvd.mpr hpdm
    have hval := DirichletCharacter.changeLevel_eq_cast_of_dvd θ⁻¹ hfm (ZMod.unitOfCoprime p hpc)
    have hv : χ⁻¹ (p : ZMod m) = θ⁻¹ (p : ZMod f) := by
      simpa only [χ, map_inv, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hfm] using hval
    simpa only [if_neg hpdm, hv, χ] using he

/-- The second product in formula (2), on the units of the inflated character. -/
theorem primitive_unit_inflation_product (f k : ℕ) [NeZero f] [NeZero (f*k)]
    (hk : 0 < k) (θ : DirichletCharacter ℂ f) (hθ : θ.IsPrimitive) (hnt : θ ≠ 1) :
    unitCoefficient (profile 1 (f*k)) (DirichletCharacter.changeLevel (dvd_mul_right f k) θ) =
    if Squarefree k ∧ k.Coprime f then
      unitCoefficient (fun v : (ZMod f)ˣ => ((v : ZMod f).val : ℂ)) θ *
        ∏ p ∈ k.primeFactors, (1-(p : ℂ)*θ⁻¹ (p : ZMod f))/(p-1) else 0 := by
  classical
  let χ := DirichletCharacter.changeLevel (dvd_mul_right f k) θ
  have hcond : χ.conductor = f := (DirichletCharacter.conductor_changeLevel θ _).trans hθ
  have hA : inducedFirstMoment θ f =
      unitCoefficient (fun v : (ZMod f)ˣ => ((v : ZMod f).val : ℂ)) θ := by
    rw [inducedFirstMoment_eq θ (dvd_refl f), DirichletCharacter.changeLevel_self]
  have hcolumn (d : ℕ) (hd : d ∈ (f*k).divisors.filter (f ∣ ·)) :
      unitCoefficient (fun v : (ZMod (f*k))ˣ => (((v : ZMod (f*k)).val % d : ℕ) : ℂ)) χ =
      inducedFirstMoment θ d := by
    obtain ⟨hmember, hfd⟩ := Finset.mem_filter.mp hd
    let _ : NeZero d := ⟨(Nat.pos_of_mem_divisors hmember).ne'⟩
    let hdN := Nat.dvd_of_mem_divisors hmember
    have hre := coefficient_changeLevel_pullback hdN
      (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ)) (DirichletCharacter.changeLevel hfd θ)
    have hv (v : (ZMod (f*k))ˣ) :
        ((ZMod.unitsMap hdN v : (ZMod d)ˣ) : ZMod d).val = (v : ZMod (f*k)).val % d := by
      change (ZMod.cast (v : ZMod (f*k)) : ZMod d).val = _
      rw [ZMod.cast_eq_val, ZMod.val_natCast]
    rw [inducedFirstMoment_eq θ hfd]
    simpa only [hv, ← DirichletCharacter.changeLevel_trans, χ] using hre
  change unitCoefficient (profile 1 (f*k)) χ = _
  rw [unit_packet_coefficient_conductor_divisors χ, hcond]
  have hm := primitive_column_moebius_sum f k (NeZero.pos f) hk (fun p => θ⁻¹ (p : ZMod f))
    (inducedFirstMoment θ) (inducedFirstMoment θ f) (fun d hd =>
      normalized_prime_column_product f (NeZero.pos f) (fun p => θ⁻¹ (p : ZMod f))
        (inducedFirstMoment θ) (inducedFirstMoment_prime_step θ hnt) d (Nat.pos_of_mem_divisors hd))
  rw [← hA, ← hm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hcolumn d hd]

/-- Full gcd and primitive-conductor product for the coefficient of the
induced character, including the vanishing cases. -/
theorem packet_primitive_character_product (g f k : ℕ) [NeZero f] [NeZero (f*k)]
    (hk : 0 < k) (θ : DirichletCharacter ℂ f) (hθ : θ.IsPrimitive) (hnt : θ ≠ 1) :
    let χ := DirichletCharacter.changeLevel (dvd_mul_right f k) θ
    unitCoefficient (profile g (f*k)) χ =
      if Squarefree k ∧ k.Coprime f then
        (g : ℂ) * unitCoefficient (fun v : (ZMod f)ˣ => ((v : ZMod f).val : ℂ)) θ *
          (∏ p ∈ g.primeFactors.filter (fun p => ¬ p ∣ f*k), (1-χ (p : ZMod (f*k))/(p : ℂ))) *
          ∏ p ∈ k.primeFactors, (1 - (p : ℂ) * star (θ (p : ZMod f))) / (p - 1)
      else 0 := by
  classical
  dsimp only
  simp only [MulChar.star_apply']
  rw [packet_gcd_unitCoefficient_product, primitive_unit_inflation_product f k hk θ hθ hnt]
  split_ifs <;> ring

end RiemannResearch.CategoryTheory.ParetoPacketCharacters
