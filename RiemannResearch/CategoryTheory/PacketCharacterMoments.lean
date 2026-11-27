import RiemannResearch.CategoryTheory.ParetoPacketCharacters

/-! # Character first moments at enlarged moduli

Uniform unit averages descend along modulus reduction. Weighted sums of
nonprincipal characters acquire the factor p(1 − χ(p)) on prime enlargement.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.ParetoPacketCharacters
open ValuationCharacterGram

private theorem uniform_sum_pullback {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (hπ : Function.Surjective π) (f : H → ℂ) :
    (Fintype.card H : ℂ) * (∑ x : G, f (π x)) =
      (Fintype.card G : ℂ) * ∑ y : H, f y := by
  classical
  have hi (y : H) : (∑ x : G, f (y * π x)) = ∑ x : G, f (π x) := by
    obtain ⟨a, rfl⟩ := hπ y
    simpa only [Equiv.coe_mulLeft, map_mul] using
      (Equiv.sum_comp (Equiv.mulLeft a) (fun x : G => f (π x)))
  have hj (x : G) : (∑ y : H, f (y * π x)) = ∑ y : H, f y := by
    exact Equiv.sum_comp (Equiv.mulRight (π x)) f
  calc
    _ = ∑ y : H, ∑ x : G, f (y * π x) := by simp only [hi, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x : G, ∑ y : H, f (y * π x) := Finset.sum_comm
    _ = _ := by simp only [hj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Uniform unit coefficients of a lifted profile and character agree exactly
with the coefficient at their common lower level. -/
theorem coefficient_changeLevel_pullback {h d : ℕ} [NeZero h] [NeZero d] (hd : d ∣ h)
    (f : (ZMod d)ˣ → ℂ) (χ : DirichletCharacter ℂ d) :
    unitCoefficient (fun v => f (ZMod.unitsMap hd v)) (DirichletCharacter.changeLevel hd χ) =
      unitCoefficient f χ := by
  classical
  let π := ZMod.unitsMap hd
  have hv (u : (ZMod h)ˣ) : (DirichletCharacter.changeLevel hd χ) ((u : ZMod h)⁻¹) =
      χ ((π u : ZMod d)⁻¹) := by
    rw [ZMod.inv_coe_unit, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    change χ (((π u⁻¹ : (ZMod d)ˣ) : ZMod d)) = _
    rw [map_inv, ZMod.inv_coe_unit]
  have he := uniform_sum_pullback π (ZMod.unitsMap_surjective hd)
      (fun u => f u * χ ((u : ZMod d)⁻¹))
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at he
  have hhφ : (h.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos h)).ne'
  have hdφ : (d.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos d)).ne'
  unfold unitCoefficient
  simp only [hv, div_mul_eq_mul_div₀, ← Finset.sum_div]
  apply (div_eq_div_iff hhφ hdφ).mpr
  simpa only [π, mul_comm] using he

/-- The lower-modulus column of the packet coefficient reduces to the
least-residue coefficient at that modulus when the character descends. -/
theorem residue_coefficient_changeLevel {h d : ℕ} [NeZero h] [NeZero d] (hd : d ∣ h)
    (χ : DirichletCharacter ℂ d) :
    unitCoefficient (fun v : (ZMod h)ˣ => (((v : ZMod h).val % d : ℕ) : ℂ))
        (DirichletCharacter.changeLevel hd χ) =
      unitCoefficient (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ)) χ := by
  have he := coefficient_changeLevel_pullback hd (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ)) χ
  have hfun (v : (ZMod h)ˣ) :
      (((ZMod.unitsMap hd v : (ZMod d)ˣ) : ZMod d).val) = (v : ZMod h).val % d := by
    change (ZMod.cast (v : ZMod h) : ZMod d).val = _
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  simpa only [hfun] using he

private theorem character_period_sum_zero {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hχ : χ ≠ 1) : (∑ k ∈ Finset.range d, χ (k : ZMod d)) = 0 := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d =>
    rw [← Fin.sum_univ_eq_sum_range]
    have hz := MulChar.sum_eq_zero_of_ne_one hχ
    change (∑ v : ZMod (d+1), χ ((v.val : ℕ) : ZMod (d+1))) = 0
    simpa only [ZMod.natCast_zmod_val] using hz

/-- Summing the least-residue first moment over complete periods multiplies
it by exactly the number of periods. The affine shift has zero contribution. -/
theorem character_firstMoment_fullPeriods {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (r : ℕ) :
    (∑ k ∈ Finset.range (r*d), (k : ℂ) * χ (k : ZMod d)) =
      (r : ℂ) * ∑ k ∈ Finset.range d, (k : ℂ) * χ (k : ZMod d) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
      add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, character_period_sum_zero χ hχ,
      Nat.cast_succ]
    ring

/-- Removing the multiples of p from p full periods of a nonprincipal
character gives the local factor 1 - χ(p), for any positive p. -/
theorem character_firstMoment_sieved {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (p : ℕ) (hp : 0 < p) :
    (∑ k ∈ (Finset.range (p*d)).filter (fun k => ¬p ∣ k), (k : ℂ) * χ (k : ZMod d)) =
      (p : ℂ) * (1 - χ (p : ZMod d)) * ∑ k ∈ Finset.range d, (k : ℂ) * χ (k : ZMod d) := by
  classical
  have hb : (∑ j ∈ Finset.range d, ((p*j : ℕ) : ℂ) * χ ((p*j : ℕ) : ZMod d)) =
      ∑ k ∈ (Finset.range (p*d)).filter (p ∣ ·), (k : ℂ) * χ (k : ZMod d) := by
    apply Finset.sum_bij (fun j _ => p*j)
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        ((Nat.mul_lt_mul_left hp).mpr (Finset.mem_range.mp hj)), dvd_mul_right _ _⟩
    · intro i _ j _ heq
      exact Nat.eq_of_mul_eq_mul_left hp heq
    · intro k hk
      obtain ⟨hlt, ⟨j, rfl⟩⟩ := Finset.mem_filter.mp hk
      exact ⟨j, Finset.mem_range.mpr ((Nat.mul_lt_mul_left hp).mp (Finset.mem_range.mp hlt)), rfl⟩
    · intro j _
      rfl
  have he := Finset.sum_filter_add_sum_filter_not (Finset.range (p*d)) (p ∣ ·)
    (fun k => (k : ℂ) * χ (k : ZMod d))
  rw [← hb, character_firstMoment_fullPeriods χ hχ p] at he
  have heq (j : ℕ) :
      ((p*j : ℕ) : ℂ) * χ ((p*j : ℕ) : ZMod d) =
        ((p : ℂ)*χ (p : ZMod d)) * ((j : ℂ)*χ (j : ZMod d)) := by
    simp only [Nat.cast_mul, map_mul]
    ring
  simp only [heq, ← Finset.mul_sum] at he
  linear_combination he

/-- Weighted residue sum of the induced character at a prime enlargement.
This includes primes already dividing d, where χ(p) vanishes. -/
theorem changeLevel_prime_firstMoment {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hχ : χ ≠ 1) (p : ℕ) (hp : p.Prime) :
    (∑ k ∈ Finset.range (p*d), (k : ℂ) *
      (DirichletCharacter.changeLevel (dvd_mul_left d p) χ) (k : ZMod (p*d))) =
      (p : ℂ) * (1 - χ (p : ZMod d)) * ∑ k ∈ Finset.range d, (k : ℂ) * χ (k : ZMod d) := by
  classical
  let hd : d ∣ p*d := dvd_mul_left d p
  have he (k : ℕ) : (DirichletCharacter.changeLevel hd χ) (k : ZMod (p*d)) =
      if p ∣ k then 0 else χ (k : ZMod d) := by
    by_cases hk : p ∣ k
    · rw [if_pos hk]
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
      exact fun h => hp.coprime_iff_not_dvd.mp h.1.symm hk
    · rw [if_neg hk]
      by_cases hc : k.Coprime d
      · have hall := Nat.coprime_mul_iff_right.mpr ⟨(hp.coprime_iff_not_dvd.mpr hk).symm, hc⟩
        have ht := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd (ZMod.unitOfCoprime k hall)
        simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] using ht
      · rw [MulChar.map_nonunit χ (fun hu => hc ((ZMod.isUnit_iff_coprime k d).mp hu))]
        apply MulChar.map_nonunit
        rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
        exact fun h => hc h.2
  rw [← character_firstMoment_sieved χ hχ p hp.pos, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [he k]
  by_cases hk : p ∣ k <;> simp [hk]

/-- The primitive base coefficient is the normalized first moment of the
inverse character on all least residues. The nonunit summands vanish. -/
theorem least_residue_coefficient_firstMoment {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    unitCoefficient (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ)) χ =
      (∑ k ∈ Finset.range d, (k : ℂ) * χ⁻¹ (k : ZMod d)) / d.totient := by
  classical
  let F (v : ZMod d) : ℂ := (v.val : ℂ) * χ⁻¹ v
  have hv (u : (ZMod d)ˣ) : χ ((u : ZMod d)⁻¹) = χ⁻¹ (u : ZMod d) := by
    rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hunit : (∑ u : (ZMod d)ˣ, F u) = ∑ v ∈ Finset.univ.filter IsUnit, F v := by
    apply Finset.sum_bij (fun (u : (ZMod d)ˣ) _ => (u : ZMod d))
    · intro u _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
    · intro u _ v _ h
      exact Units.ext h
    · intro v hv
      have hu := (Finset.mem_filter.mp hv).2
      exact ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
    · intro u _
      rfl
  have hall : (∑ v ∈ Finset.univ.filter IsUnit, F v) = ∑ v : ZMod d, F v := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hmiss
    have hn : ¬ IsUnit v := fun hu => hmiss (Finset.mem_filter.mpr ⟨hv, hu⟩)
    simp [F, MulChar.map_nonunit χ⁻¹ hn]
  have hr : (∑ v : ZMod d, F v) = ∑ k ∈ Finset.range d, (k : ℂ) * χ⁻¹ (k : ZMod d) := by
    cases d with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ d =>
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ v : ZMod (d+1), (v.val : ℂ) * χ⁻¹ v) =
        ∑ v : ZMod (d+1), (v.val : ℂ) * χ⁻¹ ((v.val : ℕ) : ZMod (d+1))
      simp only [ZMod.natCast_zmod_val]
  unfold unitCoefficient
  simp only [hv, div_mul_eq_mul_div₀, ← Finset.sum_div]
  exact congrArg (· / (d.totient : ℂ)) (hunit.trans (hall.trans hr))

/-- Passing from d to p*d gives the normalized local factor in the primitive
coefficient formula. A repeated prime leaves the least-residue coefficient fixed. -/
theorem least_residue_coefficient_prime_step {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) (p : ℕ) (hp : p.Prime) [NeZero (p*d)] :
    unitCoefficient (fun v : (ZMod (p*d))ˣ => ((v : ZMod (p*d)).val : ℂ))
        (DirichletCharacter.changeLevel (dvd_mul_left d p) χ) =
      (if p ∣ d then 1 else (p : ℂ) * (1 - χ⁻¹ (p : ZMod d)) / (p-1 : ℂ)) *
        unitCoefficient (fun v : (ZMod d)ˣ => ((v : ZMod d).val : ℂ)) χ := by
  classical
  have hi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hpd : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hφ : (d.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos d)).ne'
  rw [least_residue_coefficient_firstMoment, least_residue_coefficient_firstMoment, ← map_inv,
    changeLevel_prime_firstMoment χ⁻¹ hi p hp]
  split_ifs with hd
  · have hz : χ⁻¹ (p : ZMod d) = 0 :=
      MulChar.map_nonunit _ (fun hw => (hp.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p d).mp hw)) hd)
    rw [hz, Nat.totient_mul_of_prime_of_dvd hp hd, Nat.cast_mul]
    field_simp
    ring
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd, Nat.cast_mul, Nat.cast_sub hp.one_le,
      Nat.cast_one]
    have hpm : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
    field_simp

end RiemannResearch.CategoryTheory.ParetoPacketCharacters
