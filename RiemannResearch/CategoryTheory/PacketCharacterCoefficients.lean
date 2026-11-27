import RiemannResearch.CategoryTheory.ParetoPacketCharacters

/-! # Fourier coefficients of the CRT packets

We compute the principal and even coefficients on gcd fibres, restrict the
unit-profile Möbius formula to multiples of the character conductor, and
evaluate the primitive case of the CRT packet character decomposition.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannResearch.CategoryTheory.ParetoPacketCharacters
open RiemannResearch.RH.Pareto ValuationCharacterGram

/-- The coefficient of a constant is concentrated in the principal character. -/
theorem coefficient_constant {h : ℕ} [NeZero h] (c : ℂ) (χ : DirichletCharacter ℂ h) :
    unitCoefficient (fun _ => c) χ = if χ = 1 then c else 0 := by
  classical
  split_ifs with ht
  · subst χ
    have hφ : (h.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos h)).ne'
    simp only [unitCoefficient, ZMod.inv_coe_unit, MulChar.one_apply_coe, mul_one,
      Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
    field_simp
  · obtain ⟨a, ha⟩ : ∃ a : (ZMod h)ˣ, χ a ≠ 1 := by
      by_contra! htriv
      exact ht (MulChar.ext (fun a => by rw [htriv a, MulChar.one_apply_coe]))
    have he := coefficient_translate (fun _ => c) a χ
    have hz : (χ a - 1) * unitCoefficient (fun _ => c) χ = 0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

/-- For every even character this computes the coefficient itself, including
the principal character. The measure in this coefficient is uniform on the units. -/
theorem packet_even_coefficient {g h : ℕ} [NeZero h] (hg : 0 < g) (hh : 1 < h)
    (χ : DirichletCharacter ℂ h) (heven : χ (-1 : ZMod h) = 1) :
    unitCoefficient (profile g h) χ =
      if χ = 1 then (((g*h).totient : ℂ) - (ramanujanSum (g*h) g : ℂ))/2 else 0 := by
  classical
  let c : ℂ := ((g*h).totient : ℂ) - (ramanujanSum (g*h) g : ℂ)
  have hpair (v : (ZMod h)ˣ) : profile g h v + profile g h (-v) = c := by
    have hv := packet_odd_reconstruction g h hg hh v
    rw [odd_synthesis] at hv
    dsimp [c]
    linear_combination 2*hv
  have hsum : unitCoefficient (fun v => profile g h v + profile g h (-v)) χ =
      unitCoefficient (profile g h) χ + unitCoefficient (fun v => profile g h (-v)) χ := by
    simp only [unitCoefficient, add_div, add_mul, Finset.sum_add_distrib]
  have hneg := coefficient_translate (profile g h) (-1) χ
  simp only [neg_one_mul, Units.val_neg, Units.val_one, heven, one_mul] at hneg
  rw [show (fun v => profile g h v + profile g h (-v)) = (fun _ => c) from funext hpair,
    coefficient_constant, hneg] at hsum
  split_ifs at hsum ⊢ with ht
  · change _ = c / 2
    linear_combination -hsum / 2
  · linear_combination -hsum / 2

/-- Möbius inversion commutes with taking a uniform unit coefficient.
Each summand admits the lower-modulus conductor test. -/
theorem unit_packet_coefficient_divisors {h : ℕ} [NeZero h] (χ : DirichletCharacter ℂ h) :
    unitCoefficient (profile 1 h) χ =
      ∑ d ∈ h.divisors, (ArithmeticFunction.moebius (h/d) : ℂ) *
        unitCoefficient (fun v : (ZMod h)ˣ => (((v : ZMod h).val % d : ℕ) : ℂ)) χ := by
  classical
  unfold unitCoefficient profile ramanujanPacket residue
  simp only [one_mul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    Complex.ofReal_natCast, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- A residue column below the primitive conductor contributes zero. -/
theorem residue_coefficient_zero {h d : ℕ} [NeZero h] (hd : d ∈ h.divisors)
    (χ : DirichletCharacter ℂ h) (hn : ¬χ.conductor ∣ d) :
    unitCoefficient (fun v : (ZMod h)ˣ => (((v : ZMod h).val % d : ℕ) : ℂ)) χ = 0 := by
  let hdh := Nat.dvd_of_mem_divisors hd
  let _ : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
  have he := coefficient_zero_of_conductor_not_dvd hdh
    (fun w : (ZMod d)ˣ => ((w : ZMod d).val : ℂ)) χ hn
  have hfun (v : (ZMod h)ˣ) :
      (((ZMod.unitsMap hdh v : (ZMod d)ˣ) : ZMod d).val) = (v : ZMod h).val % d := by
    change (ZMod.cast (v : ZMod h) : ZMod d).val = _
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  simpa only [hfun] using he

/-- Explicit imprimitive coefficients only use divisors divisible by the
primitive conductor. All operations are finite and exact. -/
theorem unit_packet_coefficient_conductor_divisors {h : ℕ} [NeZero h]
    (χ : DirichletCharacter ℂ h) :
    unitCoefficient (profile 1 h) χ =
      ∑ d ∈ h.divisors.filter (χ.conductor ∣ ·), (ArithmeticFunction.moebius (h/d) : ℂ) *
        unitCoefficient (fun v : (ZMod h)ˣ => (((v : ZMod h).val % d : ℕ) : ℂ)) χ := by
  rw [unit_packet_coefficient_divisors]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hmiss
  have hn : ¬χ.conductor ∣ d := fun hy => hmiss (Finset.mem_filter.mpr ⟨hd, hy⟩)
  rw [residue_coefficient_zero hd χ hn, mul_zero]

/-- Only the full-modulus least-residue column survives for a primitive
character. In the notation of equation (2) this gives exactly A(χ). -/
theorem primitive_unit_packet_coefficient {h : ℕ} [NeZero h]
    (χ : DirichletCharacter ℂ h) (hχ : χ.IsPrimitive) :
    unitCoefficient (profile 1 h) χ =
      unitCoefficient (fun v : (ZMod h)ˣ => ((v : ZMod h).val : ℂ)) χ := by
  classical
  have hh := NeZero.pos h
  rw [unit_packet_coefficient_divisors, Finset.sum_eq_single h]
  · rw [Nat.div_self hh, ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
    congr 1
    funext v
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
  · intro d hd hne
    have hdh := Nat.dvd_of_mem_divisors hd
    have hnf : ¬χ.conductor ∣ d := by
      rw [show χ.conductor = h from hχ]
      exact fun hhd => hne (Nat.dvd_antisymm hdh hhd)
    rw [residue_coefficient_zero hd χ hnf, mul_zero]
  · exact fun habs => (habs (Nat.mem_divisors.mpr ⟨dvd_rfl, hh.ne'⟩)).elim

end RiemannResearch.CategoryTheory.ParetoPacketCharacters
