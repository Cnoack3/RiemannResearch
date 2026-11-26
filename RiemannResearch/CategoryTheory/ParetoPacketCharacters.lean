import RiemannResearch.CategoryTheory.ValuationCharacterGram
import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.ParetoPacketGreenGram

/-! # Dirichlet characters on the gcd classes of a physical packet

The character calculation in the user's CRT packet note uses counting measure on each
unit group. The physical site reconstruction below is pointwise and independent of
the choice of Hilbert norm.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.CategoryTheory.ParetoPacketCharacters
open RiemannResearch.RH.Pareto ValuationCharacterGram

def profile (g h : ℕ) (u : (ZMod h)ˣ) : ℂ :=
  (ramanujanPacket (g*h) (g*(u : ZMod h).val) : ℝ)

private theorem packet_mod (q n : ℕ) : ramanujanPacket q (n % q) = ramanujanPacket q n := by
  unfold ramanujanPacket
  apply Finset.sum_congr rfl
  intro d hd
  simp only [residue, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mem_divisors hd)]

/-- Character sum on a gcd class. A zero modulus is assigned zero. -/
def fibreValue (g h k : ℕ) : ℂ := by
  classical
  exact if hh : h = 0 then 0 else
    letI : NeZero h := ⟨hh⟩
    ∑ χ : DirichletCharacter ℂ h, unitCoefficient (profile g h) χ * χ (k : ZMod h)

theorem fibreValue_eq (g h k : ℕ) (hh : h ≠ 0) (hk : k.Coprime h) :
    fibreValue g h k = (ramanujanPacket (g*h) (g*k) : ℂ) := by
  classical
  let _ : NeZero h := ⟨hh⟩
  let u := ZMod.unitOfCoprime k hk
  have hu : (u : ZMod h) = (k : ZMod h) := rfl
  unfold fibreValue
  rw [dif_neg hh, ← hu, unitFourier_reconstruct, profile, hu, ZMod.val_natCast,
    ← Nat.mul_mod_mul_left, packet_mod]

/-- A Fourier evaluation at every physical site, including nonunits of the conductor. -/
def characterPacket (q n : ℕ) : ℝ :=
  (fibreValue (n.gcd q) (q / n.gcd q) (n / n.gcd q)).re

theorem characterPacket_eq (q n : ℕ) (hq : 0 < q) :
    characterPacket q n = ramanujanPacket q n := by
  have hg : 0 < n.gcd q := Nat.gcd_pos_of_pos_right _ hq
  have hh := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right n q)) hg
  rw [characterPacket, fibreValue_eq _ _ _ hh.ne' (Nat.coprime_div_gcd_div_gcd hg),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right n q), Nat.mul_div_cancel' (Nat.gcd_dvd_left n q)]
  rfl

/-- Reflection about zero on the period, including the Ramanujan correction. -/
theorem packet_reflect (q k : ℕ) (hq : 1 < q) (hk : 0 < k) (hkq : k ≤ q) :
    ramanujanPacket q k + ramanujanPacket q (q-k) = (q.totient : ℝ) - ramanujanSum q k := by
  have h := packet_reflection_totient q q (k-1) hq (dvd_refl q) (by omega)
  rw [show q - 1 - (k-1) = q-k by omega] at h
  linarith only [h, ramanujanPacket_increment q k hq hk]

/-- The odd part of any unit profile, as a character sum. The scalar multiplier
is zero for every even character. -/
theorem odd_synthesis {h : ℕ} [NeZero h] (f : (ZMod h)ˣ → ℂ) (u : (ZMod h)ˣ) :
    (∑ χ : DirichletCharacter ℂ h,
      (unitCoefficient f χ * (1 - χ (-1 : ZMod h)) / 2) * χ u) =
      (f u - f (-u)) / 2 := by
  classical
  rw [← unitFourier_reconstruct f u, ← unitFourier_reconstruct f (-u),
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro χ _
  have hn : χ ((-u : (ZMod h)ˣ) : ZMod h) = χ (-1 : ZMod h) * χ u := by
    rw [← map_mul]
    simp
  rw [hn]
  ring

/-- All nontrivial gcd quotients carry only an explicit constant and odd modes. -/
theorem packet_odd_reconstruction (g h : ℕ) (hg : 0 < g) (hh : 1 < h)
    [NeZero h] (u : (ZMod h)ˣ) :
    profile g h u =
      (((g*h).totient : ℂ) - (ramanujanSum (g*h) g : ℂ))/2 +
      ∑ χ : DirichletCharacter ℂ h,
        (unitCoefficient (profile g h) χ * (1 - χ (-1 : ZMod h)) / 2) * χ u := by
  let _ : Nontrivial (ZMod h) := ZMod.nontrivial_iff.mpr hh.ne'
  let _ : NeZero (u : ZMod h) := ⟨u.ne_zero⟩
  have hv : 0 < (u : ZMod h).val := Nat.pos_of_ne_zero (by simp)
  have hvh := ZMod.val_lt (u : ZMod h)
  have hq : 1 < g*h := lt_of_lt_of_le hh (by nlinarith)
  have hpair := packet_reflect (g*h) (g*(u : ZMod h).val) hq (Nat.mul_pos hg hv)
    (Nat.mul_le_mul_left _ hvh.le)
  have hcg : (g*h).gcd (g*(u : ZMod h).val) = g := by
    rw [Nat.gcd_mul_left, (ZMod.val_coe_unit_coprime u).symm.gcd_eq_one, mul_one]
  have hck : ramanujanSum (g*h) (g*(u : ZMod h).val) = ramanujanSum (g*h) g := by
    rw [ramanujanSum_gcd_divisors _ _ (by omega), ramanujanSum_gcd_divisors _ g (by omega),
      hcg, Nat.gcd_eq_right (dvd_mul_right g h)]
  rw [hck, ← Nat.mul_sub] at hpair
  have hc : profile g h u + profile g h (-u) =
      ((g*h).totient : ℂ) - (ramanujanSum (g*h) g : ℂ) := by
    unfold profile
    rw [Units.val_neg, ZMod.val_neg_of_ne_zero]
    exact_mod_cast hpair
  rw [odd_synthesis, ← hc]
  ring

/-- Removing one prime from a divisor common to the conductor and site. -/
theorem packet_prime_gcd_step (p m n : ℕ) (hp : p.Prime) (hm : 1 < m) :
    ramanujanPacket (p*m) (p*n) =
      p * ramanujanPacket m n - if p ∣ m then 0 else ramanujanPacket m (p*n) := by
  rw [ramanujanPacket_mul_prime _ _ _ hp hm]
  simp [dilation, hp.pos]

/-- Translating the unit argument by a multiplies the Fourier coefficient by chi(a). -/
theorem coefficient_translate {h : ℕ} [NeZero h] (f : (ZMod h)ˣ → ℂ)
    (a : (ZMod h)ˣ) (χ : DirichletCharacter ℂ h) :
    unitCoefficient (fun v => f (a*v)) χ = χ a * unitCoefficient f χ := by
  classical
  unfold unitCoefficient
  rw [← Equiv.sum_comp (Equiv.mulLeft a) (fun v : (ZMod h)ˣ =>
    f v / (h.totient : ℂ) * χ ((v : ZMod h)⁻¹)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  change f (a*v) / _ * χ ((v : ZMod h)⁻¹) =
    χ a * (f (a*v) / _ * χ (((a*v : (ZMod h)ˣ) : ZMod h)⁻¹))
  have hx : (a : ZMod h) * (((a*v : (ZMod h)ˣ) : ZMod h)⁻¹) = (v : ZMod h)⁻¹ := by
    simp only [ZMod.inv_coe_unit, ← Units.val_mul]
    congr 1
    rw [mul_comm a v, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hx, map_mul]
  ring

/-- Each lower-modulus column in the Mobius transform has zero coefficient
when the primitive conductor does not divide its modulus. -/
theorem coefficient_zero_of_conductor_not_dvd {h d : ℕ} [NeZero h] (hd : d ∣ h)
    (f : (ZMod d)ˣ → ℂ) (χ : DirichletCharacter ℂ h) (hn : ¬χ.conductor ∣ d) :
    unitCoefficient (fun v => f (ZMod.unitsMap hd v)) χ = 0 := by
  classical
  let F := fun v : (ZMod h)ˣ => f (ZMod.unitsMap hd v)
  change unitCoefficient F χ = 0
  by_contra hnon
  apply hn
  apply χ.conductor_dvd_of_mem_conductorSet
  apply (χ.factorsThrough_iff_ker_unitsMap hd).mpr
  intro a ha
  have hae : ZMod.unitsMap hd a = 1 := MonoidHom.mem_ker.mp ha
  have hF : (fun v => F (a*v)) = F := by funext v; simp [F, hae]
  have hx := coefficient_translate F a χ
  rw [hF] at hx
  have hz : (χ a-1)*unitCoefficient F χ = 0 := by linear_combination -hx
  have hchar := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hnon)
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  simpa using hchar

/-- The parity-carry formula for every odd prime. Its last indicator has the
finite character expansion on units already given by unitFourier_reconstruct. -/
theorem twice_prime_parity (p n : ℕ) (hp : p.Prime) (hp' : 2 < p) :
    ramanujanPacket (2*p) n =
      ((p : ℝ)-1) * ((n%2 : ℕ) : ℝ) +
        (p : ℝ) * (1-2*((n%2 : ℕ) : ℝ)) * (((n%p)%2 : ℕ) : ℝ) := by
  have hodd : p%2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hnd : ¬ p ∣ 2 := fun h => (not_le_of_gt hp') (Nat.le_of_dvd (by decide) h)
  have hb : n%2 = ((n/p)%2 + (n%p)%2)%2 := by
    calc
      n%2 = (p*(n/p) + n%p)%2 := congrArg (· % 2) (Nat.div_add_mod n p).symm
      _ = _ := by rw [Nat.add_mod, Nat.mul_mod]; simp [hodd]
  rw [Nat.mul_comm 2 p, ramanujanPacket_mul_prime_of_not_dvd _ _ _ hp (by decide) hnd,
    ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
  simp only [dilation, residue]
  rcases Nat.mod_two_eq_zero_or_one (n/p) with hq | hq <;>
    rcases Nat.mod_two_eq_zero_or_one (n%p) with hr | hr <;>
    (simp [hq, hr] at hb; simp [hq, hr, hb] <;> ring)

/-- At six the varying real character distinguishes residues one and two modulo three. -/
theorem six_site_characters (n : ℕ) :
    ramanujanPacket 6 n = 2 * ((n%2 : ℕ) : ℝ) +
      (3/2 : ℝ) * (1-2*((n%2 : ℕ) : ℝ)) *
        ((if n%3 = 0 then 0 else 1) +
         (if n%3 = 1 then 1 else if n%3 = 2 then -1 else 0)) := by
  rw [show 6 = 2*3 by decide, twice_prime_parity _ _ (by decide) (by decide)]
  have hh := Nat.mod_lt n (show 0 < 3 by decide)
  interval_cases e : n%3 <;> norm_num [e]
  all_goals ring

/-- Real and imaginary parts of the quartic character normalized by beta(2)=i. -/
theorem ten_site_characters (n : ℕ) :
    ramanujanPacket 10 n = 4 * ((n%2 : ℕ) : ℝ) +
      (5/2 : ℝ) * (1-2*((n%2 : ℕ) : ℝ)) *
        ((if n%5 = 0 then 0 else 1) +
         (if n%5 = 1 then 1 else if n%5 = 4 then -1 else 0) -
         (if n%5 = 2 then 1 else if n%5 = 3 then -1 else 0)) := by
  rw [show 10 = 2*5 by decide, twice_prime_parity _ _ (by decide) (by decide)]
  have hh := Nat.mod_lt n (show 0 < 5 by decide)
  interval_cases e : n%5 <;> norm_num [e] <;> ring

end RiemannResearch.CategoryTheory.ParetoPacketCharacters
