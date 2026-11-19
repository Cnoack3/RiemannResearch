import RiemannResearch.RH.CRTCarryRamanujanCoordinates
import RiemannResearch.RH.UniversalAtomCarryPresentation
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.RamanujanFiniteIdentities
import RiemannResearch.RH.ExactHeadRamanujanPlancherel
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.ExactHeadGreenProfile
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Certified carries in finite conductor coordinates

The common period can be any positive multiple of the inputs and output.
Source: the user-provided atom/carry CRT agenda, §14.6. The primitive and
integrated coordinates use S. Ramanujan, *On certain trigonometrical sums*,
sections 2 and 16 (1918), https://ramanujan.sirinudi.org/Volumes/published/ram21.html.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.FiniteCarryRamanujanDictionary
open ArithmeticCumulative Pareto UniversalAtomCarry
open ExactHeadGcdAtoms ExactHeadGreenProfile ExactHeadRamanujanPlancherel
open RiemannResearch.Analysis.FiniteProfileEnergy

variable {ι : Type*} [Fintype ι]

def commonPacketCoefficient (p : ι → ℕ) (a : ι → ℤ) (d q : ℕ) : ℝ :=
  (∑ i, if q ∣ p i then (a i : ℝ) / (p i : ℝ) else 0) -
    (if q ∣ d then 1 / (d : ℝ) else 0)

theorem commonPacketCoefficient_of_dvd (p : ι → ℕ) (a : ι → ℤ) {d q : ℕ}
    (hq : q ∣ d) :
    commonPacketCoefficient p a d q = CRTCarryRamanujan.packetCoefficient p a d q := by
  simp [commonPacketCoefficient, CRTCarryRamanujan.packetCoefficient, hq]

/-- A weighted normalized atom in the packet coordinates of any common period. -/
theorem multiple_atom_expansion (L d n : ℕ) (hL : 0 < L) (hd : 0 < d)
    (hdL : d ∣ L) (v : ℝ) :
    v * residueFraction d n =
      ∑ q ∈ L.divisors, (if q ∣ d then v / d else 0) * ramanujanPacket q n := by
  have hf : L.divisors.filter (fun q => q ∣ d) = d.divisors := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨h, hd.ne'⟩
    · rintro ⟨h, _⟩
      exact ⟨⟨dvd_trans h hdL, hL.ne'⟩, h⟩
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, hf, ← Finset.mul_sum, ramanujanPacket_divisor_sum d n hd]
  unfold residueFraction Pareto.residue
  ring

/-- The output contributes only to its own divisors, including for certificates
whose input conductors do not divide the output. -/
theorem carry_common_packet_expansion (L d : ℕ) (hL : 0 < L) (hd : 0 < d)
    (hdL : d ∣ L) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpL : ∀ i, p i ∣ L)
    (a : ι → ℤ) (k : ℤ) (hrec : (∑ i, (a i : ℝ) / (p i : ℝ)) = 1 / d + k)
    (n : ℕ) :
    (QPrimeCRTCarries.carry p a n : ℝ) =
      ∑ q ∈ L.divisors, commonPacketCoefficient p a d q * ramanujanPacket q n := by
  have h := QPrimeCRTCarries.residue_eq_sum_sub_carry_of_reciprocal d hd p hp a k hrec n
  have ho := multiple_atom_expansion L d n hL hd hdL 1
  rw [one_mul] at ho
  rw [show (QPrimeCRTCarries.carry p a n : ℝ) =
      (∑ i, (a i : ℝ) * residueFraction (p i) n) - residueFraction d n by linarith, ho]
  simp_rw [multiple_atom_expansion L (p _) n hL (hp _) (hpL _) (a _ : ℝ)]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [commonPacketCoefficient, sub_mul, Finset.sum_mul]

theorem certificate_packet_expansion (c : Certificate) (L : ℕ) (hL : 0 < L)
    (hdL : c.output ∣ L) (hpL : ∀ i, c.input i ∣ L) (n : ℕ) :
    c.carry n = ∑ q ∈ L.divisors,
      commonPacketCoefficient c.input c.coeff c.output q * ramanujanPacket q n :=
  carry_common_packet_expansion L c.output hL (Nat.zero_lt_of_lt c.output_gt_one)
    hdL c.input (fun i => Nat.zero_lt_of_lt (c.input_gt_one i)) hpL
    c.coeff c.charge c.reciprocal n

/-- The displayed coefficient of the invisible constant packet records the charge. -/
theorem certificate_packet_coefficient_one (c : Certificate) :
    commonPacketCoefficient c.input c.coeff c.output 1 = c.charge := by
  simp only [commonPacketCoefficient, one_dvd, if_true, c.reciprocal]
  ring

private theorem packet_one (n : ℕ) : ramanujanPacket 1 n = 0 := by
  simp [ramanujanPacket, Pareto.residue, Nat.mod_one]

/-- Uniqueness on all nontrivial divisors, allowing arbitrary coefficients at one. -/
theorem packet_coefficients_unique (L : ℕ) (hL : 0 < L) (u v : ℕ → ℝ)
    (huv : ∀ n, (∑ q ∈ L.divisors, u q * ramanujanPacket q n) =
      ∑ q ∈ L.divisors, v q * ramanujanPacket q n)
    (q : ℕ) (hq : q ∈ L.divisors) (hq1 : 1 < q) : u q = v q := by
  have hzero (n : ℕ) : ∑ t ∈ L.divisors.erase 1, (u t - v t) * ramanujanPacket t n = 0 := by
    have he := Finset.sum_erase_add L.divisors (fun t => (u t - v t) * ramanujanPacket t n)
      (Nat.one_mem_divisors.mpr hL.ne')
    rw [packet_one, mul_zero, add_zero] at he
    rw [he]
    simp only [sub_mul, Finset.sum_sub_distrib, huv n, sub_self]
  have hgt (t : ℕ) (ht : t ∈ L.divisors.erase 1) : 1 < t := by
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp ht
    have := Nat.pos_of_mem_divisors hm
    omega
  exact sub_eq_zero.mp (ramanujanPacket_finite_independent (L.divisors.erase 1)
    (fun t => u t - v t) hgt hzero q (Finset.mem_erase.mpr ⟨by omega, hq⟩))

/-- Equality on the single finite period already detects every nontrivial coefficient. -/
theorem packet_coefficients_unique_on_period (L : ℕ) (hL : 0 < L) (u v : ℕ → ℝ)
    (huv : ∀ n < L, (∑ t ∈ L.divisors, u t * ramanujanPacket t n) =
      ∑ t ∈ L.divisors, v t * ramanujanPacket t n)
    (q : ℕ) (hq : q ∈ L.divisors) (hq1 : 1 < q) : u q = v q := by
  apply packet_coefficients_unique L hL u v _ q hq hq1
  intro n
  have hperiod (t : ℕ) (ht : t ∈ L.divisors) :
      ramanujanPacket t n = ramanujanPacket t (n % L) := by
    have hdiv : t ∣ L * (n / L) := dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors ht) _
    have h := ramanujanPacket_period_of_dvd t (L * (n / L)) hdiv (n % L)
    rwa [Nat.mod_add_div] at h
  have hs (a : ℕ → ℝ) :
      (∑ t ∈ L.divisors, a t * ramanujanPacket t n) =
        ∑ t ∈ L.divisors, a t * ramanujanPacket t (n % L) :=
    Finset.sum_congr rfl (fun t ht => congrArg (fun x : ℝ => a t * x) (hperiod t ht))
  exact (hs u).trans ((huv (n % L) (Nat.mod_lt n hL)).trans (hs v).symm)

theorem certificate_packet_unique (c : Certificate) (L : ℕ) (hL : 0 < L)
    (hdL : c.output ∣ L) (hpL : ∀ i, c.input i ∣ L) (u : ℕ → ℝ)
    (hu : ∀ n, c.carry n = ∑ q ∈ L.divisors, u q * ramanujanPacket q n)
    (q : ℕ) (hq : q ∈ L.divisors) (hq1 : 1 < q) :
    u q = commonPacketCoefficient c.input c.coeff c.output q :=
  packet_coefficients_unique L hL u _ (fun n =>
    (hu n).symm.trans (certificate_packet_expansion c L hL hdL hpL n)) q hq hq1

/-- Exact composition of the floor change of coordinates with gcd-cell incidence.
The linear drift is the actual integral reciprocal charge. -/
theorem certificate_cumulative_gcd_expansion (c : Certificate) (L : ℕ) (hL : 0 < L)
    (hdL : c.output ∣ L) (hpL : ∀ i, c.input i ∣ L) (n : ℕ) :
    c.carry n = (n : ℝ) * c.charge +
      (∑ g ∈ L.divisors, if c.output ∣ g then ExactHeadGcdAtoms.atom L g n else 0) -
      ∑ i, (c.coeff i : ℝ) *
        ∑ g ∈ L.divisors, if c.input i ∣ g then ExactHeadGcdAtoms.atom L g n else 0 := by
  have gd (m : ℕ) (hm : m ∣ L) := grid_eq_atom_sum L m n hL.ne'
    (Nat.mem_divisors.mpr ⟨hm, hL.ne'⟩)
  rw [← gd c.output hdL]
  simp_rw [← gd (c.input _) (hpL _)]
  rw [c.carry_eq]
  simp_rw [residueFraction_eq_div_sub_floor (c.input _) n (Nat.zero_lt_of_lt (c.input_gt_one _))]
  rw [residueFraction_eq_div_sub_floor c.output n (Nat.zero_lt_of_lt c.output_gt_one)]
  have hs : (∑ i, (c.coeff i : ℝ) * ((n : ℝ) / c.input i)) =
      (n : ℝ) * (∑ i, (c.coeff i : ℝ) / c.input i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hs, c.reciprocal]
  unfold grid
  ring

/-- A finite test paired with the floor carry is the signed conductor-score
synthesis on all nontrivial divisors of the common period. -/
theorem certificate_pairing_conductor_scores (c : Certificate) (L : ℕ) (hL : 0 < L)
    (hdL : c.output ∣ L) (hpL : ∀ i, c.input i ∣ L) (s : Finset ℕ) (w R : ℕ → ℝ) :
    pairing s w R c.carry = -∑ q ∈ L.divisors.erase 1,
      commonPacketCoefficient c.input c.coeff c.output q * conductorScore L s w R q := by
  let A := commonPacketCoefficient c.input c.coeff c.output
  have hc (n : ℕ) : c.carry n = ∑ q ∈ L.divisors.erase 1, A q * ramanujanPacket q n := by
    have he := Finset.sum_erase_add L.divisors (fun q => A q * ramanujanPacket q n)
      (Nat.one_mem_divisors.mpr hL.ne')
    rw [packet_one, mul_zero, add_zero] at he
    rw [he]
    exact certificate_packet_expansion c L hL hdL hpL n
  change (∑ n ∈ s, w n * R n * c.carry n) = _
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hne, hqL⟩ := Finset.mem_erase.mp hq
  have hpos := Nat.pos_of_mem_divisors hqL
  rw [conductorScore_nontrivial L q hL.ne' (Nat.dvd_of_mem_divisors hqL) (by omega)]
  simp only [mul_neg, neg_neg, pairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp [A]
  ring

/-- Gcd-cell indicators are pointwise disjoint under any choice of finite weights. -/
theorem weighted_gcd_cells_orthogonal (L g h : ℕ) (hgh : g ≠ h)
    (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ s, w n * (if Nat.gcd n L = g then (1 : ℝ) else 0) *
      (if Nat.gcd n L = h then (1 : ℝ) else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  by_cases hg : Nat.gcd n L = g
  · simp [hg, hgh]
  · simp [hg]

private theorem prime_sum (p n : ℕ) (hp : p.Prime) :
    ramanujanSum p n = (if p ∣ n then (p : ℝ) else 0) - 1 := by
  have h := ramanujanSum_divisor_sum p n hp.pos
  rw [hp.divisors, Finset.sum_insert (by simpa using hp.ne_one.symm), Finset.sum_singleton] at h
  have h1 : ramanujanSum 1 n = 1 := by simp [ramanujanSum]
  rw [h1] at h
  linarith

/-- Uniform integration over residues 0 through 5 sends an orthogonal pair to
a pair with inner product one half. -/
theorem modulo_six_primitive_and_integrated_gram :
    (∑ n ∈ Finset.range 6, ramanujanSum 2 n * ramanujanSum 3 n) / 6 = 0 ∧
    (∑ n ∈ Finset.range 6, ramanujanPacket 2 n * ramanujanPacket 3 n) / 6 = (1 / 2 : ℝ) := by
  have h2 : Nat.Prime 2 := by decide
  have h3 : Nat.Prime 3 := by decide
  constructor
  · simp_rw [prime_sum 2 _ h2, prime_sum 3 _ h3]
    norm_num [Finset.sum_range_succ]
  · rw [ramanujanPacket_prime_eq_residue 2 h2, ramanujanPacket_prime_eq_residue 3 h3]
    norm_num [Finset.sum_range_succ, Pareto.residue]

end RiemannResearch.RH.FiniteCarryRamanujanDictionary
