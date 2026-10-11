import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ParetoNoiseSignal
import RiemannResearch.LinearAlgebra.NoiseSignalQuadratic

/-!
# Coprime increments and finite Pareto pair certificates

Source: `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, Section 3.3.

The packet increment is proved for the actual residue/Möbius packet functions.
Every finite set of odd coprime indices yields a lower bound for the complete
infinite Pareto squared error. Convergence of the finite certificates proves the
bound for all such indices. An Euler product evaluation is not assumed here.
-/

open scoped BigOperators
open Filter
open RiemannResearch.LinearAlgebra.NoiseSignalQuadratic
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- At a positive index coprime to the conductor, every residue increment is
its value at the first coordinate. -/
theorem residue_difference_of_coprime_divisor (q n d : ℕ)
    (hn : 0 < n) (hc : Nat.Coprime n q) (hd : d ∈ q.divisors) :
    residue d n - residue d (n - 1) = residue d 1 := by
  have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hdp : 0 < d := Nat.pos_of_mem_divisors hd
  have hgcd : Nat.gcd n q = 1 := hc
  rw [residue_difference d n hn]
  by_cases hd1 : d = 1
  · subst d
    norm_num [residue]
  · have hnd : ¬ d ∣ n := by
      intro hdn
      have hdiv : d ∣ 1 := by
        simpa only [hgcd] using Nat.dvd_gcd hdn hdq
      exact hd1 (Nat.dvd_one.mp hdiv)
    have hdgt : 1 < d := by omega
    simp [hnd, residue, Nat.mod_eq_of_lt hdgt]

/-- The common increment needs no prime or squarefree restriction on `q`. -/
theorem ramanujanPacket_difference_of_coprime (q n : ℕ)
    (hn : 0 < n) (hc : Nat.Coprime n q) :
    ramanujanPacket q n - ramanujanPacket q (n - 1) = ramanujanPacket q 1 := by
  unfold ramanujanPacket
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_sub, residue_difference_of_coprime_divisor q n d hn hc hd]

/-- An actual finite packet sum has its first value as increment at any positive
index coprime to every conductor. -/
theorem packetCombination_difference_of_coprime (Q : Finset ℕ) (a : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) (hc : ∀ q ∈ Q, Nat.Coprime n q) :
    (∑ q ∈ Q, a q * ramanujanPacket q n) -
        (∑ q ∈ Q, a q * ramanujanPacket q (n - 1)) =
      ∑ q ∈ Q, a q * ramanujanPacket q 1 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub, ramanujanPacket_difference_of_coprime q n hn (hc q hq)]

/-- Odd indices at least three yield disjoint coordinate pairs, also disjoint
from the first coordinate. The result applies to any nonnegative summable energy. -/
theorem finite_odd_pairs_sum_le_tsum (s : Finset ℕ) (e : ℕ → ℝ)
    (hmin : ∀ n ∈ s, 3 ≤ n) (hodd : ∀ n ∈ s, n % 2 = 1)
    (he : ∀ k, 0 ≤ e k) (hs : Summable e) :
    e 1 + (∑ n ∈ s, (e (n - 1) + e n)) ≤ ∑' k, e k := by
  have hd : Disjoint (s.image (fun n => n - 1)) s := by
    apply Finset.disjoint_left.mpr
    intro k hk hs'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have := hmin n hn
    have := hodd n hn
    have := hodd (n - 1) hs'
    omega
  have h1 : 1 ∉ s.image (fun n => n - 1) ∪ s := by
    intro h
    rcases Finset.mem_union.mp h with hp | hs'
    · obtain ⟨n, hn, hne⟩ := Finset.mem_image.mp hp
      have := hmin n hn
      omega
    · have := hmin 1 hs'
      omega
  have himage : (∑ k ∈ s.image (fun n => n - 1), e k) =
      ∑ n ∈ s, e (n - 1) := by
    apply Finset.sum_image
    intro x hx y hy hxy
    dsimp only at hxy
    have := hmin x hx
    have := hmin y hy
    omega
  have hsum : (∑ k ∈ insert 1 (s.image (fun n => n - 1) ∪ s), e k) =
      e 1 + (∑ n ∈ s, (e (n - 1) + e n)) := by
    rw [Finset.sum_insert h1, Finset.sum_union hd, himage,
      Finset.sum_add_distrib]
  rw [← hsum]
  exact hs.sum_le_tsum _ (fun k _ => he k)

/-- Finite reciprocal-square mass already gives a lower bound for the complete
Pareto error. All common-increment hypotheses concern actual function values. -/
theorem common_increment_full_error_lower_bound (s : Finset ℕ) (f : ℕ → ℝ)
    (hmin : ∀ n ∈ s, 3 ≤ n) (hodd : ∀ n ∈ s, n % 2 = 1)
    (hinc : ∀ n ∈ s, f n - f (n - 1) = f 1)
    (hs : Summable (fun k => positiveWeight k * (1 - f k) ^ 2)) :
    (reciprocalSquareMass s (fun n => (n : ℝ)) - 1) /
        (2 * reciprocalSquareMass s (fun n => (n : ℝ))) ≤
      ∑' k, positiveWeight k * (1 - f k) ^ 2 := by
  have hn : ∀ n ∈ s, 1 < (n : ℝ) := by
    intro n hn
    exact_mod_cast (show 1 < n by have := hmin n hn; omega)
  have hp := finite_pair_energy_lower_bound s (fun n => (n : ℝ))
    (fun n => f (n - 1)) f (f 1) hn hinc
  have hconvert :
      (1 - f 1) ^ 2 / 2 +
        (∑ n ∈ s, ((1 - f (n - 1)) ^ 2 / (((n : ℝ) - 1) * n) +
          (1 - f n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) =
      positiveWeight 1 * (1 - f 1) ^ 2 +
        ∑ n ∈ s, (positiveWeight (n - 1) * (1 - f (n - 1)) ^ 2 +
          positiveWeight n * (1 - f n) ^ 2) := by
    congr 1
    · norm_num [positiveWeight] <;> ring
    · apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := by have := hmin n hn; omega
      simp only [positiveWeight, Nat.cast_sub hn1, Nat.cast_one]
      ring
  rw [hconvert] at hp
  exact hp.trans (finite_odd_pairs_sum_le_tsum s
    (fun k => positiveWeight k * (1 - f k) ^ 2) hmin hodd
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)) hs)

/-- Fully instantiated packet-family certificate; no summability assumption is
left because finite residue/Möbius packet sums are bounded. -/
theorem packetCombination_coprime_full_error_lower_bound
    (Q s : Finset ℕ) (a : ℕ → ℝ)
    (hmin : ∀ n ∈ s, 3 ≤ n) (hodd : ∀ n ∈ s, n % 2 = 1)
    (hc : ∀ n ∈ s, ∀ q ∈ Q, Nat.Coprime n q) :
    (reciprocalSquareMass s (fun n => (n : ℝ)) - 1) /
        (2 * reciprocalSquareMass s (fun n => (n : ℝ))) ≤
      ∑' k, positiveWeight k * (1 - ∑ q ∈ Q, a q * ramanujanPacket q k) ^ 2 := by
  apply common_increment_full_error_lower_bound s
    (fun k => ∑ q ∈ Q, a q * ramanujanPacket q k) hmin hodd
  · intro n hn
    exact packetCombination_difference_of_coprime Q a n
      (by have := hmin n hn; omega) (hc n hn)
  · exact packetCombination_error_summable Q a

/-- A conductor supported on the prime factors of `P` can be supplied by any
explicit divisibility witness `q ∣ P ^ a`. -/
theorem coprime_of_dvd_power (n P q a : ℕ) (hc : Nat.Coprime n P)
    (hq : q ∣ P ^ a) : Nat.Coprime n q := by
  exact (hc.pow_right a).of_dvd_right hq

/-- Finite certificate specialized to conductors dividing powers of `P`. -/
theorem packetCombination_fixedSupport_finite_error_lower_bound
    (P : ℕ) (Q s : Finset ℕ) (a : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, ∃ b : ℕ, q ∣ P ^ b)
    (hmin : ∀ n ∈ s, 3 ≤ n) (hodd : ∀ n ∈ s, n % 2 = 1)
    (hc : ∀ n ∈ s, Nat.Coprime n P) :
    (reciprocalSquareMass s (fun n => (n : ℝ)) - 1) /
        (2 * reciprocalSquareMass s (fun n => (n : ℝ))) ≤
      ∑' k, positiveWeight k * (1 - ∑ q ∈ Q, a q * ramanujanPacket q k) ^ 2 := by
  apply packetCombination_coprime_full_error_lower_bound Q s a hmin hodd
  intro n hn q hq
  obtain ⟨b, hb⟩ := hQ q hq
  exact coprime_of_dvd_power n P q b (hc n hn) hb

/-- The odd positive pair indices available for a fixed support modulus. -/
def coprimePairIndex (P n : ℕ) : Prop :=
  3 ≤ n ∧ n % 2 = 1 ∧ Nat.Coprime n P

instance (P n : ℕ) : Decidable (coprimePairIndex P n) :=
  inferInstanceAs (Decidable (3 ≤ n ∧ n % 2 = 1 ∧ Nat.Coprime n P))

/-- The reciprocal-square mass of an admissible index, zero elsewhere. -/
def coprimePairMass (P n : ℕ) : ℝ :=
  if coprimePairIndex P n then 1 / (n : ℝ) ^ 2 else 0

def coprimeReciprocalSquareMass (P : ℕ) : ℝ :=
  1 + ∑' n, coprimePairMass P n

theorem coprimePairMass_nonneg (P n : ℕ) : 0 ≤ coprimePairMass P n := by
  unfold coprimePairMass
  split_ifs
  · positivity
  · exact le_refl 0

/-- Summability follows from the already verified Pareto probability masses. -/
theorem coprimePairMass_summable (P : ℕ) : Summable (coprimePairMass P) := by
  apply Summable.of_nonneg_of_le (coprimePairMass_nonneg P) _
    (positiveWeight_summable.mul_left 2)
  intro n
  unfold coprimePairMass
  split_ifs with hn
  · have hn3 : 3 ≤ n := hn.1
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : 0 < (n : ℝ) := by linarith
    unfold positiveWeight
    rw [show (2 : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      2 / ((n : ℝ) * ((n : ℝ) + 1)) by ring]
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0)
      (mul_pos hn0 (by linarith))).2
    nlinarith
  · exact mul_nonneg (by norm_num) (positiveWeight_nonneg n)

theorem coprimeReciprocalSquareMass_pos (P : ℕ) :
    0 < coprimeReciprocalSquareMass P := by
  have ht : 0 ≤ ∑' n, coprimePairMass P n :=
    tsum_nonneg (coprimePairMass_nonneg P)
  unfold coprimeReciprocalSquareMass
  linarith

/-- The finite certificates converge to the full coprime-index mass. -/
theorem coprimeReciprocalSquareMass_tendsto (P : ℕ) :
    Tendsto
      (fun N => reciprocalSquareMass
        ((Finset.range N).filter (coprimePairIndex P)) (fun n => (n : ℝ)))
      atTop (nhds (coprimeReciprocalSquareMass P)) := by
  simpa only [reciprocalSquareMass, coprimeReciprocalSquareMass,
    Finset.sum_filter, coprimePairMass] using
    tendsto_const_nhds.add (coprimePairMass_summable P).hasSum.tendsto_sum_nat

/-- Complete fixed-support error floor with the actual infinite reciprocal-square
mass. No evaluation by an Euler product is used or assumed. -/
theorem packetCombination_fixedSupport_full_error_lower_bound
    (P : ℕ) (Q : Finset ℕ) (a : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, ∃ b : ℕ, q ∣ P ^ b) :
    (coprimeReciprocalSquareMass P - 1) /
        (2 * coprimeReciprocalSquareMass P) ≤
      ∑' k, positiveWeight k * (1 - ∑ q ∈ Q, a q * ramanujanPacket q k) ^ 2 := by
  have hfinite (N : ℕ) :
      (reciprocalSquareMass
          ((Finset.range N).filter (coprimePairIndex P)) (fun n => (n : ℝ)) - 1) /
        (2 * reciprocalSquareMass
          ((Finset.range N).filter (coprimePairIndex P)) (fun n => (n : ℝ))) ≤
        ∑' k, positiveWeight k * (1 - ∑ q ∈ Q, a q * ramanujanPacket q k) ^ 2 := by
    apply packetCombination_fixedSupport_finite_error_lower_bound P Q
      ((Finset.range N).filter (coprimePairIndex P)) a hQ
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2.1
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2.2
  have hA := coprimeReciprocalSquareMass_tendsto P
  have hden : (2 : ℝ) * coprimeReciprocalSquareMass P ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (coprimeReciprocalSquareMass_pos P))
  have hratio := (hA.sub (tendsto_const_nhds (x := (1 : ℝ)))).div
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hA) hden
  exact isClosed_Iic.mem_of_tendsto hratio (Filter.Eventually.of_forall hfinite)

/-- The corresponding complete noise-to-signal obstruction at nonzero mean. -/
theorem packetCombination_fixedSupport_noiseSignal_lower_bound
    (P : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, ∃ b : ℕ, q ∣ P ^ b)
    (hm : paretoMean (fun k => ∑ q ∈ Q, c q * ramanujanPacket q k) ≠ 0) :
    (coprimeReciprocalSquareMass P - 1) /
        (coprimeReciprocalSquareMass P + 1) ≤
      noiseSignalRatio (fun k => ∑ q ∈ Q, c q * ramanujanPacket q k) := by
  let f : ℕ → ℝ := fun k => ∑ q ∈ Q, c q * ramanujanPacket q k
  obtain ⟨C, hC⟩ := packetCombination_bounded Q c
  let a : ℝ := paretoMean f / (paretoVariance f + (paretoMean f) ^ 2)
  have hbound := packetCombination_fixedSupport_full_error_lower_bound
    P Q (fun q => a * c q) hQ
  have heq : (fun k => ∑ q ∈ Q, (a * c q) * ramanujanPacket q k) =
      (fun k => a * f k) := by
    funext k
    simp only [f, Finset.mul_sum, mul_assoc]
  simp_rw [congrFun heq] at hbound
  have herr :
      (coprimeReciprocalSquareMass P - 1) /
        (2 * coprimeReciprocalSquareMass P) ≤ paretoError (fun k => a * f k) := by
    change _ ≤ ∑' k, positiveWeight k * ((1 - a * f k) * (1 - a * f k))
    simpa only [← sq] using hbound
  have hop := paretoError_scale_completion (f := f) hC hm a
  change paretoError (fun k => a * f k) = _ at hop
  simp only [a, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hop
  rw [hop] at herr
  have hmpos : 0 < (paretoMean f) ^ 2 := sq_pos_of_ne_zero hm
  have hdpos : 0 < paretoVariance f + (paretoMean f) ^ 2 :=
    add_pos_of_nonneg_of_pos (paretoVariance_nonneg f) hmpos
  have hApos := coprimeReciprocalSquareMass_pos P
  have hcross := (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hApos)
    hdpos).mp herr
  change (coprimeReciprocalSquareMass P - 1) /
    (coprimeReciprocalSquareMass P + 1) ≤ paretoVariance f / (paretoMean f) ^ 2
  apply (div_le_div_iff₀ (by linarith) hmpos).2
  nlinarith

end
end RiemannResearch.RH.Pareto
