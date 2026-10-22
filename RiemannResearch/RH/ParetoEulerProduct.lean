import RiemannResearch.RH.ParetoCoprimeObstruction
import Mathlib.NumberTheory.ZetaValues

/-!
# Complete finite Euler product for the coprime obstruction

Source: `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §3.3.
The exact finite product follows by sieving one prime at a time in the convergent
Basel series. It is proved for every nonzero even support modulus.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def sievedReciprocalSquare (S : Finset ℕ) (n : ℕ) : ℝ :=
  if ∀ p ∈ S, ¬ p ∣ n then 1 / (n : ℝ) ^ 2 else 0

theorem sievedReciprocalSquare_prime_mul (S : Finset ℕ)
    (hS : ∀ q ∈ S, Nat.Prime q) (p n : ℕ) (hp : Nat.Prime p) (hpS : p ∉ S) :
    sievedReciprocalSquare S (p * n) =
      (1 / (p : ℝ) ^ 2) * sievedReciprocalSquare S n := by
  have he : (∀ q ∈ S, ¬ q ∣ p * n) ↔ (∀ q ∈ S, ¬ q ∣ n) := by
    constructor
    · intro h q hq hqn
      exact h q hq (dvd_mul_of_dvd_right hqn p)
    · intro h q hq hqpn
      rcases (hS q hq).dvd_mul.mp hqpn with hqp | hqn
      · rcases (Nat.dvd_prime hp).mp hqp with hq1 | hqp
        · exact (hS q hq).ne_one hq1
        · exact hpS (hqp ▸ hq)
      · exact h q hq hqn
  unfold sievedReciprocalSquare
  simp only [he]
  split_ifs <;> simp [Nat.cast_mul, mul_pow, one_div_mul_one_div, mul_comm]

theorem sievedReciprocalSquare_insert (S : Finset ℕ) (p n : ℕ) :
    sievedReciprocalSquare (insert p S) n = sievedReciprocalSquare S n -
      (if p ∣ n then sievedReciprocalSquare S n else 0) := by
  by_cases hp : p ∣ n <;> by_cases hs : ∀ q ∈ S, ¬ q ∣ n <;>
    simp [sievedReciprocalSquare, hp, hs]

/-- An exact finite Euler product; no limit over the prime set is involved. -/
theorem sievedReciprocalSquare_hasSum (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    HasSum (sievedReciprocalSquare S)
      ((Real.pi ^ 2 / 6) * ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      have he : sievedReciprocalSquare ∅ =
          (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
        funext n
        simp [sievedReciprocalSquare]
      rw [he]
      simpa using hasSum_zeta_two
  | @insert p S hpS ih =>
      intro hS
      have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, Nat.Prime q := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      have hs := ih hS'
      have hmult : HasSum
          (fun n : ℕ => if p ∣ n then sievedReciprocalSquare S n else 0)
          ((1 / (p : ℝ) ^ 2) *
            ((Real.pi ^ 2 / 6) * ∏ q ∈ S, (1 - 1 / (q : ℝ) ^ 2))) := by
        have hinj : Function.Injective (fun n : ℕ => p * n) := by
          intro n m h
          exact Nat.eq_of_mul_eq_mul_left hp.pos h
        have hout : ∀ n ∉ Set.range (fun n : ℕ => p * n),
            (if p ∣ n then sievedReciprocalSquare S n else 0) = 0 := by
          intro n hn
          have hnd : ¬ p ∣ n := by
            rintro ⟨m, hm⟩
            exact hn ⟨m, hm.symm⟩
          simp [hnd]
        apply (hinj.hasSum_iff hout).mp
        have he :
            ((fun n : ℕ => if p ∣ n then sievedReciprocalSquare S n else 0) ∘
              (fun n : ℕ => p * n)) =
            (fun n : ℕ => (1 / (p : ℝ) ^ 2) * sievedReciprocalSquare S n) := by
          funext n
          simp only [Function.comp_def, dvd_mul_right, if_true]
          exact sievedReciprocalSquare_prime_mul S hS' p n hp hpS
        rw [he]
        exact hs.mul_left _
      have hsub := hs.sub hmult
      have he : sievedReciprocalSquare (insert p S) =
          (fun n : ℕ => sievedReciprocalSquare S n -
            (if p ∣ n then sievedReciprocalSquare S n else 0)) := by
        funext n
        exact sievedReciprocalSquare_insert S p n
      have hv : ((Real.pi ^ 2 / 6) * ∏ q ∈ insert p S, (1 - 1 / (q : ℝ) ^ 2)) =
          ((Real.pi ^ 2 / 6) * ∏ q ∈ S, (1 - 1 / (q : ℝ) ^ 2)) -
            (1 / (p : ℝ) ^ 2) *
              ((Real.pi ^ 2 / 6) * ∏ q ∈ S, (1 - 1 / (q : ℝ) ^ 2)) := by
        rw [Finset.prod_insert hpS]
        ring
      rw [he, hv]
      exact hsub

theorem coprime_iff_avoids_primeFactors (n P : ℕ) (hP : P ≠ 0) :
    Nat.Coprime n P ↔ ∀ p ∈ P.primeFactors, ¬ p ∣ n := by
  constructor
  · intro hc p hp hpn
    have hprime := (Nat.mem_primeFactors.mp hp).1
    have hpP := (Nat.mem_primeFactors.mp hp).2.1
    have hdiv : p ∣ 1 := by
      simpa only [show Nat.gcd n P = 1 from hc] using Nat.dvd_gcd hpn hpP
    exact hprime.ne_one (Nat.dvd_one.mp hdiv)
  · intro h
    change Nat.gcd n P = 1
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpP : p ∣ P := dvd_trans hpd (Nat.gcd_dvd_right n P)
    have hpn : p ∣ n := dvd_trans hpd (Nat.gcd_dvd_left n P)
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpP, hP⟩) hpn

theorem coprime_reciprocalSquare_hasSum (P : ℕ) (hP : P ≠ 0) :
    HasSum (fun n : ℕ => if Nat.Coprime n P then (1 : ℝ) / (n : ℝ) ^ 2 else 0)
      ((Real.pi ^ 2 / 6) * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) := by
  have hprime : ∀ p ∈ P.primeFactors, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have h := sievedReciprocalSquare_hasSum P.primeFactors hprime
  have he : sievedReciprocalSquare P.primeFactors =
      (fun n : ℕ => if Nat.Coprime n P then (1 : ℝ) / (n : ℝ) ^ 2 else 0) := by
    funext n
    simp only [sievedReciprocalSquare, ← coprime_iff_avoids_primeFactors n P hP]
  rw [he] at h
  exact h

theorem coprime_reciprocalSquare_decomposition_of_even (P n : ℕ) (h2 : 2 ∣ P) :
    (if Nat.Coprime n P then (1 : ℝ) / (n : ℝ) ^ 2 else 0) =
      (if n = 1 then 1 else 0) + coprimePairMass P n := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [coprimePairMass, coprimePairIndex]
  by_cases hc : Nat.Coprime n P
  · have hnd2 : ¬ 2 ∣ n := by
      intro h2n
      have hdiv : 2 ∣ 1 := by
        simpa only [show Nat.gcd n P = 1 from hc] using Nat.dvd_gcd h2n h2
      norm_num at hdiv
    have hodd : n % 2 = 1 := by
      have hlt := Nat.mod_lt n (by decide : 0 < 2)
      have hne : n % 2 ≠ 0 := by
        simpa only [Nat.dvd_iff_mod_eq_zero] using hnd2
      omega
    have hn3 : 3 ≤ n := by omega
    simp [hn1, coprimePairMass, coprimePairIndex, hn3, hodd]
  · simp [hn1, hc, coprimePairMass, coprimePairIndex]

/-- Complete Euler evaluation of the actual obstruction mass for every
nonzero even modulus, including nonsquarefree moduli. -/
theorem coprimeReciprocalSquareMass_eulerProduct (P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P) :
    coprimeReciprocalSquareMass P =
      (Real.pi ^ 2 / 6) * ∏ p ∈ P.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  have hsum : HasSum
      (fun n : ℕ => (if n = 1 then (1 : ℝ) else 0) + coprimePairMass P n)
      (coprimeReciprocalSquareMass P) := by
    exact (hasSum_ite_eq 1 (1 : ℝ)).add (coprimePairMass_summable P).hasSum
  have he : (fun n : ℕ => (if n = 1 then (1 : ℝ) else 0) + coprimePairMass P n) =
      (fun n : ℕ => if Nat.Coprime n P then (1 : ℝ) / (n : ℝ) ^ 2 else 0) := by
    funext n
    exact (coprime_reciprocalSquare_decomposition_of_even P n h2).symm
  rw [he] at hsum
  exact hsum.unique (coprime_reciprocalSquare_hasSum P hP)

/-- Exact evaluation of the complete fixed `{2,3}` support obstruction mass. -/
theorem coprimeReciprocalSquareMass_six :
    coprimeReciprocalSquareMass 6 = Real.pi ^ 2 / 9 := by
  rw [coprimeReciprocalSquareMass_eulerProduct 6 (by decide) (by decide)]
  have hfac : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by decide,
      Nat.primeFactors_mul (by decide) (by decide),
      (show Nat.Prime 2 by decide).primeFactors,
      (show Nat.Prime 3 by decide).primeFactors]
    decide
  rw [hfac]
  norm_num
  ring

/-- Evaluated error floor for all actual packet conductors supported on `{2,3}`. -/
theorem packetCombination_two_three_error_lower_bound
    (Q : Finset ℕ) (a : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, ∃ b : ℕ, q ∣ 6 ^ b) :
    (Real.pi ^ 2 - 9) / (2 * Real.pi ^ 2) ≤
      ∑' k, positiveWeight k * (1 - ∑ q ∈ Q, a q * ramanujanPacket q k) ^ 2 := by
  have h := packetCombination_fixedSupport_full_error_lower_bound 6 Q a hQ
  rw [coprimeReciprocalSquareMass_six] at h
  have he : (Real.pi ^ 2 - 9) / (2 * Real.pi ^ 2) =
      (Real.pi ^ 2 / 9 - 1) / (2 * (Real.pi ^ 2 / 9)) := by
    field_simp [Real.pi_ne_zero]
  rw [he]
  exact h

/-- Evaluated noise-to-signal floor for actual finite `{2,3}` packet sums. -/
theorem packetCombination_two_three_noiseSignal_lower_bound
    (Q : Finset ℕ) (a : ℕ → ℝ)
    (hQ : ∀ q ∈ Q, ∃ b : ℕ, q ∣ 6 ^ b)
    (hm : paretoMean (fun k => ∑ q ∈ Q, a q * ramanujanPacket q k) ≠ 0) :
    (Real.pi ^ 2 - 9) / (Real.pi ^ 2 + 9) ≤
      noiseSignalRatio (fun k => ∑ q ∈ Q, a q * ramanujanPacket q k) := by
  have h := packetCombination_fixedSupport_noiseSignal_lower_bound 6 Q a hQ hm
  rw [coprimeReciprocalSquareMass_six] at h
  have hp : Real.pi ^ 2 + 9 ≠ 0 := by positivity
  have hp' : Real.pi ^ 2 / 9 + 1 ≠ 0 := by positivity
  have he : (Real.pi ^ 2 - 9) / (Real.pi ^ 2 + 9) =
      (Real.pi ^ 2 / 9 - 1) / (Real.pi ^ 2 / 9 + 1) := by
    field_simp [hp, hp']
  rw [he]
  exact h

end
end RiemannResearch.RH.Pareto
