/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTPeriodicEnergy
import RiemannResearch.RH.CRTBlockLegalPackets
import RiemannResearch.RH.CRTBlockRationalData

/-!
# A full-energy, kernel-certified failure of imposed block symmetry

For the block {5,7}, every symmetric exact-head coefficient vector has energy
> 4/5, whereas one explicit asymmetric legal vector has full energy < 7/10.
The finite rational calculations are linked to actual Cesaro means; the
infinite tail is bounded using the proved periodic-energy theorem.
-/
namespace RiemannResearch.RH.CRTBlock.Certificate
noncomputable section
open scoped BigOperators
open ArithmeticCumulative
open RiemannResearch.Probability.ConditionalIID (cesaro)

def sixResidues (u v z : ℝ) (n : ℕ) : ℝ :=
  residueFraction 2 n + residueFraction 3 n - residueFraction 6 n +
    u * residueFraction 5 n + v * residueFraction 7 n + z * residueFraction 35 n

def candidate : ℕ → ℝ := sixResidues (31/6) (-(14/3)) (-(7/6))

def symmetricWitness (a : ℝ) : ℕ → ℝ :=
  sixResidues (5/3-5*a) (7/3-7*a) (-(35/3)+70*a)

def fullEnergy (F : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, mixtureWeight (k+1) * (cesaro F (k+1))^2

def prefixEnergy (F : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range 100, mixtureWeight (k+1) * (cesaro F (k+1))^2

theorem sixResidues_legal (u v z : ℝ) :
    sixResidues u v z ∈ Pareto.legalSeedSpan allPositiveSeeds := by
  let V := Pareto.legalSeedSpan allPositiveSeeds
  have h2 := residueFraction_mem_legal 2 (by norm_num)
  have h3 := residueFraction_mem_legal 3 (by norm_num)
  have h6 := residueFraction_mem_legal 6 (by norm_num)
  have h5 := residueFraction_mem_legal 5 (by norm_num)
  have h7 := residueFraction_mem_legal 7 (by norm_num)
  have h35 := residueFraction_mem_legal 35 (by norm_num)
  change (residueFraction 2 + residueFraction 3 - residueFraction 6 +
    u • residueFraction 5 + v • residueFraction 7 + z • residueFraction 35) ∈ V
  exact V.add_mem (V.add_mem (V.add_mem (V.sub_mem (V.add_mem h2 h3) h6)
    (V.smul_mem u h5)) (V.smul_mem v h7)) (V.smul_mem z h35)

theorem sixResidues_periodic (u v z : ℝ) (n : ℕ) :
    sixResidues u v z (n+210) = sixResidues u v z n := by
  norm_num [sixResidues, residueFraction, Nat.add_mod]

theorem sixResidues_cesaro (u v z : ℝ) (t : ℕ) :
    cesaro (sixResidues u v z) t =
      cesaro (residueFraction 2) t + cesaro (residueFraction 3) t -
      cesaro (residueFraction 6) t + u * cesaro (residueFraction 5) t +
      v * cesaro (residueFraction 7) t + z * cesaro (residueFraction 35) t := by
  simp only [cesaro, sixResidues, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

theorem residueMeanQ_cast (d t : ℕ) (hd : 0 < d) :
    (residueMeanQ d t : ℝ) = cesaro (residueFraction d) t := by
  rw [CesaroResidue.cesaro_residue_exact d t hd]
  unfold residueMeanQ
  push_cast
  rfl

theorem mixtureQ_cast (t : ℕ) : (mixtureQ t : ℝ) = mixtureWeight t := by
  unfold mixtureQ mixtureWeight
  push_cast
  rfl

theorem candidate_cesaro (t : ℕ) : cesaro candidate t = (candidateQ t : ℝ) := by
  rw [candidate, sixResidues_cesaro]
  unfold candidateQ
  push_cast
  rw [residueMeanQ_cast 2 t (by norm_num), residueMeanQ_cast 3 t (by norm_num),
    residueMeanQ_cast 6 t (by norm_num), residueMeanQ_cast 5 t (by norm_num),
    residueMeanQ_cast 7 t (by norm_num), residueMeanQ_cast 35 t (by norm_num)]
  ring

theorem symmetricWitness_cesaro (a : ℝ) (t : ℕ) :
    cesaro (symmetricWitness a) t = (baseQ t : ℝ) + a * (directionQ t : ℝ) := by
  rw [symmetricWitness, sixResidues_cesaro]
  unfold baseQ directionQ
  push_cast
  rw [residueMeanQ_cast 2 t (by norm_num), residueMeanQ_cast 3 t (by norm_num),
    residueMeanQ_cast 6 t (by norm_num), residueMeanQ_cast 5 t (by norm_num),
    residueMeanQ_cast 7 t (by norm_num), residueMeanQ_cast 35 t (by norm_num)]
  ring

theorem prefixQ_cast (u v : ℕ → ℚ) :
    (prefixQ u v : ℝ) = ∑ k ∈ Finset.range 100,
      mixtureWeight (k+1) * (u (k+1) : ℝ) * (v (k+1) : ℝ) := by
  unfold prefixQ
  rw [prefixAux_eq_sum]
  push_cast
  simp only [mixtureQ_cast]

theorem symmetric_prefix_identity (a : ℝ) :
    prefixEnergy (symmetricWitness a) = (aa : ℝ) + 2*a*(bb : ℝ) + a^2*(cc : ℝ) := by
  unfold prefixEnergy aa bb cc
  rw [prefixQ_cast, prefixQ_cast, prefixQ_cast]
  simp_rw [symmetricWitness_cesaro]
  calc
    _ = ∑ k ∈ Finset.range 100,
        (mixtureWeight (k+1)*(baseQ (k+1) : ℝ)*(baseQ (k+1) : ℝ) +
        (2*a)*(mixtureWeight (k+1)*(baseQ (k+1) : ℝ)*(directionQ (k+1) : ℝ)) +
        a^2*(mixtureWeight (k+1)*(directionQ (k+1) : ℝ)*(directionQ (k+1) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]

theorem candidate_prefix_identity : prefixEnergy candidate = (ee : ℝ) := by
  unfold prefixEnergy ee
  rw [prefixQ_cast]
  simp only [candidate_cesaro, pow_two, mul_assoc]

theorem prefixEnergy_le_full (u v z : ℝ) :
    prefixEnergy (sixResidues u v z) ≤ fullEnergy (sixResidues u v z) := by
  obtain ⟨B, hB, hb⟩ := periodDefect_exists_bound (sixResidues u v z) 210
    (by norm_num) (sixResidues_periodic u v z)
  have h := periodic_error_prefix_tail (sixResidues u v z) 210 100 B 0 hB (fun t _ => hb t)
  simp only [sub_zero] at h
  unfold fullEnergy prefixEnergy
  rw [h]
  exact le_add_of_nonneg_right (tsum_nonneg (fun k =>
    mul_nonneg (mixtureWeight_nonneg _) (sq_nonneg _)))

theorem symmetric_fullEnergy_gt (a : ℝ) : (4/5 : ℝ) < fullEnergy (symmetricWitness a) := by
  have hC : (0 : ℝ) < cc := by exact_mod_cast finite_rational_certificates.1
  have hmin : (4/5 : ℝ) < (aa : ℝ) - (bb : ℝ)^2/(cc : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 finite_rational_certificates.2.1
    push_cast at h
    exact h
  have he : (aa : ℝ) + 2*a*(bb : ℝ) + a^2*(cc : ℝ) =
      (aa : ℝ) - (bb : ℝ)^2/(cc : ℝ) +
        (cc : ℝ)*(a+(bb : ℝ)/(cc : ℝ))^2 := by
    field_simp [ne_of_gt hC]
    <;> ring
  have hn := mul_nonneg (le_of_lt hC) (sq_nonneg (a+(bb : ℝ)/(cc : ℝ)))
  have hp : (4/5 : ℝ) < prefixEnergy (symmetricWitness a) := by
    rw [symmetric_prefix_identity, he]
    linarith
  exact hp.trans_le (prefixEnergy_le_full _ _ _)

theorem candidate_mean : periodMean candidate 210 = -(1/3 : ℝ) := by
  unfold periodMean
  rw [← CesaroResidue.cesaro_eq_cumulative candidate 210, candidate_cesaro,
    finite_rational_certificates.2.2.2.1]
  norm_num

theorem candidate_defect (t : ℕ) :
    periodDefect candidate 210 t = ((t : ℚ)*(candidateQ t+1/3) : ℚ) := by
  have he : cumulative candidate t = (t : ℝ) * cesaro candidate t := by
    by_cases ht : t = 0
    · subst t; simp [cumulative, cesaro]
    · rw [CesaroResidue.cesaro_eq_cumulative]
      have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      field_simp
  unfold periodDefect
  rw [candidate_mean, he, candidate_cesaro]
  push_cast
  ring

theorem candidate_defect_bound (t : ℕ) : |periodDefect candidate 210 t| ≤ (25/3 : ℝ) := by
  apply periodDefect_bound_of_finite candidate 210 (by norm_num)
    (sixResidues_periodic _ _ _) (25/3) _ t
  intro r hr
  rw [candidate_defect]
  have h := finite_rational_certificates.2.2.2.2 (⟨r,hr⟩ : Fin 210)
  have hR := (Rat.cast_le (K := ℝ)).2 h
  push_cast at hR ⊢
  exact hR

theorem candidate_fullEnergy_lt : fullEnergy candidate < (7/10 : ℝ) := by
  have hpre : prefixEnergy candidate < (69/100 : ℝ) := by
    rw [candidate_prefix_identity]
    have h := (Rat.cast_lt (K := ℝ)).2 finite_rational_certificates.2.2.1
    push_cast at h
    exact h
  have htail := periodic_error_tail_bound candidate 210 100 (25/3) 0 (by norm_num)
    (fun t _ => candidate_defect_bound t)
  rw [candidate_mean] at htail
  norm_num at htail
  have he := periodic_error_prefix_tail candidate 210 100 (25/3) 0 (by norm_num)
    (fun t _ => candidate_defect_bound t)
  simp only [sub_zero] at he
  change fullEnergy candidate = prefixEnergy candidate + _ at he
  linarith

theorem candidate_head (n : ℕ) (hn : 0 < n) (hN : n ≤ 3) : candidate n = 1 := by
  interval_cases n <;> norm_num [candidate, sixResidues, residueFraction]

theorem symmetric_head (a : ℝ) (n : ℕ) (hn : 0 < n) (hN : n ≤ 3) :
    symmetricWitness a n = 1 := by
  interval_cases n <;> norm_num [symmetricWitness, sixResidues, residueFraction] <;> ring

/-- A strict full-energy gap, not a finite-prefix or floating-point comparison. -/
theorem symmetry_loses_full_energy (a : ℝ) :
    fullEnergy candidate + (1/10 : ℝ) < fullEnergy (symmetricWitness a) := by
  linarith [candidate_fullEnergy_lt, symmetric_fullEnergy_gt a]

/-- The numerical functions are exactly the block packets from the CRT construction. -/
theorem block_packets_five_seven (n : ℕ) :
    blockPacket {5} n = 5 * residueFraction 5 n ∧
    blockPacket {7} n = 7 * residueFraction 7 n ∧
    blockPacket {5,7} n = 5 * residueFraction 5 n + 7 * residueFraction 7 n -
      35 * residueFraction 35 n := by
  have h5 : ({5} : Finset ℕ).powerset = {∅,{5}} := by decide +kernel
  have h7 : ({7} : Finset ℕ).powerset = {∅,{7}} := by decide +kernel
  have h57 : ({5,7} : Finset ℕ).powerset = {∅,{5},{7},{5,7}} := by decide +kernel
  simp only [blockPacket, h5,h7,h57]
  norm_num [Finset.sum_insert, Finset.ext_iff, residueFraction, Nat.mod_one] <;> ring

theorem candidate_packet_representation (n : ℕ) :
    candidate n = residueFraction 2 n + residueFraction 3 n - residueFraction 6 n +
      blockPacket {5} n - (7/10 : ℝ) * blockPacket {7} n +
        (1/30 : ℝ) * blockPacket {5,7} n := by
  obtain ⟨h5,h7,h57⟩ := block_packets_five_seven n
  rw [h5,h7,h57]
  unfold candidate sixResidues
  ring

theorem symmetric_packet_representation (a : ℝ) (n : ℕ) :
    symmetricWitness a n = residueFraction 2 n + residueFraction 3 n - residueFraction 6 n +
      a * blockPacket {5} n + a * blockPacket {7} n +
        (1/3-2*a) * blockPacket {5,7} n := by
  obtain ⟨h5,h7,h57⟩ := block_packets_five_seven n
  rw [h5,h7,h57]
  unfold symmetricWitness sixResidues
  ring

end
end RiemannResearch.RH.CRTBlock.Certificate
