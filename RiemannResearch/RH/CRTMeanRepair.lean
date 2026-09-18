import RiemannResearch.RH.CRTPeriodicEnergy
import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.CoupledCorrectionRHBridge

/-!
# Legal square-wave repairs of the period mean
Source: user-provided CRT handoff, Section 13.6, and the explicit construction
H_A = 2 g_(2A) - g_A developed in this continuation. No RH assumption is used.
-/
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
noncomputable section
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ArithmeticCumulative.CesaroResidue
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.Cesaro

def meanPulse (A n : ℕ) : ℝ :=
  2 * residueFraction (2*A) n - residueFraction A n

def meanRepair (F : ℕ → ℝ) (m : ℝ) (A n : ℕ) : ℝ :=
  F n - 2*m*meanPulse A n

theorem meanPulse_legal (A : ℕ) (hA : 0 < A) :
    meanPulse A ∈ legalSeedSpan (Set.Ici 1) := by
  have h1 : residueFraction A ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [allPositiveSeeds, Set.Ici, Nat.lt_iff_add_one_le, Nat.zero_add]
      using residueFraction_mem_legal A hA
  have h2 : residueFraction (2*A) ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [allPositiveSeeds, Set.Ici, Nat.lt_iff_add_one_le, Nat.zero_add]
      using residueFraction_mem_legal (2*A) (by omega)
  convert (legalSeedSpan (Set.Ici 1)).sub_mem
    ((legalSeedSpan (Set.Ici 1)).smul_mem (2 : ℝ) h2) h1 using 1
  ext n
  simp [meanPulse, smul_eq_mul]

theorem meanPulse_zero_before (A n : ℕ) (hn : n < A) :
    meanPulse A n = 0 := by
  have hA0 : 0 < A := by omega
  have hA : (A : ℝ) ≠ 0 := by positivity
  unfold meanPulse residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < 2*A), Nat.mod_eq_of_lt hn]
  push_cast
  field_simp
  ring

theorem meanPulse_periodic (A : ℕ) (n : ℕ) :
    meanPulse A (n+2*A) = meanPulse A n := by
  unfold meanPulse residueFraction
  simp [Nat.add_mod]

theorem cesaro_meanPulse (A t : ℕ) :
    cesaro (meanPulse A) t =
      2*cesaro (residueFraction (2*A)) t - cesaro (residueFraction A) t := by
  simp only [cesaro, meanPulse, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem cesaro_meanPulse_abs_le_one (A t : ℕ) (hA : 0 < A) :
    |cesaro (meanPulse A) t| ≤ 1 := by
  have h0 := cesaro_residue_nonneg (2*A) t
  have h1 := cesaro_residue_le_half (2*A) t (by omega)
  have h2 := cesaro_residue_nonneg A t
  have h3 := cesaro_residue_le_half A t hA
  rw [cesaro_meanPulse, abs_le]
  constructor <;> linarith

theorem cesaro_meanPulse_zero_before (A t : ℕ) (ht : t < A) :
    cesaro (meanPulse A) t = 0 := by
  unfold cesaro
  have hs : ∑ n ∈ Finset.Icc 1 t, meanPulse A n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact meanPulse_zero_before A n (lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 ht)
  rw [hs, zero_div]

theorem cesaro_meanPulse_complete_periods (A k : ℕ) (hA : 0 < A) (hk : 0 < k) :
    cesaro (meanPulse A) (k*(2*A)) = 1/2 := by
  rw [cesaro_meanPulse, cesaro_residue_complete_periods (2*A) k (by omega) hk]
  rw [show k*(2*A) = (2*k)*A by ring,
    cesaro_residue_complete_periods A (2*k) hA (by omega)]
  have hAR : (A : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem meanPulse_periodMean (A : ℕ) (hA : 0 < A) :
    periodMean (meanPulse A) (2*A) = 1/2 := by
  have h := cesaro_meanPulse_complete_periods A 1 hA (by omega)
  simpa only [one_mul, cesaro_eq_cumulative, periodMean] using h

theorem meanRepair_legal (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (m : ℝ) (A : ℕ) (hA : 0 < A) :
    meanRepair F m A ∈ legalSeedSpan (Set.Ici 1) := by
  convert (legalSeedSpan (Set.Ici 1)).sub_mem hF
    ((legalSeedSpan (Set.Ici 1)).smul_mem (2*m) (meanPulse_legal A hA)) using 1
  ext n
  simp [meanRepair, smul_eq_mul]

theorem meanRepair_same_head (F : ℕ → ℝ) (m : ℝ) (A n : ℕ) (hn : n < A) :
    meanRepair F m A n = F n := by
  simp [meanRepair, meanPulse_zero_before A n hn]

theorem meanRepair_mem_headClass (Y : ℕ) (F : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y) (m : ℝ) (A : ℕ) (hA : Y < A) :
    meanRepair F m A ∈ conditionalHeadClass Y := by
  refine ⟨meanRepair_legal F hF.1 m A (by omega), ?_⟩
  intro n hn hnY
  rw [meanRepair_same_head F m A n (by omega)]
  exact hF.2 n hn hnY

theorem periodic_multiple (F : ℕ → ℝ) (Q : ℕ)
    (hp : ∀ n, F (n+Q) = F n) (k n : ℕ) :
    F (n+Q*k) = F n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]

theorem periodMean_multiple (F : ℕ → ℝ) (Q k : ℕ) (hQ : 0 < Q) (hk : 0 < k)
    (hp : ∀ n, F (n+Q) = F n) :
    periodMean F (Q*k) = periodMean F Q := by
  have h := cumulative_periods F Q k 0 hp
  simp only [cumulative, Finset.range_zero, Finset.sum_empty,
    add_zero] at h
  unfold periodMean cumulative
  rw [h]
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem periodMean_meanRepair (F : ℕ → ℝ) (m : ℝ) (A Q : ℕ) :
    periodMean (meanRepair F m A) Q =
      periodMean F Q - 2*m*periodMean (meanPulse A) Q := by
  unfold periodMean cumulative meanRepair
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- An explicit common period, requiring no coprimality assumption. -/
theorem meanRepair_periodic (F : ℕ → ℝ) (Q A : ℕ)
    (hp : ∀ n, F (n+Q) = F n) (m : ℝ) (n : ℕ) :
    meanRepair F m A (n+Q*(2*A)) = meanRepair F m A n := by
  unfold meanRepair
  rw [periodic_multiple F Q hp (2*A) n]
  rw [show Q*(2*A) = (2*A)*Q by ring,
    periodic_multiple (meanPulse A) (2*A) (meanPulse_periodic A) Q n]

theorem meanRepair_zero_mean (F : ℕ → ℝ) (Q A : ℕ) (hQ : 0 < Q) (hA : 0 < A)
    (hp : ∀ n, F (n+Q) = F n) :
    periodMean (meanRepair F (periodMean F Q) A) (Q*(2*A)) = 0 := by
  rw [periodMean_meanRepair, periodMean_multiple F Q (2*A) hQ (by omega) hp]
  have hP : periodMean (meanPulse A) (Q*(2*A)) = 1/2 := by
    rw [Nat.mul_comm Q (2*A),
      periodMean_multiple (meanPulse A) (2*A) Q (by omega) hQ (meanPulse_periodic A),
      meanPulse_periodMean A hA]
  rw [hP]
  ring

/-- The actual infinite conditional energy of the pulse has a conductor-free bound. -/
theorem meanPulse_energy_le (A : ℕ) (hA : 0 < A) :
    conditionalMeanSquare (meanPulse A) ≤ 2 / ((A : ℝ)+1) := by
  have hE := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) (meanPulse_legal A hA)
  have hEt : Summable (fun k : ℕ => conditionalWeight (k+(A-1)) *
      (cesaro (meanPulse A) (k+(A-1)+1))^2) :=
    hE.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hq : Summable conditionalWeight := hasSum_mixtureWeight.summable
  have hqt : Summable (fun k : ℕ => conditionalWeight (k+(A-1))) :=
    hq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hprefix : (∑ k ∈ Finset.range (A-1),
      conditionalWeight k * (cesaro (meanPulse A) (k+1))^2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [cesaro_meanPulse_zero_before A (k+1)
      (by have := Finset.mem_range.mp hk; omega)]
    ring
  have hsplit := (hE.sum_add_tsum_nat_add (A-1)).symm
  change conditionalMeanSquare (meanPulse A) = _ at hsplit
  rw [hsplit, hprefix, zero_add]
  calc
    _ ≤ ∑' k : ℕ, conditionalWeight (k+(A-1)) := by
      apply Summable.tsum_le_tsum _ hEt hqt
      intro k
      have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2
        (cesaro_meanPulse_abs_le_one A (k+(A-1)+1) hA)
      simp only [sq_abs, one_pow] at hh
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hh (conditionalWeight_pos _).le
    _ = _ := by
      rw [conditionalWeight_tsum_tail, Nat.cast_sub (by omega : 1 ≤ A)]
      norm_num
      ring


theorem cesaro_meanRepair (F : ℕ → ℝ) (m : ℝ) (A t : ℕ) :
    cesaro (meanRepair F m A) t = cesaro F t - 2*m*cesaro (meanPulse A) t := by
  simp only [cesaro, meanRepair, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Exact square completion. The second complete square retains the mixed term. -/
theorem meanRepair_square_completion (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (m δ : ℝ) (hδ : δ ≠ 0)
    (A : ℕ) (hA : 0 < A) :
    conditionalMeanSquare (meanRepair F m A) +
      δ * conditionalMeanSquare (meanRepair F (-m/δ) A) =
      (1+δ)*conditionalMeanSquare F +
      ((1+1/δ)*4*m^2)*conditionalMeanSquare (meanPulse A) := by
  have hp : ∀ a ∈ Set.Ici (1 : ℕ), 0 < a := by intro a ha; exact ha
  have hsF := legal_conditionalMeanSquare_summable (Set.Ici 1) hp hF
  have hsH := legal_conditionalMeanSquare_summable (Set.Ici 1) hp (meanPulse_legal A hA)
  have hsR := legal_conditionalMeanSquare_summable (Set.Ici 1) hp
    (meanRepair_legal F hF m A hA)
  have hsS := legal_conditionalMeanSquare_summable (Set.Ici 1) hp
    (meanRepair_legal F hF (-m/δ) A hA)
  have he (k : ℕ) :
      conditionalWeight k * (cesaro (meanRepair F m A) (k+1))^2 +
      δ*(conditionalWeight k * (cesaro (meanRepair F (-m/δ) A) (k+1))^2) =
      (1+δ)*(conditionalWeight k * (cesaro F (k+1))^2) +
      ((1+1/δ)*4*m^2)*(conditionalWeight k * (cesaro (meanPulse A) (k+1))^2) := by
    rw [cesaro_meanRepair, cesaro_meanRepair]
    field_simp
    ring
  have hh : (∑' k : ℕ, (
      conditionalWeight k * (cesaro (meanRepair F m A) (k+1))^2 +
      δ*(conditionalWeight k * (cesaro (meanRepair F (-m/δ) A) (k+1))^2))) =
      ∑' k : ℕ, ((1+δ)*(conditionalWeight k * (cesaro F (k+1))^2) +
      ((1+1/δ)*4*m^2)*(conditionalWeight k * (cesaro (meanPulse A) (k+1))^2)) :=
    tsum_congr he
  rw [hsR.tsum_add (hsS.mul_left δ),
    (hsF.mul_left (1+δ)).tsum_add (hsH.mul_left ((1+1/δ)*4*m^2))] at hh
  simpa only [tsum_mul_left, conditionalMeanSquare] using hh

/-- Quantitative mean-repair control obtained from the exact square identity. -/
theorem meanRepair_energy_le (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (m δ : ℝ) (hδ : 0 < δ)
    (A : ℕ) (hA : 0 < A) :
    conditionalMeanSquare (meanRepair F m A) ≤
      (1+δ)*conditionalMeanSquare F +
      ((1+1/δ)*4*m^2)*(2/((A : ℝ)+1)) := by
  have he := meanRepair_square_completion F hF m δ (ne_of_gt hδ) A hA
  have hn := mul_nonneg hδ.le
    (conditionalMeanSquare_nonneg (meanRepair F (-m/δ) A))
  have hc : 0 ≤ (1+1/δ)*4*m^2 := by positivity
  have hb := mul_le_mul_of_nonneg_left (meanPulse_energy_le A hA) hc
  linarith

/-- Exact signed identity for the two correction directions in the handoff. -/
def tailCorrection (D : ℕ) (d : ℕ) (n : ℕ) : ℝ :=
  residueFraction d n + (1-2*(D : ℝ)/(d : ℝ))*residueFraction D n +
    (2*(D : ℝ)/(d : ℝ)-2)*residueFraction (2*D) n

theorem meanPulse_difference_tailCorrection (D A n : ℕ) (hA : 0 < A) :
    meanPulse A n - meanPulse D n =
      2*tailCorrection D (2*A) n - tailCorrection D A n := by
  have hAR : (A : ℝ) ≠ 0 := by positivity
  unfold meanPulse tailCorrection
  push_cast
  field_simp
  ring


/-- No bound on the original period mean is needed: delay cancellation sufficiently. -/
theorem meanRepair_arbitrarily_small_energy_cost (Y : ℕ) (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (m ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, Y < A ∧ conditionalMeanSquare (meanRepair F m A) <
      conditionalMeanSquare F + ε := by
  let E := conditionalMeanSquare F
  have hE : 0 ≤ E := conditionalMeanSquare_nonneg F
  let δ : ℝ := ε / (2*(E+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : δ*(E+1) = ε/2 := by
    dsimp [δ]
    have hE1 : E+1 ≠ 0 := by positivity
    field_simp
  let B : ℝ := (1+1/δ)*8*m^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨A,hA⟩ := exists_nat_gt (max (Y : ℝ) (2*B/ε))
  have hAY : Y < A := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left (Y : ℝ) (2*B/ε)) hA)
  have hA0 : 0 < A := by omega
  have hBA : 2*B/ε < (A : ℝ) :=
    lt_of_le_of_lt (le_max_right (Y : ℝ) (2*B/ε)) hA
  have hb : B/((A : ℝ)+1) < ε/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < (A : ℝ)+1)).2
    have hh := (div_lt_iff₀ hε).1 hBA
    nlinarith
  have hc := meanRepair_energy_le F hF m δ hδ A hA0
  have heq : ((1+1/δ)*4*m^2)*(2/((A : ℝ)+1)) = B/((A : ℝ)+1) := by
    dsimp [B]
    ring
  rw [heq] at hc
  refine ⟨A,hAY,?_⟩
  change conditionalMeanSquare (meanRepair F m A) < E+ε
  change conditionalMeanSquare (meanRepair F m A) ≤ (1+δ)*E+B/((A : ℝ)+1) at hc
  nlinarith

/-- A concrete periodic legal witness can be repaired at arbitrarily small energy cost. -/
theorem exists_zeroMean_head_near (Y : ℕ) (F : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n+Q)=F n) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : ℕ → ℝ, G ∈ conditionalHeadClass Y ∧
      (∃ P : ℕ, 0 < P ∧ (∀ n, G (n+P)=G n) ∧ periodMean G P=0) ∧
      conditionalMeanSquare G < conditionalMeanSquare F + ε := by
  obtain ⟨A,hAY,hE⟩ := meanRepair_arbitrarily_small_energy_cost Y F hF.1
    (periodMean F Q) ε hε
  have hA0 : 0 < A := by omega
  refine ⟨meanRepair F (periodMean F Q) A,
    meanRepair_mem_headClass Y F hF _ A hAY, ?_, hE⟩
  refine ⟨Q*(2*A), by positivity, ?_, ?_⟩
  · exact meanRepair_periodic F Q A hp (periodMean F Q)
  · exact meanRepair_zero_mean F Q A hQ (by omega) hp

end
end RiemannResearch.RH.CRTBlock
