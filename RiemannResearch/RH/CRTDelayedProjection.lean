import RiemannResearch.RH.ConditionalMeanSignedProjection
import RiemannResearch.RH.CRTMeanZeroInfimum

/-!
# Delayed signed projection and dyadic/triadic corrections
Source: user-provided Exact CRT Energy Mean Repair handoff (2026-09-18),
Appendix 9. The arbitrary-epsilon projection gain below strengthens the
finite-fraction formulation by reusing the verified delayed mean repair.
All energies and correlations are the actual infinite conditional energies.
-/
open Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.ArithmeticCumulative.CesaroResidue
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.Cesaro

theorem meanPulse_energy_pos (A : ℕ) (hA : 0 < A) :
    0 < conditionalMeanSquare (meanPulse A) := by
  have hs := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) (meanPulse_legal A hA)
  apply hs.tsum_pos
    (fun k => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _)) (2*A-1)
  rw [show 2*A-1+1 = 1*(2*A) by omega,
    cesaro_meanPulse_complete_periods A 1 hA (by omega)]
  exact mul_pos (conditionalWeight_pos _) (by norm_num)

theorem periodMean_add_mul (F G : ℕ → ℝ) (u : ℝ) (Q : ℕ) :
    periodMean (fun n => F n+u*G n) Q = periodMean F Q+u*periodMean G Q := by
  unfold periodMean cumulative
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Any head-vanishing legal direction can deliver its complete scalar gain
to the mean-zero class, to arbitrarily small positive error. -/
theorem exists_zeroMean_signed_projection_near (Y : ℕ) (F G : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y)
    (hG : G ∈ legalSeedSpan (Set.Ici 1))
    (hzero : ∀ n, 0 < n → n ≤ Y → G n = 0)
    (hg : conditionalMeanSquare G ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ K ∈ zeroMeanHeadClass Y, conditionalMeanSquare K <
      conditionalMeanSquare F-(conditionalMeanInner F G)^2/conditionalMeanSquare G+ε := by
  obtain ⟨K,hK,hcost⟩ := exists_zeroMeanHead_near Y
    (fun n => F n+(-conditionalMeanInner F G/conditionalMeanSquare G)*G n)
    (add_mul_mem_conditionalHeadClass Y F G hF hG hzero _) ε hε
  rw [conditionalMeanSquare_optimal_scalar F G hF.1 hG hg] at hcost
  exact ⟨K,hK,hcost⟩

/-- The delay and coefficient are explicit in the witness: only the delay is
chosen. The entire correction lies in two actual tail-dictionary directions. -/
theorem exists_delayed_pulse_projection (Y D : ℕ) (hYD : Y < D)
    (F : ℕ → ℝ) (hF : F ∈ zeroMeanHeadClass Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, D < A ∧
      (fun n => F n+
        (conditionalMeanInner F (meanPulse D)/conditionalMeanSquare (meanPulse D))*
          (meanPulse A n-meanPulse D n)) ∈ zeroMeanHeadClass Y ∧
      conditionalMeanSquare (fun n => F n+
        (conditionalMeanInner F (meanPulse D)/conditionalMeanSquare (meanPulse D))*
          (meanPulse A n-meanPulse D n)) <
        conditionalMeanSquare F-
          (conditionalMeanInner F (meanPulse D))^2/conditionalMeanSquare (meanPulse D)+ε := by
  have hD : 0 < D := by omega
  let u : ℝ := -conditionalMeanInner F (meanPulse D)/conditionalMeanSquare (meanPulse D)
  let K : ℕ → ℝ := fun n => F n+u*meanPulse D n
  have hK : K ∈ conditionalHeadClass Y :=
    add_mul_mem_conditionalHeadClass Y F (meanPulse D) hF.1
      (meanPulse_legal D hD)
      (fun n _ hn => meanPulse_zero_before D n (by omega)) u
  obtain ⟨Q,hQ,hper,hm⟩ := hF.2
  let P := Q*(2*D)
  have hP : 0 < P := by dsimp [P]; positivity
  have hKper (n : ℕ) : K (n+P) = K n := by
    dsimp [K, P]
    rw [periodic_multiple F Q hper (2*D) n,
      show Q*(2*D) = (2*D)*Q by ring,
      periodic_multiple (meanPulse D) (2*D) (meanPulse_periodic D) Q n]
  have hKm : periodMean K P = u/2 := by
    rw [show K = (fun n => F n+u*meanPulse D n) from rfl, periodMean_add_mul]
    have hFP : periodMean F P = 0 := by
      rw [show P = Q*(2*D) from rfl, periodMean_multiple F Q (2*D) hQ (by omega) hper, hm]
    have hHP : periodMean (meanPulse D) P = 1/2 := by
      rw [show P = (2*D)*Q by dsimp [P]; ring,
        periodMean_multiple (meanPulse D) (2*D) Q (by omega) hQ (meanPulse_periodic D),
        meanPulse_periodMean D hD]
    rw [hFP,hHP]
    ring
  obtain ⟨A,hAD,hcost⟩ := meanRepair_arbitrarily_small_energy_cost D K hK.1 (u/2) ε hε
  have hA : 0 < A := by omega
  have heq : meanRepair K (u/2) A =
      (fun n => F n+
        (conditionalMeanInner F (meanPulse D)/conditionalMeanSquare (meanPulse D))*
          (meanPulse A n-meanPulse D n)) := by
    ext n
    dsimp [meanRepair,K,u]
    ring
  have hclass : meanRepair K (u/2) A ∈ zeroMeanHeadClass Y := by
    refine ⟨meanRepair_mem_headClass Y K hK _ A (by omega),
      P*(2*A),by positivity,meanRepair_periodic K P A hKper (u/2),?_⟩
    rw [← hKm]
    exact meanRepair_zero_mean K P A hP hA hKper
  have hopt : conditionalMeanSquare K =
      conditionalMeanSquare F-
        (conditionalMeanInner F (meanPulse D))^2/conditionalMeanSquare (meanPulse D) :=
    conditionalMeanSquare_optimal_scalar F (meanPulse D) hF.1.1
      (meanPulse_legal D hD) (ne_of_gt (meanPulse_energy_pos D hD))
  rw [heq] at hclass hcost
  rw [hopt] at hcost
  exact ⟨A,hAD,hclass,hcost⟩

/-- A triadic pulse has mean one and escapes artificial dyadic resonances. -/
def ternaryPulse (A n : ℕ) : ℝ :=
  3*residueFraction (3*A) n-residueFraction A n

theorem ternaryPulse_legal (A : ℕ) (hA : 0 < A) :
    ternaryPulse A ∈ legalSeedSpan (Set.Ici 1) := by
  have h1 : residueFraction A ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [allPositiveSeeds, Set.Ici, Nat.lt_iff_add_one_le, Nat.zero_add]
      using residueFraction_mem_legal A hA
  have h3 : residueFraction (3*A) ∈ legalSeedSpan (Set.Ici 1) := by
    simpa only [allPositiveSeeds, Set.Ici, Nat.lt_iff_add_one_le, Nat.zero_add]
      using residueFraction_mem_legal (3*A) (by omega)
  convert (legalSeedSpan (Set.Ici 1)).sub_mem
    ((legalSeedSpan (Set.Ici 1)).smul_mem (3 : ℝ) h3) h1 using 1
  ext n
  simp [ternaryPulse,smul_eq_mul]

theorem ternaryPulse_zero_before (A n : ℕ) (hn : n < A) :
    ternaryPulse A n = 0 := by
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  unfold ternaryPulse residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < 3*A), Nat.mod_eq_of_lt hn]
  push_cast
  field_simp
  ring

/-- Exact triadic repair inside the handoff's complete correction dictionary. -/
theorem ternaryPulse_tailCorrection (D A n : ℕ) (hA : 0 < A) :
    ternaryPulse A n-2*meanPulse D n =
      3*tailCorrection D (3*A) n-tailCorrection D A n := by
  have hAR : (A : ℝ) ≠ 0 := by positivity
  unfold ternaryPulse meanPulse tailCorrection
  push_cast
  field_simp
  ring

/-- Compatibility of the dyadic and triadic routes is an exact finite identity. -/
theorem dyadic_triadic_pulse_compatibility (A n : ℕ) :
    2*ternaryPulse (2*A) n-ternaryPulse A n =
      3*meanPulse (3*A) n-meanPulse A n := by
  unfold ternaryPulse meanPulse
  rw [show 3*(2*A) = 2*(3*A) by ring]
  ring

end RiemannResearch.RH.CRTBlock
