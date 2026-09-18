import RiemannResearch.RH.CRTFirstPeriodEnergy
import RiemannResearch.RH.CRTLegalCoordinates
import RiemannResearch.RH.CRTMeanRepair
import RiemannResearch.RH.ParetoLegalStructure

/-!
# Legal constraints on the CRT defect chart
Source: this continuation's attempt to minimize independent CRT coordinates.
The cheap cutoff vector is a valid vector for the positive diagonal form,
but cannot be the defect vector of an actual legal mean-zero witness.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open Pareto ArithmeticCumulative
open RiemannResearch.Analysis.Cesaro

/-- The legal reflection identity holds at any actual period, not only
at a conductor chosen from a particular coefficient representation. -/
theorem legal_reflection_at_period
    (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hp : ∀ n, F (n+Q)=F n) (n : ℕ) (hn : n < Q) :
    F n + F (Q-1-n) = F (Q-1) := by
  obtain ⟨P,hP,hper⟩ := legalSeedSpan_hasLegalReflectionPeriod
    (Set.Ici 1) (by intro a ha; exact ha) hF
  have hmul : Q*(P-1)+Q=Q*P := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have hQle : Q ≤ Q*P := by omega
  have href := (hper (Q*P) (dvd_mul_left P Q)).2 n (by omega)
  have hleft : Q*P-1-n = (Q-1-n)+Q*(P-1) := by omega
  have hright : Q*P-1 = (Q-1)+Q*(P-1) := by omega
  rw [hleft,hright,periodic_multiple F Q hp (P-1),
    periodic_multiple F Q hp (P-1)] at href
  exact href

def cutoffDefect (Q Y : ℕ) (r : Fin Q) : ℝ :=
  if r.val+1 ≤ Y then ((r.val+1 : ℕ) : ℝ) else 0

/-- The unrestricted diagonal-coordinate problem has an inexpensive cutoff. -/
theorem cutoffDefect_core (Q Y : ℕ) (hYQ : Y ≤ Q) :
    firstPeriodCore Q (cutoffDefect Q Y) = (Y : ℝ)/((Y : ℝ)+2) := by
  have he : firstPeriodCore Q (cutoffDefect Q Y) =
      ∑ r : Fin Q, if r.val+1 ≤ Y then conditionalWeight r.val else 0 := by
    unfold firstPeriodCore cutoffDefect
    apply Finset.sum_congr rfl
    intro r _
    split_ifs with h
    · unfold mKernel conditionalWeight mixtureWeight
      push_cast
      have hr : (r.val : ℝ)+1 ≠ 0 := by positivity
      field_simp
    · simp
  rw [he]
  change (∑ r : Fin Q, (fun j : ℕ => if j+1 ≤ Y then conditionalWeight j else 0) r.val) = _
  rw [show (∑ r : Fin Q, (fun j : ℕ => if j+1 ≤ Y then conditionalWeight j else 0) r.val) =
    ∑ j ∈ Finset.range Q, if j+1 ≤ Y then conditionalWeight j else 0 by
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ => if j+1 ≤ Y then conditionalWeight j else 0) Q]
  calc
    _ = ∑ j ∈ Finset.range Y, conditionalWeight j := by
      symm
      calc
        _ = ∑ j ∈ Finset.range Y, if j+1 ≤ Y then conditionalWeight j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
        _ = ∑ j ∈ Finset.range Q, if j+1 ≤ Y then conditionalWeight j else 0 := by
          apply Finset.sum_subset (Finset.range_mono hYQ)
          intro j _ hj
          have hjY : ¬ j < Y := by simpa only [Finset.mem_range] using hj
          rw [if_neg (by omega : ¬ j+1 ≤ Y)]
    _ = _ := conditionalWeight_sum_range Y

theorem cutoffDefect_complete_energy_le (Q Y : ℕ) (hYQ : Y < Q) :
    (∑ r : Fin Q, progressionM Q (r.val+1)*(cutoffDefect Q Y r)^2) ≤
      (9/8 : ℝ)*((Y : ℝ)/((Y : ℝ)+2)) := by
  have h := (firstPeriodCore_enclosure Q (cutoffDefect Q Y) (by
    intro r hr
    simp [cutoffDefect,hr,show ¬ Q ≤ Y by omega])).2
  rwa [cutoffDefect_core Q Y hYQ.le] at h

/-- The tempting cheap coordinate vector is excluded by an exact legal
reflection identity. This is a mathematical obstruction, not a failed tactic. -/
theorem cutoffDefect_not_realizable
    (Y Q : ℕ) (hY : 0 < Y) (hQ : Y+4 ≤ Q)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hp : ∀ n, F (n+Q)=F n) (hm : periodMean F Q=0) :
    ¬ ∀ r : Fin Q, periodDefect F Q (r.val+1)=cutoffDefect Q Y r := by
  intro hb
  have hc (n : ℕ) (hn : 0 < n) (hnQ : n ≤ Q) :
      cumulative F n = if n ≤ Y then (n : ℝ) else 0 := by
    let r : Fin Q := ⟨n-1,by omega⟩
    have h := hb r
    change periodDefect F Q (n-1+1) =
      if n-1+1 ≤ Y then ((n-1+1 : ℕ) : ℝ) else 0 at h
    rw [show n-1+1=n by omega] at h
    simpa only [periodDefect,hm,mul_zero,sub_zero] using h
  have hfirst : F 1 = 1 := by
    have h := hc 1 (by omega) (by omega)
    simpa [cumulative,show 1 ≤ Y by omega] using h
  have hc3 : cumulative F (Q-3)=0 := by
    rw [hc (Q-3) (by omega) (by omega),if_neg (by omega)]
  have hc2 : cumulative F (Q-2)=0 := by
    rw [hc (Q-2) (by omega) (by omega),if_neg (by omega)]
  have hc1 : cumulative F (Q-1)=0 := by
    rw [hc (Q-1) (by omega) (by omega),if_neg (by omega)]
  have hs2 := cumulative_succ F (Q-3)
  rw [show Q-3+1=Q-2 by omega,hc2,hc3] at hs2
  have hlast2 : F (Q-2)=0 := by linarith
  have hs1 := cumulative_succ F (Q-2)
  rw [show Q-2+1=Q-1 by omega,hc1,hc2] at hs1
  have hlast1 : F (Q-1)=0 := by linarith
  have href := legal_reflection_at_period F Q (by omega) hF hp 1 (by omega)
  rw [show Q-1-1=Q-2 by omega,hfirst,hlast2,hlast1] at href
  norm_num at href


/-- Conditional CRT–Pareto endpoint with every coefficient feasibility
condition explicit. The subpolynomial cost hypothesis remains unproved. -/
theorem riemannHypothesis_of_subpolynomial_residue_coordinates
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (Y Q : ℕ → ℕ)
    (hYpos : ∀ j, 0 < Y j) (hQpos : ∀ j, 0 < Q j)
    (hY : Filter.Tendsto Y Filter.atTop Filter.atTop)
    (hs : ∀ j d, d ∈ s j → 2 ≤ d)
    (hdiv : ∀ j d, d ∈ s j → d ∣ Q j)
    (hrec : ∀ j, (∑ d ∈ s j, c j d / (d : ℝ)) = 1)
    (htotal : ∀ j, (∑ d ∈ s j, c j d) = 1)
    (hlow : ∀ j n, 1 < n → n ≤ Y j →
      (if n ∈ s j then c j n else 0) = -(ArithmeticFunction.moebius n : ℝ))
    (hcost : HasSubpolynomialEnergy Y
      (fun j => firstPeriodEnergy (normalizedResidueSynthesis (s j) (c j)) (Q j))) :
    RiemannHypothesis := by
  have hfeasible (j : ℕ) :=
    (normalizedResidueSynthesis_zeroMean_exact_head_iff
      (s j) (c j) (Y j) (Q j) (hYpos j) (hQpos j) (hs j) (hdiv j)).mpr
        ⟨hrec j, htotal j, hlow j⟩
  exact riemannHypothesis_of_subpolynomial_firstPeriod
    (fun j => normalizedResidueSynthesis (s j) (c j)) Q Y
    (fun j => ⟨normalizedResidueSynthesis_legal (s j) (c j) (hs j),
      (hfeasible j).1⟩)
    hY hQpos
    (fun j => normalizedResidueSynthesis_periodic (s j) (c j) (Q j) (hdiv j))
    (fun j => (hfeasible j).2) hcost

end RiemannResearch.RH.CRTBlock
