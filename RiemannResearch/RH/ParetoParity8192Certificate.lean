import RiemannResearch.RH.ParetoParityNormBounds
import RiemannResearch.RH.ParetoParity8192Arithmetic
import RiemannResearch.RH.ParetoParity8192Sieve
import RiemannResearch.RH.ParetoRawTrialPeriodicTail

/-! # Conductor-8192 full Pareto enclosure from rounded integer head units

The supplied finite-limit certificate uses conductor 8192 and scale 10^9.
The CRT computation controls every physical site strictly beyond 2^30.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
open CoefficientStabilization

private theorem head_term_le (n : ℕ) (hn : 0 < n) :
    positiveWeight n * (RawTrialTail.error support (fun d => (coeff d : ℝ)) (10^9) n)^2 ≤
      (roundedUnit n : ℝ) := by
  have hreal : (residual n : ℝ) =
      RawTrialTail.error support (fun d => (coeff d : ℝ)) (10^9) n := by
    simp only [residual,RawTrialTail.error,residue,Int.cast_sub,Int.cast_pow,
      Int.cast_sum,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
  let den := n*(n+1)
  have hden : 0 < den := Nat.mul_pos hn (Nat.succ_pos n)
  have hq : (residual n).natAbs ^ 2 ≤ den * roundedUnit n := by
    have hz := Nat.lt_mul_div_succ ((residual n).natAbs^2+(den-1)) hden
    rw [Nat.mul_succ] at hz
    change (residual n).natAbs^2 ≤ den * (((residual n).natAbs^2+(den-1))/den)
    omega
  have habs : (((residual n).natAbs : ℕ) : ℝ) = |(residual n : ℝ)| := by
    have hi := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (residual n))
    simpa only [Int.cast_natCast,Int.cast_abs] using hi
  have hr : (((residual n).natAbs : ℝ))^2 ≤ (den:ℝ)*(roundedUnit n:ℝ) := by exact_mod_cast hq
  rw [habs,sq_abs] at hr
  rw [← hreal,positiveWeight,one_div,← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)*((n:ℝ)+1))).mpr
  simpa [den,mul_comm] using hr

private theorem cast_roundedHead (T : ℕ) :
    (roundedHead T : ℝ) = ∑ j ∈ Finset.range T, (roundedUnit (j+1) : ℝ) := by
  simp only [roundedHead,Nat.cast_sum]

/-- Only the finite integer head appears as an input. -/
theorem limitEnergy_le_of_roundedHead
    (hhead : roundedHead (2 ^ 30) ≤ 5067697348817286) : limitEnergy ≤ energyBudget := by
  let c := fun d => (coeff d : ℝ)
  have hH : (∑ j ∈ Finset.range (2 ^ 30), positiveWeight (j+1) *
      (RawTrialTail.error support c (10^9) (j+1))^2) ≤ (5067697348817286 : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (2 ^ 30), (roundedUnit (j+1) : ℝ) :=
        Finset.sum_le_sum fun j _ => head_term_le (j+1) (Nat.succ_pos _)
      _ = (roundedHead (2 ^ 30) : ℝ) := (cast_roundedHead _).symm
      _ ≤ _ := by exact_mod_cast hhead
  have hm : RawTrialTail.mean support c (10^9) = (112901299:ℝ)/2 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) twiceMean_value
    simp [twiceMean] at h
    unfold RawTrialTail.mean c
    linarith only [h]
  have ha : RawTrialTail.amplitude support c = 5074605440756600 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) oscillation_value
    simpa [oscillation,RawTrialTail.amplitude,c] using h
  have hg : RawTrialTail.gcdEnergy support c = 161141128064221680975 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) covariance_value
    simpa [covariance,RawTrialTail.gcdEnergy,c] using h
  have h := RawTrialTail.limitEnergy_le_of_head support c (10^9) _ (2 ^ 30) (by norm_num)
    (fun d hd => (Finset.mem_Icc.mp hd).1) hH
  unfold RawTrialTail.uniformSquare RawTrialTail.discrepancy at h
  rw [hm,ha,hg] at h
  convert h using 1 <;> norm_num [energyBudget]

theorem normalizedParityCapture_exact_lower_of_roundedHead
    (hhead : roundedHead (2 ^ 30) ≤ 5067697348817286) :
    Real.sqrt (1 / Real.log 2 - 1 / (1-energyBudget)) ≤ normalizedParityCapture :=
  sqrt_energy_lower_le_normalizedParityCapture (limitEnergy_le_of_roundedHead hhead)
    (by norm_num [energyBudget])

theorem normalizedParityCapture_enclosure_of_roundedHead
    (hhead : roundedHead (2 ^ 30) ≤ 5067697348817286) :
    (66151243224796 : ℝ)/10^14 < normalizedParityCapture ∧
      normalizedParityCapture ≤ Real.sqrt (1/Real.log 2-1) :=
  ⟨normalizedParityCapture_lower_of_budget (limitEnergy_le_of_roundedHead hhead),
    normalizedParityCapture_upper⟩

/-- The same conclusion in terms of the executable segmented sieve. -/
theorem normalizedParityCapture_enclosure_of_sievedBlocks
    (hblocks : (∑ b ∈ Finset.range 8192, sievedBlock ((2 ^ 17) * b) (2 ^ 17)) ≤
      5067697348817286) :
    (66151243224796 : ℝ)/10^14 < normalizedParityCapture ∧
      normalizedParityCapture ≤ Real.sqrt (1/Real.log 2-1) :=
  normalizedParityCapture_enclosure_of_roundedHead (roundedHead_eq_sievedBlocks.symm ▸ hblocks)

end RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
