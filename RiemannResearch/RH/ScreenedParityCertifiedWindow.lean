import RiemannResearch.RH.ParetoGroupedResidueMass
import RiemannResearch.RH.ScreenedParityPhysicalBounds

/-! # An explicit quadratic window of the limiting screened packet

The complete conductor-241 norm certificate controls the limiting Hilbert
vector at the physical sites. This gives a finite quadratic-window example
for the excursion criterion in the user's Pareto handoff.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- At depth eight the actual limiting packet has at most seven negative
excursions on the integer window from sixteen to its square. -/
theorem screenedTwo_negative_count_sixteen :
    ((Finset.Icc 16 256).filter (fun n => hilbertSequence normalizedScreenedTwo n < -8)).card ≤ 7 := by
  classical
  let S := (Finset.Icc 16 256).filter (fun n => hilbertSequence normalizedScreenedTwo n < -8)
  let z := hilbertOne - normalizedScreenedTwo
  have hcost (n : ℕ) (hn : n ∈ S) :
      (81 : ℝ)/(256*257) ≤ positiveWeight n * (hilbertSequence z n)^2 := by
    obtain ⟨hwin, hu⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hwin
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hn256 : (n : ℝ) ≤ 256 := by exact_mod_cast hnhi
    have hden : (n : ℝ)*((n : ℝ)+1) ≤ 256*257 :=
      mul_le_mul hn256 (by linarith) (by linarith) (by norm_num)
    have hw : (1:ℝ)/(256*257) ≤ positiveWeight n := by
      change (1:ℝ)/(256*257) ≤ 1/((n:ℝ)*((n:ℝ)+1))
      exact one_div_le_one_div_of_le (by positivity) hden
    have hseq : hilbertSequence z n = 1 - hilbertSequence normalizedScreenedTwo n := by
      simp only [z, hilbertSequence_sub, Pi.sub_apply, hilbertOne_sequence, zeroAnchor, if_neg hn0.ne']
    have h9 : 9 ≤ hilbertSequence z n := by rw [hseq]; linarith
    have hs : (81:ℝ) ≤ (hilbertSequence z n)^2 := by
      simpa only [show (9:ℝ)^2 = 81 by norm_num] using
        (sq_le_sq₀ (by norm_num : 0 ≤ (9:ℝ)) (by linarith : 0 ≤ hilbertSequence z n)).mpr h9
    calc
      _ = (1:ℝ)/(256*257)*81 := by norm_num
      _ ≤ _ := mul_le_mul hw hs (by norm_num) (positiveWeight_nonneg _)
  have htotal : (S.card:ℝ)*(81/(256*257)) ≤ ‖z‖^2 := by
    calc
      _ = ∑ _n ∈ S, (81:ℝ)/(256*257) := by simp
      _ ≤ ∑ n ∈ S, positiveWeight n * (hilbertSequence z n)^2 := Finset.sum_le_sum hcost
      _ ≤ _ := by
        rw [hilbert_norm_weighted_sq]
        exact (hilbertSequence_square_summable z).sum_le_tsum S
          (fun n _ => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  have hcert : ‖z‖^2 ≤ (628101568132839 : ℝ)/64908898431867161 :=
    RiemannResearch.RH.GroupedResidueMass.Conductor241.screenedTwo_squared_distance_le_mod30
  change S.card ≤ 7
  by_contra h
  have h8 : (8 : ℝ) ≤ S.card := by exact_mod_cast (show 8 ≤ S.card by omega)
  linarith

end RiemannResearch.RH.Pareto.PrimePowerSchur
