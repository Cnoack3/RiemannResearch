import RiemannResearch.RH.QRamanujanDPPLaw
import RiemannResearch.Probability.DeterminantalWeightedMoments

/-!
# Actual Q signed weighted sampling statistics

Source: sixth transfer program, 24 October 2026. Every formula is for the
constructed complete-Q law; limiting moments retain all signed cross terms.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open RiemannResearch.Probability.DPP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weighted_covariance (n : ℕ) (e : ι ↪ ℕ) (a b : ι → ℝ) :
    (∫ x, linearStatistic (fun x => {i | x i = true}) e a x *
      linearStatistic (fun x => {i | x i = true}) e b x ∂law n) -
      (∫ x, linearStatistic (fun x => {i | x i = true}) e a x ∂law n) *
      (∫ x, linearStatistic (fun x => {i | x i = true}) e b x ∂law n) =
      (∑ i, a i * b i * kernel n (e i) (e i)) -
        ∑ i, ∑ j, a i * b j * (kernel n (e i) (e j)) ^ 2 := by
  rw [(law_isDPP n).linearStatistic_covariance e a b]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← kernel_symmetric n (e i) (e j)]
  ring

theorem weighted_variance (n : ℕ) (e : ι ↪ ℕ) (a : ι → ℝ) :
    ProbabilityTheory.variance (linearStatistic (fun x => {i | x i = true}) e a) (law n) =
      (∑ i, (a i) ^ 2 * kernel n (e i) (e i)) -
        ∑ i, ∑ j, a i * a j * (kernel n (e i) (e j)) ^ 2 := by
  rw [(law_isDPP n).variance_linearStatistic e a]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← kernel_symmetric n (e i) (e j)]
  ring

theorem weighted_variance_tendsto (e : ι ↪ ℕ) (a : ι → ℝ) :
    Tendsto (fun n => ProbabilityTheory.variance
      (linearStatistic (fun x => {i | x i = true}) e a) (law n)) atTop
      (𝓝 (ProbabilityTheory.variance
        (linearStatistic (fun x => {i | x i = true}) e a) limitLaw)) := by
  simp only [(law_isDPP _).variance_linearStatistic e a,
    limitLaw_isDPP.variance_linearStatistic e a]
  apply Tendsto.sub
  · exact tendsto_finset_sum _ (fun i _ => (kernel_tendsto (e i) (e i)).const_mul _)
  · apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact ((kernel_tendsto (e i) (e j)).const_mul _).mul (kernel_tendsto (e j) (e i))

end RiemannResearch.RH.QRamanujanDPP
