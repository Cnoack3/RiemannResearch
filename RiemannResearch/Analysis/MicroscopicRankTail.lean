import RiemannResearch.Analysis.MicroscopicRankCover
import RiemannResearch.Analysis.ZeroDPPRankVacancy

/-! The rank bound with the same moment normalization as the DPP vacancy bound. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MicroscopicRankCover
open ActualZeroOrdinate ActualZeroWindowVariance ZeroDPPRankVacancy

theorem eventually_rankTail_le_truncated {q : ℝ} (hq : 0 < q) :
    ∀ᶠ T : ℝ in atTop, ∀ J : ℕ,
      actualRankTail T q J ≤ truncatedWindowSecondMoment T (2*q) J / q := by
  filter_upwards [eventually_actual_cover hq] with T hc
  intro J
  let H := 2*q / (Real.log T / (2*Real.pi))
  have hi : Integrable (fun t => crowdedSquare J (actualWindowCount T H t)) :=
    truncatedSquare_integrable (copyOrdinate T) T H J
  have hb := hc J _ hi (fun t => le_rfl)
  calc
    actualRankTail T q J ≤ _ := hb
    _ = truncatedWindowSecondMoment T (2*q) J / q := by
      unfold truncatedWindowSecondMoment
      dsimp only [H, crowdedSquare]
      ring

/-- A height-uniform exponential count-square tail yields an exponential rank
bound for every rank at once, retaining coincident occurrence pairs. -/
theorem eventually_rankTail_le_exp {q : ℝ} (hq : 0 < q)
    (he : ExpTranslatedSquareTail (2 * q)) :
    ∃ A c : ℝ, 0 ≤ A ∧ 0 < c ∧ ∀ᶠ T : ℝ in atTop, ∀ J : ℕ,
      actualRankTail T q J ≤ A * Real.exp (-(c * (J : ℝ))) := by
  obtain ⟨A,c,hA,hc,he⟩ := he
  refine ⟨A/q,c,div_nonneg hA hq.le,hc,?_⟩
  filter_upwards [he, eventually_rankTail_le_truncated hq] with T hT hR
  intro J
  calc
    actualRankTail T q J ≤ _ := hR J
    _ ≤ (A * Real.exp (-c * (J:ℝ))) / q :=
      div_le_div_of_nonneg_right (hT J) hq.le
    _ = _ := by rw [neg_mul]; ring

end RiemannResearch.Analysis.MicroscopicRankCover
