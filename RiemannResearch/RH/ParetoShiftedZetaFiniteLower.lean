import RiemannResearch.RH.ParetoShiftedZetaSimpleWindow

noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint)

private theorem simple_window_mass_atTop (S : Finset ℝ) :
    Tendsto (fun L : ℝ => ∑ a ∈ S, 2*Real.arctan L/(1/4+a^2)) atTop
      (𝓝 (∑ a ∈ S, Real.pi/(1/4+a^2))) := by
  apply tendsto_finsetSum
  intro a _
  have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul 2).div_const (1/4+a^2)
  convert h using 2 <;> ring

/-- A finite set of distinct simple critical ordinates contributes the
sum of its Cauchy masses to the lower damping coefficient. -/
theorem global_shifted_budget_lower_at_simple_zeros (S : Finset ℝ)
    (hm : ∀ a ∈ S, Zeta23.zeroMult (criticalPoint a) = 1)
    (hi : ∀ᶠ ε in 𝓝[>] (0:ℝ), Integrable (fun t => boundarySquare
      (fun v => 1-shiftedZetaQuotient ε v) t))
    {b : ℝ} (hb : b < ∑ a ∈ S, Real.pi/(1/4+a^2)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), b*ε <
      ∫ t, boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t := by
  classical
  obtain ⟨L,hL,hbL⟩ := ((eventually_ge_atTop (0:ℝ)).and
    ((simple_window_mass_atTop S).eventually (lt_mem_nhds hb))).exists
  let w (ε t : ℝ) := boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t
  let I (ε a : ℝ) := Ioc (a-ε*L) (a+ε*L)
  have hsum := (tendsto_finsetSum S (fun a ha => simple_zero_scaled_window a L hL (hm a ha))).eventually (lt_mem_nhds hbL)
  have hd : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ a ∈ S, ∀ d ∈ S, a ≠ d → Disjoint (I ε a) (I ε d) := by
    apply (Filter.eventually_all_finset S).mpr
    intro a _
    apply (Filter.eventually_all_finset S).mpr
    intro d _
    by_cases e : a = d
    · exact Eventually.of_forall fun _ h => (h e).elim
    have hcont : Continuous (fun ε : ℝ => 2*ε*L) := by fun_prop
    have hlt : ∀ᶠ ε in 𝓝[>] (0:ℝ), 2*ε*L < |a-d| := by
      exact ((hcont.tendsto 0).eventually (gt_mem_nhds (by
        simpa only [mul_zero, zero_mul] using abs_pos.mpr (sub_ne_zero.mpr e)))).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlt] with ε he _
    rcases lt_or_gt_of_ne e with h | h
    · rw [abs_of_neg (sub_neg.mpr h)] at he
      exact Ioc_disjoint_Ioc_of_le (by linarith : a+ε*L ≤ d-ε*L)
    · rw [abs_of_pos (sub_pos.mpr h)] at he
      exact (Ioc_disjoint_Ioc_of_le (by linarith : d+ε*L ≤ a-ε*L)).symm
  filter_upwards [hi,hsum,hd,(self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε)] with ε hi hsum hd he
  change 0 < ε at he
  have hab a : a-ε*L ≤ a+ε*L := by linarith [mul_nonneg he.le hL]
  change b < ∑ a ∈ S, (∫ t in a-ε*L..a+ε*L, w ε t)/ε at hsum
  simp_rw [intervalIntegral.integral_of_le (hab _)] at hsum
  rw [← Finset.sum_div] at hsum
  apply ((lt_div_iff₀ he).mp hsum).trans_le
  let W (a : ℝ) := (I ε a).indicator (w ε)
  have hw (a : ℝ) : Integrable (W a) := hi.indicator measurableSet_Ioc
  change (∑ a ∈ S, ∫ t in I ε a, w ε t) ≤ ∫ t, w ε t
  calc
    _ = ∑ a ∈ S, ∫ t, W a t := by
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_indicator measurableSet_Ioc).symm
    _ = ∫ t, ∑ a ∈ S, W a t := (integral_finsetSum S (fun a _ => hw a)).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum S fun a _ => hw a) hi
      intro t
      change (∑ a ∈ S, W a t) ≤ w ε t
      by_cases hx : ∃ a ∈ S, t ∈ I ε a
      · obtain ⟨a,ha,hat⟩ := hx
        rw [Finset.sum_eq_single a]
        · simp [W,hat]
        · intro d hh de
          have hnot : t ∉ I ε d := fun ht => Set.disjoint_left.mp (hd a ha d hh de.symm) hat ht
          simp [W,hnot]
        · simp [ha]
      · have hall : ∀ a ∈ S, t ∉ I ε a := fun a ha ht => hx ⟨a,ha,ht⟩
        rw [Finset.sum_eq_zero (fun a ha => by simp [W,hall a ha])]
        dsimp [w,boundarySquare]
        positivity

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.global_shifted_budget_lower_at_simple_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms global_shifted_budget_lower_at_simple_zeros

end RiemannResearch.RH.Pareto.ResidueMellin
