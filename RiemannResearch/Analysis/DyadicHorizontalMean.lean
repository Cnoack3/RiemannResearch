/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualOneSidedHorizontalDisplacement

/-!
# From a dyadic right-displacement cap to the cumulative first moment

The dyadic window is (T,2T] with all analytic multiplicities. A recent
manuscript reports a bound of 0.32133 for the dyadic mass multiplied by
2π/T. An explicit proposition records exactly that source input. Geometric
iteration recovers the same coefficient for the cumulative mean.

<https://rstation.ai/problems/riemann_hypothesis/papers/182>
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Upper asymptotic value with the epsilon quantifier at real heights. -/
def MeanUpper (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, f T ≤ c+ε

/-- Iterating at half-height preserves a linear-in-height dyadic coefficient. -/
theorem meanUpper_of_dyadic {f : ℝ → ℝ} {b : ℝ}
    (hbounded : ∃ A : ℝ, ∀ᶠ T : ℝ in atTop, f T ≤ A)
    (hdyadic : MeanUpper (fun T => 2*f (2*T)-f T) b) : MeanUpper f b := by
  obtain ⟨A, hA⟩ := hbounded
  intro ε hε
  let c := b+ε/2
  have hstep := hdyadic (ε/2) (by positivity)
  have hhalf := tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)
  have hit (n : ℕ) : ∀ᶠ T : ℝ in atTop, f T ≤ c+(A-c)*(1/2:ℝ)^n := by
    induction n with
    | zero => simpa using hA
    | succ n ih =>
      filter_upwards [hhalf.eventually ih,hhalf.eventually hstep] with T hp ht
      change f (T/2) ≤ _ at hp
      change 2*f (2*(T/2))-f (T/2) ≤ c at ht
      rw [show 2*(T/2)=T by ring] at ht
      rw [pow_succ]
      linarith only [hp,ht]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)
  have hlimit : Tendsto (fun n : ℕ => c+(A-c)*(1/2:ℝ)^n) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (hpow.const_mul (A-c))
  obtain ⟨n,hn⟩ := (hlimit.eventually_lt_const (show c < b+ε by dsimp [c]; linarith)).exists
  filter_upwards [hit n] with T hT
  exact hT.trans hn.le

/-- Any positive global Selberg slope bounds the cumulative right mean,
which supplies the initial value for geometric iteration. -/
theorem oneSidedHeightMean_eventually_bounded {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) : ∃ A : ℝ, ∀ᶠ T : ℝ in atTop, oneSidedHeightMean T ≤ A := by
  obtain ⟨K,hK,hb⟩ := exists_selberg_displacementMoment_bound ha hD
  have hR := tendsto_count_div_mainTerm
  refine ⟨((K/a)*2)/(4*Real.pi),?_⟩
  filter_upwards [hb,hR.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ)<1)),
    hR.eventually_lt_const (by norm_num : (1:ℝ) < 2),eventually_gt_atTop (1:ℝ)] with T hB hpos hr hT
  change 0 < (Ncount 0 T : ℝ) / _ at hpos
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by intro hz; simp [hz] at hpos
  have hX : displacementMoment T 1 * Real.log T ≤ K/a :=
    (le_div_iff₀ ha).mpr (by simpa [mul_left_comm,mul_comm,mul_assoc] using hB 0)
  apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
  rw [mul_comm (oneSidedHeightMean T), ← firstMark_mul_countRatio_eq hT hN]
  exact mul_le_mul hX hr.le hpos.le (div_nonneg hK ha.le)

def rightDisplacementMass (T : ℝ) : ℝ :=
  realSum T (fun z => max (z.re-1/2) 0)

theorem dyadicMean_eq_mass {T : ℝ} (hT : 0 < T) :
    2*oneSidedHeightMean (2*T)-oneSidedHeightMean T =
      (rightDisplacementMass (2*T)-rightDisplacementMass T)/T := by
  unfold oneSidedHeightMean rightDisplacementMass
  field_simp [hT.ne']
  <;> ring

/-- The recent manuscript's reported dyadic input. Its normalization differs
from the cumulative mark by a factor of 2π. -/
def ManuscriptDyadicRightCap : Prop :=
  MeanUpper (fun T => (2*Real.pi) * ((rightDisplacementMass (2*T)-rightDisplacementMass T)/T))
    (32133/100000)

theorem cumulative_right_mean_of_manuscript {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) (hm : ManuscriptDyadicRightCap) :
    MeanUpper oneSidedHeightMean ((32133/100000)/(2*Real.pi)) := by
  apply meanUpper_of_dyadic (oneSidedHeightMean_eventually_bounded ha hD)
  intro ε hε
  have hp : 0 < 2*Real.pi := by positivity
  filter_upwards [hm ((2*Real.pi)*ε) (mul_pos hp hε), eventually_gt_atTop (0:ℝ)] with T h ht
  rw [dyadicMean_eq_mass ht]
  have hn := (le_div_iff₀ hp).mpr (show ((rightDisplacementMass (2*T)-rightDisplacementMass T)/T)*
      (2*Real.pi) ≤ (32133/100000)+(2*Real.pi)*ε by simpa only [mul_comm] using h)
  exact hn.trans_eq (by field_simp [hp.ne'] <;> ring)

end RiemannResearch.Analysis.ActualZeroOrdinate
