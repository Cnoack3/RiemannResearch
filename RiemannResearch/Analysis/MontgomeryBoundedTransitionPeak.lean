import RiemannResearch.Analysis.MontgomeryRawSecondOrderTransition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The raw transition using the published broad complex estimate

At the transition the positive-cutoff BGSTB estimate (3.5) suffices for
the uniform O(1/√log T) first-order formula. The horizontal gap is
little-oh of 1/log T under the independent squared-defect certificate.
Source: https://arxiv.org/html/2501.14545v3#S3.E5 . -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

def SharpTransitionFirstOrder : Prop :=
  ∀ A : ℝ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    |sharpFormFactor T (transitionFrequency c T)-Real.exp (-c)| ≤ H/Real.sqrt (Real.log T)

def BoundedSharpTransitionPeak : Prop :=
  ∀ A : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    Real.sqrt (sharpFormFactor T (transitionFrequency c T)) ≤ M

theorem sharpTransitionFirstOrder_of_corrected (hMT : CorrectedComplexFormFactorEstimate) :
    SharpTransitionFirstOrder := by
  obtain ⟨C,hC,hb⟩ := hMT
  intro A
  let H := C*(Real.exp A+1)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H+1,by linarith,?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 0 A),
    (loglog_pow_div_log_tendsto_zero 2).eventually_le_const zero_lt_one]
    with T hb hT hL1 hlb hl2
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let u := (ℓ+c)/2
  let r := 1/Real.sqrt L
  have hL : 0 < L := Real.log_pos hT
  change max 0 A ≤ ℓ at hlb
  change ℓ^2/L ≤ 1 at hl2
  have hlA := (le_max_right 0 A).trans hlb
  have hl0 := (le_max_left 0 A).trans hlb
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [(abs_le.mp hc).1]
  have hul : u ≤ ℓ := by dsimp [u]; linarith [(abs_le.mp hc).2]
  have hlSq : ℓ^2 ≤ L := by simpa using (div_le_iff₀ hL).mp hl2
  have hlroot : ℓ ≤ Real.sqrt L := (sq_le_sq₀ hl0 (Real.sqrt_nonneg _)).mp
    (by simpa only [Real.sq_sqrt hL.le] using hlSq)
  have hroot := Real.sqrt_pos.mpr hL
  have hroot1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  have hr1 : r ≤ 1 := (div_le_iff₀ hroot).2 (by simpa using hroot1)
  have ha0 : 0 ≤ α := div_nonneg hu0 hL.le
  have ha : α ≤ r := by
    change u/L ≤ 1/Real.sqrt L
    rw [div_le_div_iff₀ hL hroot]
    calc
      _ ≤ Real.sqrt L*Real.sqrt L := mul_le_mul_of_nonneg_right (hul.trans hlroot) hroot.le
      _ = 1*L := by rw [← sq, Real.sq_sqrt hL.le, one_mul]
  have hsp : Real.exp (-c) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hc).1])
  have hh := hb α ⟨ha0,ha.trans hr1⟩
  dsimp only at hh
  rw [transition_spike c T hT] at hh
  have hadd : Real.exp (-c)+1 ≤ Real.exp A+1 := by linarith
  have he : |sharpFormFactor T α-(Real.exp (-c)+α)| ≤ H*r := by
    apply hh.trans
    calc
      _ ≤ C*(Real.exp A+1)/Real.sqrt L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hadd hC) hroot.le
      _ = H*r := by dsimp only [H,r]; ring
  have hα : |(Real.exp (-c)+α)-Real.exp (-c)| ≤ r := by
    simpa only [add_sub_cancel_left,abs_of_nonneg ha0] using ha
  exact (abs_sub_le _ _ _).trans ((add_le_add he hα).trans_eq
    (show H*r+r=(H+1)/Real.sqrt L by dsimp only [r]; ring))

theorem boundedSharpTransitionPeak_of_first_order (hfirst : SharpTransitionFirstOrder) :
    BoundedSharpTransitionPeak := by
  intro A
  obtain ⟨H,hH,hh⟩ := hfirst A
  refine ⟨Real.sqrt (Real.exp A+H),Real.sqrt_nonneg _,?_⟩
  filter_upwards [hh,Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ht hL
  intro c hc
  have hr : 1 ≤ Real.sqrt (Real.log T) := by simpa using Real.sqrt_le_sqrt hL
  have hp : 0 < Real.sqrt (Real.log T) := zero_lt_one.trans_le hr
  have he : H/Real.sqrt (Real.log T) ≤ H := (div_le_iff₀ hp).mpr (le_mul_of_one_le_right hH hr)
  have hsp := Real.exp_le_exp.mpr (show -c ≤ A by linarith [(abs_le.mp hc).1])
  apply Real.sqrt_le_sqrt
  linarith only [(abs_le.mp (ht c hc)).2,hsp,he]

/-- Conversion uses uniform boundedness of the square root of the
complex statistic. No narrow second-order expansion is required here. -/
theorem rawSharpTransitionScaledGap_of_defect_boundedPeak (hdef : TransitionScaledDefect)
    (hpeak : BoundedSharpTransitionPeak) : RawSharpTransitionScaledGap := by
  intro A ε hε
  obtain ⟨M,hM,hm⟩ := hpeak A
  let η := min 1 (ε/(1+2*M))
  have hden : 0 < 1+2*M := by linarith
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : (1+2*M)*η ≤ ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hden).mp (min_le_right _ _)
  filter_upwards [hm,hdef A (η^2) (by positivity),eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hpeak hq hT hL1
  intro c hc
  let L := Real.log T
  let α := transitionFrequency c T
  let r := η/L
  have hL : 0 < L := Real.log_pos hT
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := (div_le_iff₀ hL).2 (by simpa using hη1.trans hL1)
  have hbound : horizontalDefect T α ≤ r^2 := by simpa only [r,div_pow] using hq c hc
  have hdiff : |Real.sqrt (formFactor T α)-Real.sqrt (sharpFormFactor T α)| ≤ Real.sqrt (r^2) := by
    rw [abs_sub_comm]
    exact (sqrt_horizontal_error T α).trans (Real.sqrt_le_sqrt hbound)
  have hpair := WeightedSqrtTransfer.abs_sub_le_of_sqrt (formFactor_nonneg hT α)
    (MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α) (sq_nonneg r) hdiff
  rw [Real.sqrt_sq hr] at hpair
  have hr2 : r^2 ≤ r := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)]
  apply hpair.trans
  calc
    _ ≤ r+(2*M)*r := add_le_add hr2 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpeak c hc) (by norm_num)) hr)
    _ = ((1+2*M)*η)/L := by dsimp only [r]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hηε hL.le

theorem rawSharpTransitionScaledGap_of_corrected_scaled_defect (hdef : TransitionScaledDefect)
    (hMT : CorrectedComplexFormFactorEstimate) : RawSharpTransitionScaledGap :=
  rawSharpTransitionScaledGap_of_defect_boundedPeak hdef
    (boundedSharpTransitionPeak_of_first_order (sharpTransitionFirstOrder_of_corrected hMT))

/-- The raw bounded-shift leading term from the published broad BGSTB
estimate alone on the analytic side. -/
theorem raw_transition_uniform_rate_of_bgstb_scaled_defect (hdef : TransitionScaledDefect)
    (hBG : BGSTBPositiveCutoffEstimate) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T)-Real.exp (-c)| ≤ K/Real.sqrt (Real.log T) := by
  have hMT := correctedComplexFormFactorEstimate_of_bgstb hBG
  obtain ⟨H,hH,hh⟩ := sharpTransitionFirstOrder_of_corrected hMT A
  have hg := rawSharpTransitionScaledGap_of_corrected_scaled_defect hdef hMT A 1 zero_lt_one
  refine ⟨1+H,by linarith,?_⟩
  filter_upwards [hg,hh,Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hg hs hL
  intro c hc
  have hp : 0 < Real.log T := zero_lt_one.trans_le hL
  have hr1 : 1 ≤ Real.sqrt (Real.log T) := by simpa using Real.sqrt_le_sqrt hL
  have hrs : Real.sqrt (Real.log T) ≤ Real.log T := by
    nlinarith only [Real.sq_sqrt hp.le,mul_nonneg (Real.sqrt_nonneg (Real.log T))
      (sub_nonneg.mpr hr1)]
  have hr := div_le_div_of_nonneg_left zero_le_one (Real.sqrt_pos.mpr hp) hrs
  exact (abs_sub_le _ _ _).trans ((add_le_add ((hg c hc).trans hr) (hs c hc)).trans_eq
    (by ring))

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
