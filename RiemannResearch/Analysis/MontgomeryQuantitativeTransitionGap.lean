import RiemannResearch.Analysis.MontgomeryBoundedTransitionPeak
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Quantitative raw-to-complex comparison at the Montgomery transition

On a fixed bounded interval of transition shifts the reflected quartic band
retains an explicit O((log log T)²/(log T)^(3/2)) horizontal rate. -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- A uniform transition defect with logarithmic exponent twice p. -/
def TransitionDefectLogBudget (p : ℕ) : Prop :=
  ∀ A : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    horizontalDefect T (transitionFrequency c T) ≤
      C*(Real.log (Real.log T))^(2*p)/(Real.log T)^3

/-- Taking the square-root defect and using a bounded peak halves the logarithmic exponent. -/
theorem raw_sharp_transition_rate_of_log_budget (p : ℕ) (hQ : TransitionDefectLogBudget p)
    (hpeak : BoundedSharpTransitionPeak) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T)-sharpFormFactor T (transitionFrequency c T)| ≤
        K*(Real.log (Real.log T))^p/(Real.log T*Real.sqrt (Real.log T)) := by
  obtain ⟨C,hC,hq⟩ := hQ A
  obtain ⟨M,hM,hm⟩ := hpeak A
  let B := Real.sqrt C
  have hB := Real.sqrt_nonneg C
  refine ⟨B^2+2*M*B,by dsimp [B]; positivity,?_⟩
  filter_upwards [hq,hm,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0,
    (loglog_pow_div_log_tendsto_zero p).eventually_le_const zero_lt_one]
    with T hd he hT hL1 hl0 hrate
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let r := ℓ^p/(L*Real.sqrt L)
  have hL : 0 < L := Real.log_pos hT
  have hLs := Real.sqrt_pos.mpr hL
  have hLs1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL1
  change 0 ≤ ℓ at hl0
  change ℓ^p/L ≤ 1 at hrate
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := (div_le_iff₀ (mul_pos hL hLs)).2 (by
    have hel : ℓ^p ≤ L := by simpa using (div_le_iff₀ hL).mp hrate
    simpa only [one_mul] using hel.trans (le_mul_of_one_le_right hL.le hLs1))
  have hdef : horizontalDefect T α ≤ (B*r)^2 := by
    apply (hd c hc).trans_eq
    change C*ℓ^(2*p)/L^3 = (Real.sqrt C*(ℓ^p/(L*Real.sqrt L)))^2
    rw [Nat.mul_comm 2 p,pow_mul]
    simp only [mul_pow,div_pow,Real.sq_sqrt hC,Real.sq_sqrt hL.le]
    field_simp [hL.ne'] <;> ring
  have hpeak := he c hc
  have hBr : 0 ≤ B*r := mul_nonneg hB hr0
  have hsq : |Real.sqrt (formFactor T α)-Real.sqrt (sharpFormFactor T α)| ≤ Real.sqrt ((B*r)^2) := by
    rw [abs_sub_comm]
    exact (sqrt_horizontal_error T α).trans (Real.sqrt_le_sqrt hdef)
  have hpair := WeightedSqrtTransfer.abs_sub_le_of_sqrt (formFactor_nonneg hT α)
    (MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α) (sq_nonneg (B*r)) hsq
  rw [Real.sqrt_sq hBr,mul_pow] at hpair
  have hr2 : r^2 ≤ r := by nlinarith only [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  apply hpair.trans
  calc
    _ ≤ B^2*r+(2*M)*(B*r) := add_le_add (mul_le_mul_of_nonneg_left hr2 (sq_nonneg B))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpeak (by norm_num)) hBr)
    _ = (B^2+2*M*B)*ℓ^p/(L*Real.sqrt L) := by dsimp only [r]; ring

/-- A Selberg quartic band supplies the p=2 input at bounded transition shifts. -/
theorem transitionDefectLogBudget_two_of_quartic {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) : TransitionDefectLogBudget 2 := by
  obtain ⟨C,hC,hq⟩ := hQ
  intro A
  refine ⟨16*C,by positivity,?_⟩
  filter_upwards [hq,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 A),
    (loglog_pow_div_log_tendsto_zero 1).eventually_le_const (by positivity : (0:ℝ) < a/4)]
    with T hd hT hlb hw
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let u := (ℓ+c)/2
  have hL : 0 < L := Real.log_pos hT
  change max 1 A ≤ ℓ at hlb
  have hlA := (le_max_right 1 A).trans hlb
  have hl1 := (le_max_left 1 A).trans hlb
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith [(abs_le.mp hc).1]
  have hul : u ≤ ℓ := by dsimp only [u]; linarith [(abs_le.mp hc).2]
  have hα : α*L = u := div_mul_cancel₀ _ hL.ne'
  simp only [pow_one] at hw
  change ℓ/L ≤ a/4 at hw
  have hband : |α*L| ≤ a*L/4 := by
    rw [hα,abs_of_nonneg hu0]
    linarith only [hul,(div_le_iff₀ hL).mp hw]
  have hh := hd α hband
  change horizontalDefect T α ≤ C*(1+|α*L|)^4/L^3 at hh
  rw [hα,abs_of_nonneg hu0] at hh
  apply hh.trans
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1+u by linarith) (by linarith : 1+u ≤ 2*ℓ) 4
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
    (pow_nonneg hL.le 3)).trans_eq
  change C*(2*ℓ)^4/L^3 = (16*C)*ℓ^4/L^3
  ring

/-- The published broad complex estimate suffices for the quantitative transfer. -/
theorem raw_sharp_transition_explicit_rate {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (hBG : BGSTBPositiveCutoffEstimate) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T)-sharpFormFactor T (transitionFrequency c T)| ≤
        K*(Real.log (Real.log T))^2/(Real.log T*Real.sqrt (Real.log T)) :=
  raw_sharp_transition_rate_of_log_budget 2 (transitionDefectLogBudget_two_of_quartic ha hQ)
    (boundedSharpTransitionPeak_of_first_order
      (sharpTransitionFirstOrder_of_corrected (correctedComplexFormFactorEstimate_of_bgstb hBG))) A

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
