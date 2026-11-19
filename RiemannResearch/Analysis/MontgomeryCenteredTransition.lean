import RiemannResearch.Analysis.MontgomeryBGSTBTransitionComponents
import RiemannResearch.Analysis.MontgomeryCenteredLogMeanSquare
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Component interface for the signed archimedean transition

Centering the logarithmic signal at log(2π) improves the required signed
cross estimates. The two residuals below are the exact narrow analytic
statements used here. The signed nonleading terms of the positive-height
explicit formula, and the quantitative prime number theorem, are described in
the accompanying proof note. -/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor MontgomeryLogMeanSquare

def centeredLogSignalEnergy (k T x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, (Real.log (t+2)-k)^2)/x^2

/-- Positive-height cutoff and the total signed cross remainder after
centering the gamma signal at log(2π), scaled by T. -/
def CenteredPositiveCutoffRemainder : Prop :=
  ∀ A ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    let u := transitionFrequency c T*Real.log T
    let x := Real.exp u
    |2*Real.pi*(actualComplexPairSum T (Real.log x)).re -
      (centeredLogSignalEnergy (Real.log (2*Real.pi)) T x + primeSignalEnergy T x)| ≤ ε*T

/-- The signed prime residual with main term T log x in the range
x=e^(c/2)√(log T). The leading constant in the prime diagonal cancels
between the closed head and open tail. -/
def NarrowPrimeMeanSquareRemainder : Prop :=
  ∀ A ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    let u := transitionFrequency c T*Real.log T
    let x := Real.exp u
    |primeSignalEnergy T x-T*Real.log x| ≤ ε*T

/-- Signed order-1/log T coefficient from the two actual positive-cutoff
residuals and the proven centered logarithmic mean square. -/
theorem sharpTransitionArchimedean_of_centered_component_bounds
    (hcut : CenteredPositiveCutoffRemainder) (hprime : NarrowPrimeMeanSquareRemainder) :
    TransitionArchimedeanCorrection sharpFormFactor := by
  intro A ε hε
  let k := Real.log (2*Real.pi)
  let B := Real.exp |A|
  let η := ε/3
  have hη : 0 < η := by dsimp [η]; positivity
  have hB : 0 < B := Real.exp_pos _
  have hm := (Metric.tendsto_nhds.mp (centered_log_mean_square_coefficient k))
    (η/B) (div_pos hη hB)
  filter_upwards [hcut A η hη,hprime A η hη,hm,eventually_gt_atTop (1 : ℝ)] with T hc hp he hT
  intro c ha
  let α := transitionFrequency c T
  let L := Real.log T
  let u := α*L
  let x := Real.exp u
  let I := ∫ t in (0 : ℝ)..T, (Real.log (t+2)-k)^2
  let Q := 2*Real.pi*(actualComplexPairSum T (Real.log x)).re
  let e := Real.exp (-c)
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hL : 0 < L := Real.log_pos hT
  have hx : 0 < x := Real.exp_pos _
  have hu : u = (Real.log L+c)/2 := div_mul_cancel₀ _ hL.ne'
  have hx2 : L/x^2 = e := by
    dsimp only [x,e]
    rw [pow_two,← Real.exp_add,hu,show (Real.log L+c)/2+(Real.log L+c)/2=Real.log L+c by ring,
      Real.exp_add,Real.exp_log hL,div_mul_eq_div_div,div_self hL.ne',one_div,Real.exp_neg]
  have heB : e ≤ B := Real.exp_le_exp.mpr (by linarith only [(abs_le.mp ha).1,le_abs_self A])
  have hc' : |Q-(I/x^2+primeSignalEnergy T x)|/T ≤ η := (div_le_iff₀ hTpos).2 (hc c ha)
  have hp' : |primeSignalEnergy T x-T*Real.log x|/T ≤ η := (div_le_iff₀ hTpos).2 (hp c ha)
  have he' : |(I/T-L^2)/L+2*(1+k)| ≤ η/B := by
    simpa only [Real.dist_eq,sub_neg_eq_add,neg_mul] using he.le
  have he'' : |((I/T-L^2)/L+2*(1+k))*e| ≤ η := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul he' heB (Real.exp_pos _).le (div_nonneg hη.le hB.le)).trans_eq
      (div_mul_cancel₀ _ hB.ne')
  have hident := sharpFormFactor_sub_main_eq_pair_remainder T α hT
  change sharpFormFactor T α-(Real.exp (-2*u)*L+α) =
      ((actualComplexPairSum T (Real.log x)).re-
        T/(2*Real.pi)*(L^2/x^2+Real.log x))/(T*L/(2*Real.pi)) at hident
  rw [show Real.exp (-2*u)*L=e from transition_spike c T hT] at hident
  have hid : L*(sharpFormFactor T α-(e+α))+2*(1+k)*e =
      (Q-(I/x^2+primeSignalEnergy T x))/T+(primeSignalEnergy T x-T*Real.log x)/T+
        ((I/T-L^2)/L+2*(1+k))*e := by
    rw [hident,← hx2]
    dsimp only [Q]
    field_simp [hTpos.ne',hL.ne',hx.ne',Real.pi_ne_zero]
    ring
  change |L*(sharpFormFactor T α-(e+α))+2*(1+k)*e| ≤ ε
  rw [hid]
  apply (abs_add_le _ _).trans
  have h₁ : |(Q-(I/x^2+primeSignalEnergy T x))/T| ≤ η := by
    rw [abs_div,abs_of_pos hTpos]
    exact hc'
  have h₂ : |(primeSignalEnergy T x-T*Real.log x)/T| ≤ η := by
    rw [abs_div,abs_of_pos hTpos]
    exact hp'
  have hinit := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  exact (add_le_add hinit he'').trans_eq (by dsimp [η]; ring)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
