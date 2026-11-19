import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.MontgomeryReflectedDefect
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.WeightedSqrtTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The second-order transition at the spike of the raw Montgomery form factor

The narrow complex estimate uses BGSTB's positive-cutoff decomposition
(3.4), the individual errors in its proof, and the Montgomery–Vaughan
mean-value theorem for the prime polynomial. It is a stronger input on a
narrower range than BGSTB's stated (3.5). The reflected quartic estimate
uses the paired fourth-order Gram cancellation. -/
noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open ActualZeroOrdinate MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- The narrow range has x=e^(c/2)√log T. With the linear term retained,
the required error for the normalized complex statistic is 1/log T. -/
def SharpTransitionSecondOrder : Prop :=
  ∀ A : ℝ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    |sharpFormFactor T (transitionFrequency c T) -
      (Real.exp (-c) + transitionFrequency c T)| ≤ H / Real.log T

/-- At a fixed positive fraction of a density frequency width, the two
central shifts are kept together until after squaring. -/
def ReflectedQuarticDefectEstimate (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ,
    let u := α * Real.log T
    |u| ≤ a * Real.log T / 4 →
      horizontalDefect T α ≤ C * (1+|u|)^4 / (Real.log T)^3

/-- Combining the quartic Gram bound with the reflected Selberg density tail
gives the horizontal estimate consumed by the raw transition theorem. -/
theorem reflectedQuarticDefectEstimate_of_uniformSelberg {a : ℝ}
    (ha : 0 < a) (hD : UniformSelbergDensity a) : ReflectedQuarticDefectEstimate a := by
  obtain ⟨A, hA, hgram⟩ := MontgomeryReflectedDefect.exists_horizontalDefect_le_reflected_quartic
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  let B := 48 * C / ((1 - (1/2 : ℝ)) ^ 5 * a ^ 4)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (9 : ℝ)] with T hT₀' hT
  intro α u hu
  have hwidth : 2 * |u| ≤ (1/2) * (a * Real.log T) := by
    change |u| ≤ a * Real.log T / 4 at hu
    linarith only [hu]
  have hm := weightedFourthMoment_div_height_band (hT₀.trans_le hT₀') hC ha
    (by norm_num : (1/2 : ℝ) < 1) hwidth (hden T hT₀')
  have hscale : 0 ≤ A * (1 + |u|)^4 := mul_nonneg hA.le (by positivity)
  apply (hgram T α hT).trans
  exact (mul_le_mul_of_nonneg_left hm hscale).trans_eq (by dsimp [B,u]; ring)

/-- Uniform absolute gap of the raw and complex statistics at scale 1/log T. -/
def RawSharpTransitionScaledGap : Prop :=
  ∀ A ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    |formFactor T (transitionFrequency c T) - sharpFormFactor T (transitionFrequency c T)| ≤
      ε / Real.log T

/-- A squared-norm certificate for the entire bounded transition range.
The normalization allows a density-free fourth-moment provider. -/
def TransitionScaledDefect : Prop :=
  ∀ A ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    horizontalDefect T (transitionFrequency c T) ≤ ε / (Real.log T)^2

theorem transitionScaledDefect_of_reflectedQuartic {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) : TransitionScaledDefect := by
  intro A ε hε
  obtain ⟨C, hC, hq⟩ := hQ
  let δ := ε/(16*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcoef : C*(16*δ) ≤ ε := by
    have hp : 0 < C+1 := by linarith
    dsimp [δ]
    rw [show C*(16*(ε/(16*(C+1)))) = ε*C/(C+1) by field_simp [hp.ne']]
    exact (div_le_iff₀ hp).2 (mul_le_mul_of_nonneg_left (by linarith : C ≤ C+1) hε.le)
  filter_upwards [hq,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 A),
    (loglog_pow_div_log_tendsto_zero 4).eventually_le_const hδ,
    (loglog_pow_div_log_tendsto_zero 1).eventually_le_const
      (by positivity : (0:ℝ) < a/4)] with T hb hT hℓb hfour hband
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let u := (ℓ+c)/2
  have hL : 0 < L := Real.log_pos hT
  change max 1 A ≤ ℓ at hℓb
  change ℓ^4/L ≤ δ at hfour
  simp only [pow_one] at hband
  change ℓ/L ≤ a/4 at hband
  have hℓA := (le_max_right 1 A).trans hℓb
  have hℓ1 := (le_max_left 1 A).trans hℓb
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [(abs_le.mp hc).1]
  have huℓ : u ≤ ℓ := by dsimp [u]; linarith [(abs_le.mp hc).2]
  have hαu : α*L = u := div_mul_cancel₀ _ hL.ne'
  have huB : |α*L| ≤ a*L/4 := by
    rw [hαu, abs_of_nonneg hu0]
    linarith only [huℓ, (div_le_iff₀ hL).mp hband]
  have hpow : (1+u)^4 ≤ (16*δ)*L := by
    have hsum : 1+u ≤ 2*ℓ := by linarith
    have hp := pow_le_pow_left₀ (show 0≤1+u by linarith) hsum 4
    have hf := (div_le_iff₀ hL).mp hfour
    calc
      _ ≤ (2*ℓ)^4 := hp
      _ = 16*ℓ^4 := by ring
      _ ≤ 16*(δ*L) := mul_le_mul_of_nonneg_left hf (by norm_num)
      _ = _ := by ring
  have hdef := hb α huB
  change horizontalDefect T α ≤ C*(1+|α*L|)^4/L^3 at hdef
  rw [hαu, abs_of_nonneg hu0] at hdef
  change horizontalDefect T α ≤ ε/L^2
  calc
    _ ≤ C*(1+u)^4/L^3 := hdef
    _ ≤ C*((16*δ)*L)/L^3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
      (pow_nonneg hL.le _)
    _ = (C*(16*δ))*L/L^3 := by ring
    _ ≤ ε*L/L^3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hL.le)
      (pow_nonneg hL.le _)
    _ = _ := by field_simp [hL.ne']

/-- The square-root comparison and bounded complex spike turn the squared
defect certificate into a uniform absolute error of little-oh of 1/log T. -/
theorem rawSharpTransitionScaledGap_of_defect (hdef : TransitionScaledDefect)
    (hsharp : SharpTransitionSecondOrder) : RawSharpTransitionScaledGap := by
  intro A ε hε
  obtain ⟨H,hH,hcmp⟩ := hsharp A
  let M := Real.sqrt (Real.exp A+1+H)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  let η := min 1 (ε/(1+2*M))
  have hden : 0 < 1+2*M := by linarith
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : (1+2*M)*η ≤ ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hden).mp (min_le_right _ _)
  filter_upwards [hcmp,hdef A (η^2) (by positivity),eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 A),
    (loglog_pow_div_log_tendsto_zero 1).eventually_le_const zero_lt_one]
    with T he hq hT hL1 hℓb hshort
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let u := (ℓ+c)/2
  let r := η/L
  have hL : 0 < L := Real.log_pos hT
  change max 1 A ≤ ℓ at hℓb
  simp only [pow_one] at hshort
  change ℓ/L ≤ 1 at hshort
  have hℓA := (le_max_right 1 A).trans hℓb
  have huℓ : u ≤ ℓ := by dsimp [u]; linarith [(abs_le.mp hc).2]
  have hα1 : α ≤ 1 := (div_le_div_of_nonneg_right huℓ hL.le).trans hshort
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := (div_le_iff₀ hL).2 (by simpa using hη1.trans hL1)
  have hbound : horizontalDefect T α ≤ r^2 := by simpa only [r,div_pow] using hq c hc
  have herr := he c hc
  change |sharpFormFactor T α - (Real.exp (-c) + α)| ≤ H/L at herr
  have hsp : Real.exp (-c) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hc).1])
  have hpeak : Real.sqrt (sharpFormFactor T α) ≤ M := by
    apply Real.sqrt_le_sqrt
    have heH : H/L ≤ H := (div_le_iff₀ hL).2 (le_mul_of_one_le_right hH hL1)
    linarith only [(abs_le.mp herr).2, hsp, hα1, heH]
  have hdiff : |Real.sqrt (formFactor T α) - Real.sqrt (sharpFormFactor T α)| ≤
      Real.sqrt (r^2) := by
    rw [abs_sub_comm]
    exact (sqrt_horizontal_error T α).trans (Real.sqrt_le_sqrt hbound)
  have hpair := WeightedSqrtTransfer.abs_sub_le_of_sqrt (formFactor_nonneg hT α)
    (MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α) (sq_nonneg r) hdiff
  rw [Real.sqrt_sq hr] at hpair
  have hr2 : r^2 ≤ r := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)]
  apply hpair.trans
  calc
    _ ≤ r+(2*M)*r := add_le_add hr2
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpeak (by norm_num)) hr)
    _ = ((1+2*M)*η)/L := by dsimp [r]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hηε hL.le


/-- Wide-band quartic comparison specialized to the shrinking transition. -/
theorem raw_sharp_transition_scaled_gap {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (hsharp : SharpTransitionSecondOrder)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T) - sharpFormFactor T (transitionFrequency c T)| ≤
        ε / Real.log T :=
  rawSharpTransitionScaledGap_of_defect (transitionScaledDefect_of_reflectedQuartic ha hQ)
    hsharp A ε hε

/-- With bounded shifts c, the raw form factor preserves the second term
including its sign. -/
theorem raw_transition_second_order_of_scaled_gap
    (hgap : RawSharpTransitionScaledGap) (hsharp : SharpTransitionSecondOrder)
    (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T) -
        (Real.exp (-c) + transitionFrequency c T)| ≤ K / Real.log T := by
  obtain ⟨H, hH, hs⟩ := hsharp A
  refine ⟨1+H, by linarith, ?_⟩
  filter_upwards [hgap A 1 zero_lt_one, hs] with T h h'
  intro c hc
  exact (abs_sub_le _ _ _).trans ((add_le_add (h c hc) (h' c hc)).trans_eq (by ring))

/-- Density-controlled specialization of the source-independent transfer. -/
theorem raw_transition_second_order {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (hsharp : SharpTransitionSecondOrder) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T) -
        (Real.exp (-c) + transitionFrequency c T)| ≤ K / Real.log T :=
  raw_transition_second_order_of_scaled_gap (fun B _ hε =>
    raw_sharp_transition_scaled_gap ha hQ hsharp B hε) hsharp A

/-- Sharp leading coefficient of the difference from the spike alone,
uniformly for |c|≤A. -/
theorem normalized_raw_transition_uniform_rate_of_scaled_gap
    (hgap : RawSharpTransitionScaledGap) (hsharp : SharpTransitionSecondOrder)
    (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |(2*Real.log T/Real.log (Real.log T)) *
        (formFactor T (transitionFrequency c T)-Real.exp (-c))-1| ≤
        K / Real.log (Real.log T) := by
  obtain ⟨B, hB, hb⟩ := raw_transition_second_order_of_scaled_gap hgap hsharp A
  refine ⟨2*B+|A|, by positivity, ?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T h hT hℓ
  intro c hc
  let L := Real.log T
  let ℓ := Real.log L
  let α := transitionFrequency c T
  let E := formFactor T α - (Real.exp (-c)+α)
  have hL : 0 < L := Real.log_pos hT
  change 0 < ℓ at hℓ
  have hscale : 0 ≤ 2*L/ℓ := by positivity
  have hα : α*L = (ℓ+c)/2 := div_mul_cancel₀ _ hL.ne'
  have he : (2*L/ℓ)*(formFactor T α-Real.exp (-c))-1 = (2*L/ℓ)*E+c/ℓ := by
    dsimp only [E]
    field_simp [hℓ.ne']
    nlinarith only [hα]
  rw [he]
  calc
    _ ≤ |(2*L/ℓ)*E|+|c/ℓ| := abs_add_le _ _
    _ = (2*L/ℓ)*|E|+|c|/ℓ := by rw [abs_mul, abs_of_nonneg hscale, abs_div, abs_of_pos hℓ]
    _ ≤ (2*L/ℓ)*(B/L)+|A|/ℓ := add_le_add (mul_le_mul_of_nonneg_left (h c hc) hscale)
      (div_le_div_of_nonneg_right (hc.trans (le_abs_self A)) hℓ.le)
    _ = (2*B+|A|)/ℓ := by field_simp [hL.ne', hℓ.ne']

/-- Density-controlled specialization of the normalized leading coefficient. -/
theorem normalized_raw_transition_uniform_rate {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (hsharp : SharpTransitionSecondOrder) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |(2*Real.log T/Real.log (Real.log T)) *
        (formFactor T (transitionFrequency c T)-Real.exp (-c))-1| ≤ K / Real.log (Real.log T) :=
  normalized_raw_transition_uniform_rate_of_scaled_gap (fun B _ hε =>
    raw_sharp_transition_scaled_gap ha hQ hsharp B hε) hsharp A

/-- A signed order-1/log T expansion incorporating the archimedean center
log(2π). Passing the concrete statistic explicitly makes this the same
predicate for both orderings of the pair sum. -/
def TransitionArchimedeanCorrection (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ A ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
    |Real.log T*(F T (transitionFrequency c T)-(Real.exp (-c)+transitionFrequency c T))+
      2*(1+Real.log (2*Real.pi))*Real.exp (-c)| ≤ ε

/-- Any signed correction determined on the complex side carries over at
this scale. The complex correction itself is a separate analytic premise. -/
theorem raw_transition_archimedean_of_scaled_gap
    (hgap : RawSharpTransitionScaledGap)
    (hsharp : TransitionArchimedeanCorrection sharpFormFactor) :
    TransitionArchimedeanCorrection formFactor := by
  intro A ε hε
  have hh : 0 < ε/2 := by positivity
  filter_upwards [hgap A (ε/2) hh,hsharp A (ε/2) hh,eventually_gt_atTop (1:ℝ)] with T hg hs hT
  intro c hc
  let α := transitionFrequency c T
  let L := Real.log T
  let main := Real.exp (-c)+α
  let corr := 2*(1+Real.log (2*Real.pi))*Real.exp (-c)
  have hL : 0 < L := Real.log_pos hT
  have hlg : |L*(formFactor T α-sharpFormFactor T α)| ≤ ε/2 := by
    rw [abs_mul, abs_of_pos hL, mul_comm]
    exact (le_div_iff₀ hL).mp (hg c hc)
  change |L*(formFactor T α-main)+corr| ≤ ε
  calc
    _ = |L*(formFactor T α-sharpFormFactor T α) + (L*(sharpFormFactor T α-main)+corr)| := by
      congr 1; ring
    _ ≤ ε/2+ε/2 := (abs_add_le _ _).trans (add_le_add hlg (hs c hc))
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
