import RiemannResearch.Analysis.FiniteSpectralEscape
import RiemannResearch.Analysis.FiniteSpectralMomentObstruction

/-!
# Complete-source escape for spectra with changing finite dimensions

The literal Pareto spectrum has index type Fin(finrank(headSpace n N)).
These consumers accept that dependent index type directly. They do not
replace or discard any source vector when the dimension changes.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

variable (ι : ℕ → Type*) [∀ n, Fintype (ι n)]

/-- Exact escape law at moving thresholds for the full dependent spectrum. -/
theorem dependent_moving_highMass_tendsto
    (w lam : (n : ℕ) → ι n → ℝ) (delta : ℝ) (R : ℕ → ℝ)
    (hw : ∀ n i, 0 ≤ w n i) (hlam : ∀ n i, 0 ≤ lam n i)
    (hR : ∀ n, 1 ≤ R n)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hlow : Tendsto (fun n =>
      (1 + R n) * optimizerTail Finset.univ (w n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => highMass Finset.univ (w n) (lam n) (R n)) atTop (𝓝 delta) := by
  have hdiff : Tendsto (fun n => highMass Finset.univ (w n) (lam n) (R n) -
      correction Finset.univ (w n) (lam n)) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |highMass Finset.univ (w n) (lam n) (R n) -
        correction Finset.univ (w n) (lam n)|) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => abs_nonneg _) _ hlow
      intro n
      have hpos : 0 < R n := lt_of_lt_of_le zero_lt_one (hR n)
      have hratio : (1 + R n) / R n ≤ 1 + R n := by
        apply (div_le_iff₀ hpos).mpr
        nlinarith [hR n]
      simpa only [max_eq_left hratio] using
        abs_highMass_sub_correction_le_threshold_tail
          Finset.univ (w n) (lam n) (R n)
          (fun i _ => hw n i) (fun i _ => hlam n i) hpos
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [habs.eventually (Iio_mem_nhds (neg_pos.mpr ha))] with n hn
      have hbound := neg_abs_le (highMass Finset.univ (w n) (lam n) (R n) -
        correction Finset.univ (w n) (lam n))
      linarith
    · intro b hb
      filter_upwards [habs.eventually (Iio_mem_nhds hb)] with n hn
      exact (le_abs_self _).trans_lt hn
  convert hdiff.add hT using 1 <;> simp

/-- At each fixed positive threshold, the escaped source mass tends to the
same residual defect, even as the complete spectrum changes dimension. -/
theorem dependent_highMass_tendsto
    (w lam : (n : ℕ) → ι n → ℝ) (delta R : ℝ)
    (hw : ∀ n i, 0 ≤ w n i) (hlam : ∀ n i, 0 ≤ lam n i) (hR : 0 < R)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hS : Tendsto (fun n => optimizerTail Finset.univ (w n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => highMass Finset.univ (w n) (lam n) R) atTop (𝓝 delta) := by
  have hdiff : Tendsto (fun n => highMass Finset.univ (w n) (lam n) R -
      correction Finset.univ (w n) (lam n)) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |highMass Finset.univ (w n) (lam n) R -
        correction Finset.univ (w n) (lam n)|) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => abs_nonneg _)
        (fun n => abs_highMass_sub_correction_le_threshold_tail
          Finset.univ (w n) (lam n) R
          (fun i _ => hw n i) (fun i _ => hlam n i) hR)
      simpa using hS.const_mul (max (1 + R) ((1 + R) / R))
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [habs.eventually (Iio_mem_nhds (neg_pos.mpr ha))] with n hn
      have hbound := neg_abs_le (highMass Finset.univ (w n) (lam n) R -
        correction Finset.univ (w n) (lam n))
      linarith
    · intro b hb
      filter_upwards [habs.eventually (Iio_mem_nhds hb)] with n hn
      exact (le_abs_self _).trans_lt hn
  convert hdiff.add hT using 1 <;> simp

/-- Vanishing of the escaped mass at just one positive threshold is exact. -/
theorem dependent_highMass_tendsto_zero_iff_defect_zero
    (w lam : (n : ℕ) → ι n → ℝ) (delta R : ℝ)
    (hw : ∀ n i, 0 ≤ w n i) (hlam : ∀ n i, 0 ≤ lam n i) (hR : 0 < R)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hS : Tendsto (fun n => optimizerTail Finset.univ (w n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => highMass Finset.univ (w n) (lam n) R) atTop (𝓝 0) ↔
      delta = 0 := by
  have hB := dependent_highMass_tendsto ι w lam delta R hw hlam hR hT hS
  constructor
  · intro hz
    exact tendsto_nhds_unique hB hz
  · intro hz
    simpa only [hz] using hB

/-- Source tightness for a sequence of complete spectra of varying dimension. -/
def DependentSourceTightAtInfinity (w lam : (n : ℕ) → ι n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ᶠ n in atTop, highMass Finset.univ (w n) (lam n) R ≤ ε

theorem dependent_sourceTightAtInfinity_iff_defect_zero
    (w lam : (n : ℕ) → ι n → ℝ) (delta : ℝ)
    (hw : ∀ n i, 0 ≤ w n i) (hlam : ∀ n i, 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hS : Tendsto (fun n => optimizerTail Finset.univ (w n) (lam n)) atTop (𝓝 0)) :
    DependentSourceTightAtInfinity ι w lam ↔ delta = 0 := by
  have hdelta : 0 ≤ delta :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hT (Filter.Eventually.of_forall
      (fun n => correction_nonneg Finset.univ (w n) (lam n)
        (fun i _ => hw n i) (fun i _ => hlam n i)))
  constructor
  · intro htight
    by_contra hne
    have hpos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
    obtain ⟨R, hR, hupper⟩ := htight (delta / 2) (by linarith)
    have hB := dependent_highMass_tendsto ι w lam delta R hw hlam hR hT hS
    have hlower := hB.eventually_const_lt (show delta / 2 < delta by linarith)
    obtain ⟨n, hn⟩ := (hupper.and hlower).exists
    linarith [hn.1, hn.2]
  · intro hzero ε hε
    refine ⟨1, by norm_num, ?_⟩
    have hz := (dependent_highMass_tendsto_zero_iff_defect_zero ι w lam delta 1
      hw hlam (by norm_num) hT hS).mpr hzero
    exact (hz.eventually_lt_const hε).mono (fun n hn => le_of_lt hn)

/-- The complete double-logarithmic moment has normalized limiting lower
floor delta, with coefficient one. No limit of the moment is assumed.
The chosen positive envelope need not equal the physical optimizer tail. -/
theorem dependent_eventually_lt_relative_doubleLog_moment_of_envelope
    (w lam : (n : ℕ) → ι n → ℝ) (delta : ℝ) (sigma : ℕ → ℝ)
    (hw : ∀ n i, 0 ≤ w n i)
    (hlam : ∀ n i, 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ n, 0 < sigma n) (hone : ∀ n, sigma n < 1)
    (htail : ∀ n, optimizerTail Finset.univ (w n) (lam n) ≤ sigma n) :
    ∀ c : ℝ, c < delta → ∀ᶠ n in atTop,
      c < moment Finset.univ (w n) (lam n) doubleLog /
        Real.log (1 + Real.log (1 / sigma n)) := by
  let R : ℕ → ℝ := fun n => 1 / Real.sqrt (sigma n)
  let D : ℕ → ℝ := fun n => Real.log (1 + Real.log (1 / sigma n))
  have hR : ∀ n, 1 ≤ R n := by
    intro n
    have hroot : 0 < Real.sqrt (sigma n) := Real.sqrt_pos.mpr (hpos n)
    apply (le_div_iff₀ hroot).mpr
    have hsquare := Real.sq_sqrt (hpos n).le
    have hrootnonneg := Real.sqrt_nonneg (sigma n)
    nlinarith [hone n]
  have hD : ∀ n, 0 < D n := by
    intro n
    have hinv : 1 < 1 / sigma n := (lt_div_iff₀ (hpos n)).mpr (by linarith [hone n])
    exact Real.log_pos (by linarith [Real.log_pos hinv])
  have hsqrt : Tendsto (fun n => Real.sqrt (sigma n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsigma
  have hmajor : Tendsto (fun n => sigma n + Real.sqrt (sigma n)) atTop (𝓝 0) := by
    simpa only [add_zero] using hsigma.add hsqrt
  have hlow : Tendsto (fun n => (1 + R n) *
      optimizerTail Finset.univ (w n) (lam n)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => mul_nonneg (by linarith [hR n])
        (optimizerTail_nonneg Finset.univ (w n) (lam n) (fun i _ => hw n i) (fun i _ => hlam n i)))
      _ hmajor
    intro n
    have hroot : 0 < Real.sqrt (sigma n) := Real.sqrt_pos.mpr (hpos n)
    have hrootne : Real.sqrt (sigma n) ≠ 0 := ne_of_gt hroot
    have hsquare : (Real.sqrt (sigma n)) ^ 2 = sigma n := Real.sq_sqrt (hpos n).le
    have hmul := mul_le_mul_of_nonneg_left (htail n)
      (show 0 ≤ 1 + R n by linarith [hR n])
    have hid : (1 + R n) * sigma n = sigma n + Real.sqrt (sigma n) := by
      dsimp [R]
      field_simp [hrootne]
      nlinarith [hsquare]
    exact hmul.trans_eq hid
  have hB := dependent_moving_highMass_tendsto
    ι w lam delta R hw hlam hR hT hlow
  have hinv : Tendsto (fun n => 1 / sigma n) atTop atTop := by
    have hwithin : Tendsto sigma atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hsigma, Filter.Eventually.of_forall hpos⟩
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hwithin
  have hL : Tendsto (fun n => Real.log (1 / sigma n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hinv
  have hinner : Tendsto (fun n => 1 + Real.log (1 / sigma n)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hL.eventually (eventually_ge_atTop (b - 1))] with n hn
    linarith
  have hDto : Tendsto D atTop atTop := Real.tendsto_log_atTop.comp hinner
  have hquot : Tendsto (fun n => Real.log 2 / D n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hDto
  have hscale : Tendsto (fun n => (D n - Real.log 2) / D n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hquot
    simp only [sub_zero] at h
    convert h using 1
    ext n
    field_simp [ne_of_gt (hD n)]
  have hprod : Tendsto (fun n => ((D n - Real.log 2) / D n) *
      highMass Finset.univ (w n) (lam n) (R n)) atTop (𝓝 delta) := by
    simpa only [one_mul] using hscale.mul hB
  intro c hc
  filter_upwards [hprod.eventually_const_lt hc] with n hn
  apply hn.trans_le
  have hmark := threshold_mul_highMass_le_moment
    Finset.univ (w n) (lam n) (R n) doubleLog (fun i _ => hw n i)
    (fun i hi => doubleLog_nonneg (hlam n i))
    (fun i hi hRi => doubleLog_mono_nonneg (by linarith [hR n]) hRi)
  have hscalele : D n - Real.log 2 ≤ doubleLog (R n) :=
    relative_doubleLog_scale_sub_log_two_le_cutoff (sigma n) (hpos n) (hone n)
  have hBnonneg := highMass_nonneg Finset.univ (w n) (lam n) (R n) (fun i _ => hw n i)
  have hnum := (mul_le_mul_of_nonneg_right hscalele hBnonneg).trans hmark
  dsimp [D] at hnum ⊢
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hnum (hD n).le


/-- Any strict feedback fraction of the actual correction is absorbable on
the coefficient-one normalized double-log scale. The moment need not vanish
before this argument: the limiting defect forces its lower floor to delta. -/
theorem dependent_defect_eq_zero_of_relative_doubleLog_feedback
    (w lam : (n : ℕ) → ι n → ℝ) (delta theta : ℝ)
    (sigma E : ℕ → ℝ)
    (hw : ∀ n i, 0 ≤ w n i)
    (hlam : ∀ n i, 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ n, 0 < sigma n) (hone : ∀ n, sigma n < 1)
    (htail : ∀ n, optimizerTail Finset.univ (w n) (lam n) ≤ sigma n)
    (htheta : theta < 1) (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ᶠ n in atTop,
      moment Finset.univ (w n) (lam n) doubleLog /
          Real.log (1 + Real.log (1 / sigma n)) ≤
        E n + theta * correction Finset.univ (w n) (lam n)) : delta = 0 := by
  have hdelta : 0 ≤ delta := le_of_tendsto_of_tendsto tendsto_const_nhds hT
    (Filter.Eventually.of_forall fun n =>
      correction_nonneg Finset.univ (w n) (lam n) (fun i _ => hw n i) (fun i _ => hlam n i))
  by_contra hne
  have hdelta_pos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
  have hstrict : theta * delta < delta := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta hdelta_pos
  let c : ℝ := (delta + theta * delta) / 2
  have hc_delta : c < delta := by dsimp [c]; linarith
  have htheta_c : theta * delta < c := by dsimp [c]; linarith
  have hlower := dependent_eventually_lt_relative_doubleLog_moment_of_envelope
    ι w lam delta sigma hw hlam hT hsigma hpos hone htail c hc_delta
  have hrhs : Tendsto (fun n => E n + theta * correction Finset.univ (w n) (lam n))
      atTop (𝓝 (theta * delta)) := by
    simpa only [zero_add] using hE.add (hT.const_mul theta)
  obtain ⟨n, hn⟩ := (hlower.and (hbudget.and (hrhs.eventually_lt_const htheta_c))).exists
  linarith [hn.1, hn.2.1, hn.2.2]



/-- Finite initial exceptions in envelope positivity, size and domination are
irrelevant. This permits envelopes built directly from the optimizer tail. -/
theorem dependent_eventually_lt_relative_doubleLog_moment_of_eventual_envelope
    (w lam : (n : ℕ) → ι n → ℝ) (delta : ℝ) (sigma : ℕ → ℝ)
    (hw : ∀ n i, 0 ≤ w n i) (hlam : ∀ n i, 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 < sigma n)
    (hone : ∀ᶠ n in atTop, sigma n < 1)
    (htail : ∀ᶠ n in atTop, optimizerTail Finset.univ (w n) (lam n) ≤ sigma n) :
    ∀ c : ℝ, c < delta → ∀ᶠ n in atTop,
      c < moment Finset.univ (w n) (lam n) doubleLog /
        Real.log (1 + Real.log (1 / sigma n)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hpos.and (hone.and htail))
  have hshift := tendsto_add_atTop_nat K
  have hlower :=
    dependent_eventually_lt_relative_doubleLog_moment_of_envelope
      (fun n => ι (n+K)) (fun n => w (n+K)) (fun n => lam (n+K))
      delta (fun n => sigma (n+K)) (fun n => hw (n+K))
      (fun n => hlam (n+K)) (hT.comp hshift) (hsigma.comp hshift)
      (fun n => (hK (n+K) (by omega)).1)
      (fun n => (hK (n+K) (by omega)).2.1)
      (fun n => (hK (n+K) (by omega)).2.2)
  intro c hc
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hlower c hc)
  apply eventually_atTop.mpr
  refine ⟨L+K, ?_⟩
  intro n hn
  have he : n-K+K = n := Nat.sub_add_cancel (by omega)
  let P : ℕ → Prop := fun j =>
    c < moment Finset.univ (w j) (lam j) doubleLog /
      Real.log (1 + Real.log (1 / sigma j))
  have hh : P (n-K+K) := hL (n-K) (by omega)
  exact (congrArg P he).mp hh

/-- A strict normalized moment budget is needed only on a cofinal sequence.
All finite initial envelope exceptions are allowed. This is an arithmetic
provider consumer, not a proof of the budget. -/
theorem dependent_defect_eq_zero_of_cofinal_relative_doubleLog_feedback
    (w lam : (n : ℕ) → ι n → ℝ) (delta theta : ℝ)
    (sigma E : ℕ → ℝ) (k : ℕ → ℕ)
    (hw : ∀ n i, 0 ≤ w n i) (hlam : ∀ n i, 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction Finset.univ (w n) (lam n)) atTop (𝓝 delta))
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 < sigma n)
    (hone : ∀ᶠ n in atTop, sigma n < 1)
    (htail : ∀ᶠ n in atTop, optimizerTail Finset.univ (w n) (lam n) ≤ sigma n)
    (hk : Tendsto k atTop atTop) (htheta : theta < 1)
    (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ᶠ n in atTop,
      moment Finset.univ (w (k n)) (lam (k n)) doubleLog /
          Real.log (1 + Real.log (1 / sigma (k n))) ≤
        E n + theta * correction Finset.univ (w (k n)) (lam (k n))) : delta = 0 := by
  have hdelta : 0 ≤ delta := le_of_tendsto_of_tendsto tendsto_const_nhds hT
    (Filter.Eventually.of_forall fun n =>
      correction_nonneg Finset.univ (w n) (lam n)
        (fun i _ => hw n i) (fun i _ => hlam n i))
  by_contra hne
  have hdelta_pos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
  have hstrict : theta * delta < delta := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta hdelta_pos
  let c : ℝ := (delta + theta * delta) / 2
  have hc_delta : c < delta := by dsimp [c]; linarith
  have htheta_c : theta * delta < c := by dsimp [c]; linarith
  have hlower := hk.eventually
    (dependent_eventually_lt_relative_doubleLog_moment_of_eventual_envelope
      ι w lam delta sigma hw hlam hT hsigma hpos hone htail c hc_delta)
  have hrhs : Tendsto (fun n => E n +
      theta * correction Finset.univ (w (k n)) (lam (k n)))
      atTop (𝓝 (theta * delta)) := by
    simpa only [Function.comp_def, zero_add] using hE.add ((hT.comp hk).const_mul theta)
  obtain ⟨n, hn⟩ :=
    (hlower.and (hbudget.and (hrhs.eventually_lt_const htheta_c))).exists
  linarith [hn.1, hn.2.1, hn.2.2]

end RiemannResearch.Analysis.FiniteSpectralBudget
