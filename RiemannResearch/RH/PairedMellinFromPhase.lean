import RiemannResearch.RH.ParetoMellinObstructionTargets
import RiemannResearch.RH.PairedMellinFrequencies
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Paired annihilators from the phase-centered analytic provider

The proved cutoff frequency selection and common scalar normalization produce
paired annihilators at every requested error scale. The sole analytic assumption
is the explicitly stated `PhaseCenteredAnalyticProvider`.
-/
namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section
open RiemannResearch.LinearAlgebra.PairedAnnihilatorObstruction

/-- A cutoff form of Dirichlet approximation. This is a bounded number-theoretic
interface; it imposes no lower bound proportional to the cutoff on the denominator. -/
def PairedMellinFrequencySelection : Prop :=
  ∀ r : ℝ, 4 ≤ r → ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
    let t := 2 * Real.pi * (m : ℝ) / Real.log (2 : ℝ)
    let s := 2 * Real.pi * (n : ℝ) / Real.log (3 : ℝ)
    1 ≤ t ∧ 1 ≤ s ∧ max t s ≤ 64*r^2 ∧ |t-s| ≤ 16/r^2 ∧ |t-s| ≤ 1

private theorem norm_le_div_sqrt_of_sq_bound {E : Type*} [SeminormedAddCommGroup E]
    (v : E) {a x c k : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hk : 0 ≤ k) (hc : c ≤ k^2) (hv : ‖v‖^2 ≤ c/x) :
    ‖v‖ ≤ k / Real.sqrt a := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hsq : ‖v‖^2*a ≤ k^2 := by
    calc
      _ ≤ ‖v‖^2*x := mul_le_mul_of_nonneg_left hax (sq_nonneg _)
      _ ≤ c := (le_div_iff₀ hx).mp hv
      _ ≤ k^2 := hc
  have hspos := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  apply (le_div_iff₀ hspos).mpr
  have hprod : (‖v‖ * Real.sqrt a)^2 ≤ k^2 := by
    rw [mul_pow,hs]
    exact hsq
  nlinarith [mul_nonneg (norm_nonneg v) hspos.le]

private theorem phase_pair_difference_bound
    (q : ℝ → ThresholdHilbert →L[ℝ] ℂ)
    (hqd : ∀ t : ℝ, 1 ≤ t → DifferentiableAt ℝ q t)
    (hqdb : ∀ t : ℝ, 1 ≤ t → ‖deriv q t‖^2 ≤ 82/t)
    {t s : ℝ} (ht : 1 ≤ t) (hs : 1 ≤ s) :
    ‖q t-q s‖ ≤ (10 / Real.sqrt (min t s)) * |t-s| := by
  let a : ℝ := min t s
  let b : ℝ := max t s
  have ha1 : 1 ≤ a := le_min ht hs
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ q x := by
    intro x hx
    exact hqd x (ha1.trans hx.1)
  have hdb : ∀ x ∈ Set.Icc a b, ‖deriv q x‖ ≤ 10 / Real.sqrt a := by
    intro x hx
    exact norm_le_div_sqrt_of_sq_bound (deriv q x) ha0 hx.1 (by norm_num)
      (by norm_num : (82 : ℝ) ≤ 10^2) (hqdb x (ha1.trans hx.1))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := q) (s := Set.Icc a b) (x := s) (y := t) hd hdb (convex_Icc a b)
    ⟨min_le_right t s, le_max_right t s⟩ ⟨min_le_left t s, le_max_left t s⟩
  simpa only [Real.norm_eq_abs] using h

private theorem common_scale_signal_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : E) (P : E →L[ℝ] ℂ) {t b : ℝ}
    (ht : 1 ≤ t) (htb : t ≤ b)
    (hPu : ‖P u‖ = 1 / Real.sqrt (1+t^2)) :
    1 ≤ ‖((1+b) • P) u‖ := by
  have hb : 0 < 1+b := by linarith
  have hrootpos : 0 < Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have hrootle : Real.sqrt (1+t^2) ≤ 1+b := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hb.le, ?_⟩
    have htb' := mul_self_le_mul_self (show 0 ≤ t by linarith) htb
    nlinarith
  rw [smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos hb, hPu, mul_one_div]
  apply (le_div_iff₀ hrootpos).mpr
  simpa only [one_mul] using hrootle

/-- Common normalization preserves proximity of the two functionals. Individual
phase normalizations are deliberately avoided. -/
private theorem phase_centered_scale_witnesses
    (hphase : PhaseCenteredAnalyticProvider) (hfreq : PairedMellinFrequencySelection)
    (r : ℝ) (hr : 4 ≤ r) :
    ∃ L R : ThresholdHilbert →L[ℝ] ℂ,
      (∀ f ∈ hilbertLegalClosure ({2} : Set ℕ), L f = 0) ∧
      (∀ g ∈ hilbertLegalClosure ({3} : Set ℕ), R g = 0) ∧
      1 ≤ ‖L hilbertOne‖ ∧ 1 ≤ ‖R hilbertOne‖ ∧
      ‖L‖ ≤ 100*r ∧ ‖R‖ ≤ 100*r ∧ ‖L-R‖ ≤ 4000/r := by
  obtain ⟨q, hqrepr, hqnorm, hqone, hqd, hqdb, hqzero⟩ := hphase
  obtain ⟨m,n,hm,hn,hfreq⟩ := hfreq r hr
  let t : ℝ := 2 * Real.pi * (m : ℝ) / Real.log (2 : ℝ)
  let s : ℝ := 2 * Real.pi * (n : ℝ) / Real.log (3 : ℝ)
  change 1 ≤ t ∧ 1 ≤ s ∧ max t s ≤ 64*r^2 ∧ |t-s| ≤ 16/r^2 ∧ |t-s| ≤ 1 at hfreq
  obtain ⟨ht,hs,hmax,hgap,hgap1⟩ := hfreq
  let a : ℝ := min t s
  let b : ℝ := max t s
  let w : ℝ := 1+b
  let L : ThresholdHilbert →L[ℝ] ℂ := w • q t
  let R : ThresholdHilbert →L[ℝ] ℂ := w • q s
  have hr0 : 0 < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have ha1 : 1 ≤ a := le_min ht hs
  have ha0 : 0 < a := by linarith
  have hb1 : 1 ≤ b := ht.trans (le_max_left t s)
  have hw0 : 0 < w := by dsimp [w]; linarith
  have hba : b ≤ a+1 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hgap1
    dsimp [a,b]
    rcases le_total t s with h | h
    · rw [min_eq_left h,max_eq_right h]
      linarith
    · rw [min_eq_right h,max_eq_left h]
      linarith
  have hw : w ≤ 3*a := by dsimp [w]; linarith
  have hrootpos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hrootsq : (Real.sqrt a)^2 = a := Real.sq_sqrt ha0.le
  have hrootr : Real.sqrt a ≤ 8*r := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hab : a ≤ b := min_le_max
    change b ≤ 64*r^2 at hmax
    nlinarith
  have hwroot : w / Real.sqrt a ≤ 3*Real.sqrt a := by
    apply (div_le_iff₀ hrootpos).mpr
    nlinarith [hrootsq]
  have hqt : ‖q t‖ ≤ 3 / Real.sqrt a :=
    norm_le_div_sqrt_of_sq_bound (q t) ha0 (min_le_left t s) (by norm_num)
      (by norm_num : (7 : ℝ) ≤ 3^2) (hqnorm t ht)
  have hqs : ‖q s‖ ≤ 3 / Real.sqrt a :=
    norm_le_div_sqrt_of_sq_bound (q s) ha0 (min_le_right t s) (by norm_num)
      (by norm_num : (7 : ℝ) ≤ 3^2) (hqnorm s hs)
  have hnorm (P : ThresholdHilbert →L[ℝ] ℂ) (hP : ‖P‖ ≤ 3 / Real.sqrt a) :
      ‖w • P‖ ≤ 100*r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hw0]
    calc
      w*‖P‖ ≤ w*(3/Real.sqrt a) := mul_le_mul_of_nonneg_left hP hw0.le
      _ = 3*(w/Real.sqrt a) := by ring
      _ ≤ 3*(3*Real.sqrt a) := mul_le_mul_of_nonneg_left hwroot (by norm_num)
      _ ≤ 100*r := by nlinarith [hrootr]
  refine ⟨L,R,?_,?_,?_,?_,hnorm (q t) hqt,hnorm (q s) hqs,?_⟩
  · intro f hf
    change w • q t f = 0
    have hz : q t f = 0 := by
      simpa only [t, Nat.cast_ofNat] using! (hqzero 2 (by norm_num) m hm f hf)
    rw [hz,smul_zero]
  · intro g hg
    change w • q s g = 0
    have hz : q s g = 0 := by
      simpa only [s, Nat.cast_ofNat] using! (hqzero 3 (by norm_num) n hn g hg)
    rw [hz,smul_zero]
  · exact common_scale_signal_bound hilbertOne (q t) ht (le_max_left t s) (hqone t ht)
  · exact common_scale_signal_bound hilbertOne (q s) hs (le_max_right t s) (hqone s hs)
  · have hd := phase_pair_difference_bound q hqd hqdb ht hs
    change ‖w • q t-w • q s‖ ≤ 4000/r
    have hsm : w • q t-w • q s = w • (q t-q s) := by
      apply ContinuousLinearMap.ext
      intro x
      change w • (q t x)-w • (q s x) = w • (q t x-q s x)
      exact (smul_sub w (q t x) (q s x)).symm
    rw [hsm,norm_smul,Real.norm_eq_abs,abs_of_pos hw0]
    calc
      w*‖q t-q s‖ ≤ w*((10/Real.sqrt a)*|t-s|) :=
        mul_le_mul_of_nonneg_left hd hw0.le
      _ = 10*(w/Real.sqrt a)*|t-s| := by ring
      _ ≤ 10*(3*Real.sqrt a)*|t-s| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwroot (by norm_num))
          (abs_nonneg _)
      _ ≤ 10*(3*(8*r))*|t-s| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        nlinarith [hrootr]
      _ ≤ 10*(3*(8*r))*(16/r^2) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = 3840/r := by
        field_simp [hrne]
        ring
      _ ≤ 4000/r := by
        apply (div_le_div_iff₀ hr0 hr0).mpr
        nlinarith

/-- Exact quantitative reduction from the analytic provider and cutoff frequency
selection. Every sufficiently small real δ is covered, not merely a subsequence. -/
theorem actualPairedMellinProvider_of_phase_of_frequency
    (hphase : PhaseCenteredAnalyticProvider) (hfreq : PairedMellinFrequencySelection) :
    ActualPairedMellinProvider := by
  refine ⟨400000,1,?_⟩
  refine { cost_pos := by norm_num, radius_pos := by norm_num, witnesses := ?_ }
  intro δ hδ hδsmall
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hr : (4 : ℝ) ≤ 4000/δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  obtain ⟨L,R,hL,hR,hLu,hRu,hLn,hRn,hd⟩ :=
    phase_centered_scale_witnesses hphase hfreq (4000/δ) hr
  refine ⟨L,R,hL,hR,hLu,hRu,?_,?_,?_⟩
  · convert! hLn using 1; ring
  · convert! hRn using 1; ring
  · have heq : (4000 : ℝ)/(4000/δ) = δ := by field_simp [hδne]
    rw [heq] at hd
    exact hd

/-- The cutoff frequency-selection theorem discharges the number-theoretic
interface, leaving precisely the original analytic provider. -/
theorem actualPairedMellinProvider_of_phase :
    PhaseCenteredAnalyticProvider → ActualPairedMellinProvider := by
  intro hphase
  apply actualPairedMellinProvider_of_phase_of_frequency hphase
  intro r hr
  exact pairedMellinFrequencies r hr

end
end RiemannResearch.RH.Pareto.CompressedMellin
