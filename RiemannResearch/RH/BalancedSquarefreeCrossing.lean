import RiemannResearch.RH.CanonicalMobiusCesaro
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Crossing-balanced squarefree canonical Möbius heads

Paper Section 21: `Y` here is `n-1` in the continuation. The actual trial
is the already-defined `canonicalMobiusHead Y`; its actual Hilbert lift
is `canonicalMobiusHilbert Y`. All new bounds are restricted to the
explicit reciprocal-charge crossing condition. No RH provider is assumed.

Source: user-provided Green--Pareto--Schur continuation, 6 October 2026,
Section 21 (construction, statements and proof strategy).
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.BalancedSquarefree
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

private theorem crossing_fraction_bounds (N q m : ℝ)
    (hN : 0 < N) (hq : q ≠ 0) (hc : q * (q + m / N) ≤ 0) :
    m ≠ 0 ∧ 0 < -(N*q)/m ∧ -(N*q)/m ≤ 1 := by
  have hNm : N * (m / N) = m := by
    field_simp [ne_of_gt hN]
  rcases lt_or_gt_of_ne hq with hqn | hqp
  · have ht : 0 ≤ q + m / N := by
      by_contra h
      have hp := mul_pos_of_neg_of_neg hqn (lt_of_not_ge h)
      linarith
    have hl : 0 ≤ N*q + m := by
      have hp := mul_nonneg hN.le ht
      nlinarith [hNm]
    have hNq := mul_neg_of_pos_of_neg hN hqn
    have hm : 0 < m := by linarith
    refine ⟨ne_of_gt hm, div_pos (by linarith) hm, ?_⟩
    apply (div_le_iff₀ hm).2
    linarith
  · have ht : q + m / N ≤ 0 := by
      by_contra h
      have hp := mul_pos hqp (lt_of_not_ge h)
      linarith
    have hl : N*q + m ≤ 0 := by
      have hp := mul_nonpos_of_nonneg_of_nonpos hN.le ht
      nlinarith [hNm]
    have hNq := mul_pos hN hqp
    have hm : m < 0 := by linarith
    refine ⟨ne_of_lt hm, div_pos_of_neg_of_neg (by linarith) hm, ?_⟩
    have he : -(N*q)/m = (N*q)/(-m) := by ring
    rw [he]
    apply (div_le_iff₀ (neg_pos.mpr hm)).2
    linarith

def Crossing (Y : ℕ) : Prop :=
  mobiusReciprocalSum Y ≠ 0 ∧
  mobiusReciprocalSum Y * mobiusReciprocalSum (Y+1) ≤ 0

def parameter (Y : ℕ) : ℝ :=
  -(((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y) /
    (ArithmeticFunction.moebius (Y+1) : ℝ)

def source (Y d : ℕ) : ℝ :=
  if d = Y+1 then -(((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y)
  else (ArithmeticFunction.moebius d : ℝ)

abbrev trial (Y : ℕ) : ℕ → ℝ := canonicalMobiusHead Y
abbrev trialHilbert (Y : ℕ) : ThresholdHilbert := canonicalMobiusHilbert Y

def raw (Y j : ℕ) : ℝ :=
  -(∑ d ∈ Finset.Icc 1 Y,
    (ArithmeticFunction.moebius d : ℝ) * residueFraction d j)

theorem crossing_bounds (Y : ℕ) (h : Crossing Y) :
    (ArithmeticFunction.moebius (Y+1) : ℝ) ≠ 0 ∧
      0 < parameter Y ∧ parameter Y ≤ 1 := by
  have hc : mobiusReciprocalSum Y *
      (mobiusReciprocalSum Y +
        (ArithmeticFunction.moebius (Y+1) : ℝ) / ((Y+1 : ℕ) : ℝ)) ≤ 0 := by
    simpa only [mobiusReciprocalSum_succ] using h.2
  simpa only [parameter] using crossing_fraction_bounds
    ((Y+1 : ℕ) : ℝ) (mobiusReciprocalSum Y)
    (ArithmeticFunction.moebius (Y+1) : ℝ) (by positivity) h.1 hc

theorem crossing_squarefree (Y : ℕ) (h : Crossing Y) : Squarefree (Y+1) := by
  by_contra hs
  have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
  exact (crossing_bounds Y h).1 (by simp [hz])

theorem parameter_mul_moebius (Y : ℕ) (h : Crossing Y) :
    parameter Y * (ArithmeticFunction.moebius (Y+1) : ℝ) =
      -(((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y) := by
  unfold parameter
  exact div_mul_cancel₀ _ (crossing_bounds Y h).1

theorem moebius_real_abs_le_one (d : ℕ) :
    |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

theorem boundary_charge_abs_le_one (Y : ℕ) (h : Crossing Y) :
    |((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y| ≤ 1 := by
  have hb := crossing_bounds Y h
  calc
    _ = |-(((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y)| := (abs_neg _).symm
    _ = |parameter Y * (ArithmeticFunction.moebius (Y+1) : ℝ)| :=
      congrArg abs (parameter_mul_moebius Y h).symm
    _ = |parameter Y| * |(ArithmeticFunction.moebius (Y+1) : ℝ)| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul
      (by simpa only [abs_of_pos hb.2.1] using hb.2.2)
      (moebius_real_abs_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem source_one (Y : ℕ) (hY : 0 < Y) : source Y 1 = 1 := by
  have hn : (1 : ℕ) ≠ Y+1 := by omega
  rw [source, if_neg hn]
  norm_num

theorem source_abs_le_one (Y d : ℕ) (h : Crossing Y) : |source Y d| ≤ 1 := by
  by_cases hd : d = Y+1
  · simp only [source, if_pos hd, abs_neg]
    exact boundary_charge_abs_le_one Y h
  · simp only [source, if_neg hd]
    exact moebius_real_abs_le_one d

theorem source_eq_zero_of_not_squarefree (Y d : ℕ) (h : Crossing Y)
    (hd : ¬ Squarefree d) : source Y d = 0 := by
  by_cases hn : d = Y+1
  · subst d
    exact False.elim (hd (crossing_squarefree Y h))
  · have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
    simp [source, hn, hz]

theorem source_reciprocal_charge_zero (Y : ℕ) :
    (∑ d ∈ Finset.Icc 1 (Y+1), source Y d / (d : ℝ)) = 0 := by
  have hs : (∑ d ∈ Finset.Icc 1 Y, source Y d / (d : ℝ)) =
      mobiusReciprocalSum Y := by
    unfold mobiusReciprocalSum
    apply Finset.sum_congr rfl
    intro d hd
    have hn : d ≠ Y+1 := by have := (Finset.mem_Icc.mp hd).2; omega
    simp [source, hn]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y+1), hs]
  rw [source, if_pos rfl]
  have hn : ((Y+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

theorem trial_eq_source (Y j : ℕ) :
    trial Y j = -(∑ d ∈ Finset.Icc 1 (Y+1), source Y d * residueFraction d j) := by
  have hs : (∑ d ∈ Finset.Icc 1 Y, source Y d * residueFraction d j) =
      ∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d j := by
    apply Finset.sum_congr rfl
    intro d hd
    have hn : d ≠ Y+1 := by have := (Finset.mem_Icc.mp hd).2; omega
    simp [source, hn]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y+1), hs]
  rw [source, if_pos rfl]
  unfold trial canonicalMobiusHead
  ring

theorem raw_succ (Y j : ℕ) :
    raw (Y+1) j = raw Y j -
      (ArithmeticFunction.moebius (Y+1) : ℝ) * residueFraction (Y+1) j := by
  unfold raw
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Y+1)]
  ring

theorem raw_head (Y j : ℕ) (hj : 0 < j) (hjY : j ≤ Y) :
    raw Y j = 1 - (j : ℝ) * mobiusReciprocalSum Y := by
  unfold raw
  rw [mobius_residue_prefix_identity Y j hj hjY]
  ring

theorem trial_eq_convex (Y j : ℕ) (h : Crossing Y) :
    trial Y j = (1-parameter Y)*raw Y j + parameter Y*raw (Y+1) j := by
  have hb : ((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum Y =
      -(parameter Y * (ArithmeticFunction.moebius (Y+1) : ℝ)) := by
    linarith [parameter_mul_moebius Y h]
  rw [raw_succ]
  change raw Y j + (((Y+1 : ℕ) : ℝ)*mobiusReciprocalSum Y)*
    residueFraction (Y+1) j = _
  rw [hb]
  ring

theorem trial_head (Y j : ℕ) (hj : 0 < j) (hjY : j < Y+1) : trial Y j = 1 :=
  canonicalMobiusHead_exact Y j hj (by omega)

theorem trial_mem_legal (Y : ℕ) :
    trial Y ∈ legalSeedSpan (Set.Ici 1) := canonicalMobiusHead_mem_legal Y

theorem trialHilbert_sequence (Y j : ℕ) :
    hilbertSequence (trialHilbert Y) j = trial Y j :=
  congrFun (canonicalMobiusHilbert_sequence Y) j

theorem trialHilbert_head (Y j : ℕ) (hj : 0 < j) (hjY : j < Y+1) :
    hilbertSequence (trialHilbert Y) j = 1 := by
  rw [trialHilbert_sequence, trial_head Y j hj hjY]

theorem trial_endpoint (Y : ℕ) :
    trial Y (Y+1) = 1 - ((Y+1 : ℕ) : ℝ) * mobiusReciprocalSum (Y+1) := by
  have hself : residueFraction (Y+1) (Y+1) = 0 := by simp [residueFraction]
  have hraw := raw_succ Y (Y+1)
  rw [hself, mul_zero, sub_zero] at hraw
  change raw Y (Y+1) + (((Y+1 : ℕ) : ℝ)*mobiusReciprocalSum Y)*
    residueFraction (Y+1) (Y+1) = _
  rw [hself, mul_zero, add_zero, ← hraw]
  exact raw_head (Y+1) (Y+1) (by omega) (le_refl _)

theorem trial_endpoint_fraction (Y : ℕ) (h : Crossing Y) :
    trial Y (Y+1) = 1 - (1-parameter Y)*(ArithmeticFunction.moebius (Y+1) : ℝ) := by
  have hn : ((Y+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc : ((Y+1 : ℕ) : ℝ) *
      ((ArithmeticFunction.moebius (Y+1) : ℝ) / ((Y+1 : ℕ) : ℝ)) =
        (ArithmeticFunction.moebius (Y+1) : ℝ) := by field_simp [hn]
  rw [trial_endpoint, mobiusReciprocalSum_succ, mul_add, hc]
  nlinarith [parameter_mul_moebius Y h]

theorem trial_endpoint_error_abs_le_one (Y : ℕ) (h : Crossing Y) :
    |1-trial Y (Y+1)| ≤ 1 := by
  have hb := crossing_bounds Y h
  have h0 : 0 ≤ 1-parameter Y := by linarith
  have h1 : 1-parameter Y ≤ 1 := by linarith
  rw [trial_endpoint_fraction Y h]
  have he : 1-(1-(1-parameter Y)*(ArithmeticFunction.moebius (Y+1) : ℝ)) =
      (1-parameter Y)*(ArithmeticFunction.moebius (Y+1) : ℝ) := by ring
  rw [he, abs_mul, abs_of_nonneg h0]
  calc
    _ ≤ 1*1 := mul_le_mul h1 (moebius_real_abs_le_one _)
      (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem trial_abs_le (Y j : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    |trial Y j| ≤ (Y : ℝ) := by
  have hs := finite_mobius_sum_abs Y hY (fun d => residueFraction d j) 1
    (by simp [residueFraction, Nat.mod_one])
    (fun d hd => residueFraction_abs_le_one d j (Finset.mem_Icc.mp hd).1)
  have hc : |(((Y+1 : ℕ) : ℝ)*mobiusReciprocalSum Y)*residueFraction (Y+1) j| ≤ 1 := by
    rw [abs_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (boundary_charge_abs_le_one Y h)
        (residueFraction_abs_le_one _ _ (by omega)) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  unfold trial canonicalMobiusHead
  calc
    _ ≤ |-(∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ)*residueFraction d j)| +
      |(((Y+1 : ℕ) : ℝ)*mobiusReciprocalSum Y)*residueFraction (Y+1) j| :=
      abs_add_le _ _
    _ ≤ ((Y : ℝ)-1)*1 + 1 := by rw [abs_neg]; exact add_le_add hs hc
    _ = (Y : ℝ) := by ring

theorem trial_error_abs_le (Y j : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    |1-trial Y j| ≤ ((Y+1 : ℕ) : ℝ) := by
  have hs := abs_add_le (1 : ℝ) (-trial Y j)
  rw [abs_one, abs_neg] at hs
  change |1 - trial Y j| ≤ 1 + |trial Y j| at hs
  have hb := trial_abs_le Y j hY h
  push_cast
  linarith

end RiemannResearch.RH.Pareto.BalancedSquarefree
