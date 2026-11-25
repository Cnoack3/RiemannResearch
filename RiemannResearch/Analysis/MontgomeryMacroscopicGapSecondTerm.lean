import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import RiemannResearch.Analysis.MontgomeryScaledHeightTests
import RiemannResearch.Analysis.DyadicZeroWassersteinLaws
import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Logarithmic correction to macroscopic positive gap counts

At full unfolded width, ordering divides the distinct-ordinate pairs exactly
in half. The measured collision atom is negligible even after multiplication
by the logarithmic factor. For smaller fractions of the cutoff, one-point
height corrections enter twice: through the clipped row lengths and through
the count increments in those rows.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPoisson MontgomeryLocalMass DyadicZeroWasserstein

/-- At the full unfolded height, the two orientations and the measured
equal-ordinate atom partition all ordered pairs of zero occurrences. -/
theorem positiveGapMass_full_width_identity {T : ℝ} (hT : 1 < T) :
    let D := T * Real.log T / (2 * Real.pi)
    2 * D * positiveGapMass T D + actualCollision T = (Ncount 0 T : ℝ)^2 := by
  classical
  let L := Real.log T / (2 * Real.pi)
  let D := T * Real.log T / (2 * Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  let t := copyOrdinate T
  let p := fun i j : Copies T =>
    if 0 < L * (t j - t i) ∧ L * (t j - t i) ≤ D then (1 : ℝ) else 0
  have hdist (i j : Copies T) : L * (t j - t i) ≤ D := by
    have hi : 0 < t i := (mem_cutoff.mp i.1.property).2.1
    have hj : t j ≤ T := (mem_cutoff.mp j.1.property).2.2
    calc
      _ ≤ L * T := mul_le_mul_of_nonneg_left (by linarith only [hi, hj]) hL.le
      _ = _ := by dsimp only [L,D]; ring
  have hpair (i j : Copies T) :
      p i j + p j i + (if t i = t j then (1 : ℝ) else 0) = 1 := by
    dsimp only [p]
    simp only [hdist, and_true, mul_pos_iff_of_pos_left hL, sub_pos]
    rcases lt_trichotomy (t i) (t j) with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  have htot : (∑ i : Copies T, ∑ j : Copies T,
      (p i j + p j i + if t i = t j then (1:ℝ) else 0)) =
      ∑ _i : Copies T, ∑ _j : Copies T, (1:ℝ) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpair i j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_copies,
    nsmul_eq_mul, mul_one] at htot
  have hswap : (∑ i : Copies T, ∑ j : Copies T, p j i) = ∑ i : Copies T, ∑ j : Copies T, p i j :=
    Finset.sum_comm
  have hdiag : (∑ i : Copies T, ∑ j : Copies T, if t i = t j then (1 : ℝ) else 0) =
      (actualCollision T : ℝ) := by
    unfold actualCollision occurrenceCollision
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, t]
  rw [hswap, hdiag] at htot
  change 2 * D * ((∑ i : Copies T, ∑ j : Copies T, p i j) / D) +
    (actualCollision T : ℝ) = (Ncount 0 T : ℝ)^2
  rw [mul_assoc, mul_comm D ((_ : ℝ) / D), div_mul_cancel₀ _ hD.ne']
  nlinarith only [htot]

/-- Even after multiplication by log T, the actual equal-ordinate atom is
negligible relative to the square of the unfolded cutoff. -/
theorem log_mul_collision_div_mainTerm_sq_tendsto_zero :
    Tendsto (fun T : ℝ => Real.log T * ((actualCollision T : ℝ) / (unfoldedCutoff T)^2))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hrow⟩ := exists_actual_cauchy_row_bound
  have hz := tendsto_count_div_mainTerm.mul Real.log_div_self_tendsto_zero
  have hu := hz.const_mul (4 * Real.pi * C)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact mul_nonneg (Real.log_nonneg hT) (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  let D := unfoldedCutoff T
  have ht : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogs : Real.log (T+3) ≤ 2 * Real.log T := by
    have hle : T+3 ≤ T^2 := by nlinarith only [hT, mul_nonneg (sub_nonneg.mpr hT) ht.le]
    have hl := Real.log_le_log (by linarith : 0 < T+3) hle
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  have hc := collision_le_kernelEnergy (copyOrdinate T) cauchyWeight cauchyWeight_nonneg
    (by norm_num [cauchyWeight])
  have htotal : (actualCollision T : ℝ) ≤ (Ncount 0 T : ℝ) * (C * Real.log (T+3)) := by
    apply hc.trans
    apply (Finset.sum_le_sum fun i _ => hrow T ht.le (copyOrdinate T i)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
  calc
    Real.log T * ((actualCollision T : ℝ) / D^2) ≤ Real.log T *
        ((Ncount 0 T : ℝ) * (C * (2 * Real.log T)) / D^2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (htotal.trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogs hC.le) (Nat.cast_nonneg _)))
        (sq_nonneg _)) hlog.le
    _ = (4 * Real.pi * C) * (((Ncount 0 T : ℝ) / D) * (Real.log T/T)) := by
      dsimp only [D,unfoldedCutoff]
      field_simp [Real.pi_ne_zero, ht.ne', hlog.ne'] <;> ring

/-- Riemann–von Mangoldt gives the second term of the cumulative count in
the full unfolded-cutoff normalization. -/
theorem log_mul_count_ratio_sub_one (hRvM : CumulativeRvM) :
    Tendsto (fun T : ℝ => Real.log T * ((Ncount 0 T : ℝ) / unfoldedCutoff T - 1)) atTop
      (𝓝 (-(1 + Real.log (2 * Real.pi)))) := by
  obtain ⟨C,hC,he⟩ := hRvM
  have herr : Tendsto (fun T : ℝ => 2*Real.pi/T * countError T) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := Real.log_div_self_tendsto_zero.const_mul (2*Real.pi*C)
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hu
    filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T h hT
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi/T)]
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*Real.pi/T)).trans_eq (by ring)
  have ht := herr.sub (tendsto_const_nhds (x := 1 + Real.log (2*Real.pi)))
  simp only [zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have ht₀ := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  dsimp only [countError,countMain,unfoldedCutoff]
  rw [Real.log_div ht₀.ne' (by positivity : 2*Real.pi ≠ 0)]
  field_simp [ht₀.ne',hl.ne',Real.pi_ne_zero] <;> ring

/-- The second-order term at the width exhausting all positive gaps accounts
for the measured equal-ordinate atom. -/
theorem positiveGapMass_full_width_second_term_of_cumulativeRvM (hRvM : CumulativeRvM) :
    Tendsto (fun T : ℝ => Real.log T *
      (positiveGapMass T (unfoldedCutoff T) / unfoldedCutoff T - 1/2))
      atTop (𝓝 (-(1 + Real.log (2*Real.pi)))) := by
  have h := (((log_mul_count_ratio_sub_one hRvM).mul
      (tendsto_count_div_mainTerm.add (tendsto_const_nhds (x := (1:ℝ))))).sub
      log_mul_collision_div_mainTerm_sq_tendsto_zero).div_const 2
  have hlim : (-(1+Real.log (2*Real.pi))*(1+1)-0)/2 = -(1+Real.log (2*Real.pi)) := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  let D := unfoldedCutoff T
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have he := positiveGapMass_full_width_identity hT
  change 2*D*positiveGapMass T D + (actualCollision T : ℝ) = (Ncount 0 T : ℝ)^2 at he
  change (Real.log T * ((Ncount 0 T : ℝ)/D - 1)*((Ncount 0 T : ℝ)/D + 1) -
      Real.log T*((actualCollision T : ℝ)/D^2))/2 =
    Real.log T*(positiveGapMass T D/D-1/2)
  field_simp [hD.ne']
  nlinarith only [congrArg (fun z : ℝ => Real.log T * z) he]

/-- The logarithmic correction at the full width for the actual positive gaps. -/
theorem positiveGapMass_full_width_second_term :
    Tendsto (fun T : ℝ => Real.log T *
      (positiveGapMass T (unfoldedCutoff T) / unfoldedCutoff T - 1/2))
      atTop (𝓝 (-(1 + Real.log (2*Real.pi)))) :=
  positiveGapMass_full_width_second_term_of_cumulativeRvM actual_cumulativeRvM

/-- One-point correction in unfolded-height coordinates. -/
def heightCountSecondProfile (x : ℝ) : ℝ := x * (Real.log x - Real.log (2*Real.pi) - 1)

theorem continuous_heightCountSecondProfile : Continuous heightCountSecondProfile := by
  have h : Continuous (fun x : ℝ => x*Real.log x-x*(Real.log (2*Real.pi)+1)) :=
    Real.continuous_mul_log.sub (continuous_id.mul_const _)
  have he : heightCountSecondProfile = fun x : ℝ => x*Real.log x-x*(Real.log (2*Real.pi)+1) := by
    funext x
    dsimp only [heightCountSecondProfile]
    ring
  rw [he]
  exact h

/-- The first integral is the correction to the clipped ramp mean. The second
is the correction to the normalized count in the individual ordinate rows. -/
def macroscopicGapSecondCoefficient (c : ℝ) : ℝ :=
  (∫ u in (1-c)..1, heightCountSecondProfile u) +
    ∫ x in (0 : ℝ)..1, heightCountSecondProfile (min 1 (x+c)) - heightCountSecondProfile x

/-- The first-order empirical height error after subtracting its explicit
second profile bounds the full pair correction up to one continuous test. -/
theorem macroscopic_second_error_le {T c η : ℝ} (hT : 1 < T) (hc : c ∈ Icc (0:ℝ) 1)
    (hF : ∀ u ∈ Icc (0:ℝ) 1, |scaledHeightCount T u -
      (u + heightCountSecondProfile u / Real.log T)| ≤ η) :
    let g := fun x => heightCountSecondProfile (min 1 (x+c)) - heightCountSecondProfile x
    |Real.log T * (positiveGapMass T (c * unfoldedCutoff T) / unfoldedCutoff T - (c-c^2/2)) -
      ((∫ u in (1-c)..1, heightCountSecondProfile u) +
        (∑ i : Copies T, g (copyOrdinate T i / T)) / unfoldedCutoff T)| ≤
      (2 * ((Ncount 0 T : ℝ) / unfoldedCutoff T) + c) * (Real.log T * η) := by
  classical
  let D := unfoldedCutoff T
  let L := Real.log T
  let B := heightCountSecondProfile
  let F := scaledHeightCount T
  let S := fun u => u+B u/L
  let x := fun i : Copies T => copyOrdinate T i/T
  let y := fun i : Copies T => min 1 (x i+c)
  let g := fun v => B (min 1 (v+c)) - B v
  have ht := zero_lt_one.trans hT
  have hD : 0 < D := div_pos (mul_pos ht (Real.log_pos hT)) (by positivity)
  have hL : 0 < L := Real.log_pos hT
  have hx (i : Copies T) : x i ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (mem_cutoff.mp i.1.property).2.1.le ht.le,
      (div_le_iff₀ ht).mpr (by rw [one_mul]; exact (mem_cutoff.mp i.1.property).2.2)⟩
  have hy (i : Copies T) : y i ∈ Icc (0:ℝ) 1 :=
    ⟨le_min zero_le_one (add_nonneg (hx i).1 hc.1),min_le_left _ _⟩
  have hs (i : Copies T) :
      |(F (y i)-F (x i)) - ((y i-x i) + g (x i)/L)| ≤ 2*η := by
    have h1 := abs_le.mp (hF _ (hx i))
    have h2 := abs_le.mp (hF _ (hy i))
    change |(scaledHeightCount T (y i)-scaledHeightCount T (x i)) -
      ((y i-x i) + (heightCountSecondProfile (y i)-heightCountSecondProfile (x i))/Real.log T)| ≤ _
    rw [sub_div]
    exact abs_le.mpr ⟨by linarith only [h2.1,h1.2],by linarith only [h2.2,h1.1]⟩
  let W := (∑ i : Copies T, g (x i))/D
  have hsum :
      |positiveGapMass T (c*D)/D - ((∫ u in (1-c)..1, F u) + W/L)| ≤
        ((Ncount 0 T : ℝ)/D)*(2*η) := by
    have hp := positiveGapMass_scaled_eq_height_rows hT hc.1
    change positiveGapMass T (c*D) = ∑ i : Copies T, (F (y i)-F (x i)) at hp
    have hri := clipped_row_integral hT hc.1
    change (∑ i : Copies T, (y i-x i))/D = ∫ u in (1-c)..1, F u at hri
    rw [hp, ← hri]
    have hsumId : (∑ i : Copies T, (y i-x i))/D + W/L =
        (∑ i : Copies T, ((y i-x i)+g (x i)/L))/D := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, add_div]
      dsimp only [W]
      ring
    rw [hsumId, ← sub_div, ← Finset.sum_sub_distrib, abs_div,abs_of_pos hD]
    have a := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Copies T))) => hs i)
    simp only [Finset.sum_const,Finset.card_univ,card_copies,nsmul_eq_mul] at a
    exact (div_le_div_of_nonneg_right a hD.le).trans_eq (by ring)
  have ha : 1-c ≤ 1 := sub_le_self _ hc.1
  have hS : Continuous S := continuous_id.add (continuous_heightCountSecondProfile.div_const L)
  have hI : (∫ u in (1-c)..1, S u) =
      c-c^2/2 + (∫ u in (1-c)..1, B u)/L := by
    dsimp only [S]
    rw [intervalIntegral.integral_add (f := fun u : ℝ => u) (g := fun u => B u/L)
      (continuous_id.intervalIntegrable _ _) ((continuous_heightCountSecondProfile.div_const L).intervalIntegrable _ _),
      integral_id, intervalIntegral.integral_div]
    ring
  have hmono := scaledHeightCount_mono hT
  have hlo := intervalIntegral.integral_mono_on (μ := volume) ha (f := fun u => S u-η)
    ((hS.sub continuous_const).intervalIntegrable _ _) (g := F) hmono.intervalIntegrable
    (fun u hu => by have hh := (abs_le.mp (hF u ⟨(sub_nonneg.mpr hc.2).trans hu.1,hu.2⟩)).1;
                    change u + heightCountSecondProfile u / Real.log T - η ≤ scaledHeightCount T u;
                    linarith only [hh])
  have hhi := intervalIntegral.integral_mono_on (μ := volume) ha (f := F) hmono.intervalIntegrable
    (g := fun u => S u+η) ((hS.add continuous_const).intervalIntegrable _ _)
    (fun u hu => by have hh := (abs_le.mp (hF u ⟨(sub_nonneg.mpr hc.2).trans hu.1,hu.2⟩)).2;
                    change scaledHeightCount T u ≤ u + heightCountSecondProfile u / Real.log T + η;
                    linarith only [hh])
  rw [intervalIntegral.integral_sub (f := S) (g := fun _ => η) (hS.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, hI] at hlo
  rw [intervalIntegral.integral_add (f := S) (g := fun _ => η) (hS.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, hI] at hhi
  simp only [smul_eq_mul] at hlo hhi
  let Q := ∫ u in (1-c)..1, B u
  have he : |positiveGapMass T (c*D)/D - ((c-c^2/2)+(Q+W)/L)| ≤
      ((Ncount 0 T : ℝ)/D)*(2*η)+c*η := by
    have ha₁ := abs_le.mp hsum
    dsimp only [Q]
    rw [add_div]
    exact abs_le.mpr ⟨by nlinarith only [ha₁.1,hlo],by nlinarith only [ha₁.2,hhi]⟩
  change |L*(positiveGapMass T (c*D)/D-(c-c^2/2)) - (Q+W)| ≤ _
  rw [show L*(positiveGapMass T (c*D)/D-(c-c^2/2)) - (Q+W) =
    L*(positiveGapMass T (c*D)/D-((c-c^2/2)+(Q+W)/L)) by field_simp [hL.ne']; ring,
    abs_mul,abs_of_pos hL]
  apply (mul_le_mul_of_nonneg_left he hL.le).trans_eq
  dsimp only [D,L]
  ring

/-- Uniform one-point asymptotics and convergence against continuous
ordinate tests determine the macroscopic logarithmic correction. -/
theorem macroscopic_gap_second_term_of_height_test {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1)
    (hcount : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) 1,
      |scaledHeightCount T u - (u + heightCountSecondProfile u / Real.log T)| ≤ K/T)
    (hweak : ∀ g : ℝ → ℝ, ContinuousOn g (Icc (0:ℝ) 1) →
      Tendsto (fun T : ℝ => (∑ i : Copies T, g (copyOrdinate T i / T)) / unfoldedCutoff T)
        atTop (𝓝 (∫ x in (0:ℝ)..1, g x))) :
    Tendsto (fun T : ℝ => Real.log T * (positiveGapMass T (c * unfoldedCutoff T) /
      unfoldedCutoff T - (c-c^2/2))) atTop (𝓝 (macroscopicGapSecondCoefficient c)) := by
  let B := heightCountSecondProfile
  let g := fun x => B (min 1 (x+c)) - B x
  let W := fun T => (∑ i : Copies T, g (copyOrdinate T i / T)) / unfoldedCutoff T
  let Q := ∫ u in (1-c)..1, B u
  have hg : Continuous g :=
    (continuous_heightCountSecondProfile.comp (continuous_const.min (continuous_id.add continuous_const))).sub
      continuous_heightCountSecondProfile
  obtain ⟨K,hK,hF⟩ := hcount
  have he : Tendsto (fun T : ℝ => Real.log T * (positiveGapMass T (c*unfoldedCutoff T) /
      unfoldedCutoff T - (c-c^2/2)) - (Q+W T)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := (((tendsto_count_div_mainTerm.const_mul 2).add (tendsto_const_nhds (x := c))).mul
      (Real.log_div_self_tendsto_zero.const_mul K))
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hu
    filter_upwards [eventually_gt_atTop (1:ℝ),hF] with T hT hFT
    rw [Real.norm_eq_abs]
    apply (macroscopic_second_error_le hT hc hFT).trans_eq
    dsimp only [unfoldedCutoff]
    ring
  have hmain : Tendsto (fun T : ℝ => Q+W T) atTop (𝓝 (macroscopicGapSecondCoefficient c)) :=
    (tendsto_const_nhds (x:=Q)).add (hweak g hg.continuousOn)
  simpa only [sub_add_cancel,zero_add] using he.add hmain


/-- The uniform expansion of the actual height counts required by the pair estimate. -/
theorem eventually_scaledHeightCount_second_profile :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) 1,
      |scaledHeightCount T u - (u + heightCountSecondProfile u / Real.log T)| ≤ K/T := by
  simpa only [scaledHeightCount,unfoldedCutoff,heightCountSecondProfile] using
    DyadicZeroWasserstein.eventually_uniform_scaled_count_error

/-- At each fixed fraction of the full height the measured positive-gap mass
has the explicit first logarithmic correction. -/
theorem macroscopic_gap_second_term {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    Tendsto (fun T : ℝ => Real.log T * (positiveGapMass T (c * unfoldedCutoff T) /
      unfoldedCutoff T - (c-c^2/2))) atTop (𝓝 (macroscopicGapSecondCoefficient c)) :=
  macroscopic_gap_second_term_of_height_test hc eventually_scaledHeightCount_second_profile
    scaledHeightTest_tendsto

private def heightProfilePrimitive (x : ℝ) : ℝ :=
  x^2 * Real.log x / 2 - x^2 * ((2 * Real.log (2*Real.pi) + 3)/4)

private theorem heightProfilePrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt heightProfilePrimitive (heightCountSecondProfile x) x := by
  by_cases hx : x = 0
  · subst x
    rw [show heightCountSecondProfile 0 = 0 by simp [heightCountSecondProfile],
      hasDerivAt_iff_tendsto_slope_zero]
    have hc : Continuous (fun t : ℝ => t*Real.log t/2 - t*((2*Real.log (2*Real.pi)+3)/4)) :=
      (Real.continuous_mul_log.div_const 2).sub (continuous_id.mul continuous_const)
    have he (t : ℝ) : t⁻¹ * heightProfilePrimitive t =
        t * Real.log t / 2 - t * ((2*Real.log (2*Real.pi)+3)/4) := by
      by_cases ht : t = 0
      · simp [ht,heightProfilePrimitive]
      · unfold heightProfilePrimitive
        field_simp [ht] <;> ring
    simp only [zero_add, show heightProfilePrimitive 0 = 0 by simp [heightProfilePrimitive],
      sub_zero,smul_eq_mul]
    simp_rw [he]
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  · have hq := (hasDerivAt_id x).pow 2
    have hp := ((hq.mul (Real.hasDerivAt_log hx)).div_const 2).sub
      (hq.mul_const ((2*Real.log (2*Real.pi)+3)/4))
    apply hp.congr_deriv
    simp only [heightCountSecondProfile, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one]
    field_simp [hx] <;> ring

private theorem integral_heightCountSecondProfile (v w : ℝ) :
    (∫ x in v..w, heightCountSecondProfile x) = heightProfilePrimitive w-heightProfilePrimitive v :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => heightProfilePrimitive_hasDerivAt x)
    (continuous_heightCountSecondProfile.intervalIntegrable _ _)

/-- Closed form for the logarithmic coefficient, including the endpoint values
with Lean's real logarithm at zero. -/
theorem macroscopicGapSecondCoefficient_eq {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    macroscopicGapSecondCoefficient c =
      (-(1-c)^2*Real.log (1-c) - c^2*Real.log c - 5*c + 3*c^2 +
        2*Real.log (2*Real.pi)*c*(c-2))/2 := by
  let g := fun x => heightCountSecondProfile (min 1 (x+c))
  have hg : Continuous g := continuous_heightCountSecondProfile.comp
    (continuous_const.min (continuous_id.add continuous_const))
  have hcut : (∫ x in (0:ℝ)..1, g x) =
      (∫ x in c..1, heightCountSecondProfile x) + c * heightCountSecondProfile 1 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 (1-c))
      (hg.intervalIntegrable (1-c) 1)]
    have hl : (∫ x in (0:ℝ)..(1-c), g x) =
        ∫ x in 0..(1-c), heightCountSecondProfile (x+c) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (sub_nonneg.mpr hc.2)] at hx
      change heightCountSecondProfile (min 1 (x+c)) = _
      rw [min_eq_right (by linarith only [hx.2])]
    have hr : (∫ x in (1-c)..1, g x) = ∫ _ in (1-c)..1, heightCountSecondProfile 1 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (sub_le_self 1 hc.1)] at hx
      change heightCountSecondProfile (min 1 (x+c)) = _
      rw [min_eq_left (by linarith only [hx.1])]
    rw [hl,hr,intervalIntegral.integral_comp_add_right,intervalIntegral.integral_const]
    simp only [zero_add,sub_add_cancel,smul_eq_mul]
    ring
  unfold macroscopicGapSecondCoefficient
  rw [intervalIntegral.integral_sub (f := g) (g := heightCountSecondProfile)
    (hg.intervalIntegrable _ _) (continuous_heightCountSecondProfile.intervalIntegrable _ _),
    hcut]
  rw [integral_heightCountSecondProfile (1-c) 1, integral_heightCountSecondProfile c 1,
    integral_heightCountSecondProfile 0 1]
  simp only [heightProfilePrimitive,heightCountSecondProfile,Real.log_one]
  ring

/-- The slope at zero of the macroscopic logarithmic coefficient is twice
the full-height one-point correction. -/
theorem macroscopicGapSecondCoefficient_div_tendsto {c : ℝ → ℝ}
    (hpos : ∀ᶠ T : ℝ in atTop, 0 < c T) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => macroscopicGapSecondCoefficient (c T)/c T)
      atTop (𝓝 (-2*(1+Real.log (2*Real.pi)))) := by
  let a := Real.log (2*Real.pi)
  have hc' : Tendsto c atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hc,hpos.mono (fun _ ht => ht.ne')⟩
  have hd : HasDerivAt (fun x : ℝ => Real.log (1-x)) (-1) 0 := by
    have h := (Real.hasDerivAt_log (show 1-(0:ℝ) ≠ 0 by norm_num)).comp 0
      ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0))
    apply h.congr_deriv
    norm_num
  have hratio : Tendsto (fun x : ℝ => Real.log (1-x)/x) (𝓝[≠] 0) (𝓝 (-1)) := by
    have h := hasDerivAt_iff_tendsto_slope_zero.mp hd
    simpa only [zero_add,sub_zero,Real.log_one,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
  have hrat := hratio.comp hc'
  have hcl : Tendsto (fun T : ℝ => c T*Real.log (c T)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_mul] using
      (Real.continuous_mul_log.continuousAt (x:=0)).tendsto.comp hc
  have hsq := (((tendsto_const_nhds (x:=(1:ℝ))).sub hc).pow 2).neg
  have hlogs := (hsq.mul hrat).sub hcl
  have hpoly := (hlogs.sub (tendsto_const_nhds (x:=(5:ℝ)))).add (hc.const_mul 3)
  have hsp := hpoly.add ((hc.sub (tendsto_const_nhds (x:=(2:ℝ)))).const_mul (2*a))
  have h := hsp.div_const 2
  have hlim : ((-(1-(0:ℝ))^2*(-1)-0-5+3*0)+2*a*(0-2))/2 = -2*(1+a) := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [hpos,hc.eventually_lt_const zero_lt_one] with T hT h1
  rw [macroscopicGapSecondCoefficient_eq ⟨hT.le,h1.le⟩]
  change ((-(1-c T)^2*(Real.log (1-c T)/c T)-c T*Real.log (c T)-5+3*c T) +
    2*a*(c T-2))/2 = _
  dsimp only [a]
  field_simp [hT.ne'] <;> ring

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.macroscopic_gap_second_term' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms macroscopic_gap_second_term

end RiemannResearch.Analysis.MontgomeryPositiveGap
