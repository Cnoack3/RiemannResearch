import RiemannResearch.Analysis.ActualInghamCauchyObservation
import RiemannResearch.Analysis.ActualInghamRightMoment
import RiemannResearch.Analysis.ActualInghamMixedMomentBound
import RiemannResearch.Analysis.ActualZeroCauchyDensity
import RiemannResearch.Analysis.ActualSelbergDyadicAssembly
import RiemannResearch.Analysis.ActualSelbergIngham
import Mathlib.Tactic

/-!
# Ingham's uniform zero-density bound for the actual inclusive count

For q = 3(1-σ)/(2-σ) the two-edge Cauchy detector gives
N(σ,T) ≪ (T/log T)^q (log T)^5, uniformly on the closed half strip.
The classical statement and the two moment orders are discussed in Chourasiya
and Simonič, https://arxiv.org/abs/2507.15184. The proof here uses the signed
Cauchy rectangle at the individual zeros and the actual local multiplicity bound.
-/

noncomputable section
open Complex Filter Set MeasureTheory Zeta23
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier MontgomeryPoisson MontgomeryLocalMass

private theorem balanced_tilt {Y σ : ℝ} (hY : 1 ≤ Y) (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    let q := 3 * (1 - σ) / (2 - σ)
    let L := 3 * Real.log Y / (2 * (2 - σ))
    0 ≤ L ∧ L ≤ 2 * Real.log Y ∧ 1 ≤ Y ^ q ∧
      Y * Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ))) = Y ^ q ∧
      Real.exp (2 * (L * (1 - σ))) = Y ^ q := by
  dsimp only
  have hp : 0 < Y := by linarith
  have hden : 0 < 2 - σ := by linarith [hσ.2]
  have hlog := Real.log_nonneg hY
  have hu : 1 ≤ 2 - σ := by linarith [hσ.2]
  refine ⟨by positivity, (div_le_iff₀ (by positivity)).mpr ?_,
    Real.one_le_rpow hY (div_nonneg (by linarith [hσ.2]) hden.le), ?_, ?_⟩
  · nlinarith [mul_nonneg hlog (sub_nonneg.mpr hu)]
  · rw [Real.rpow_def_of_pos hp]
    conv_lhs => lhs; rw [← Real.exp_log hp]
    rw [← Real.exp_add]; congr 1; field_simp; ring
  · rw [Real.rpow_def_of_pos hp]
    congr 1
    field_simp [hden.ne']

private theorem actual_two_endpoint_moments {T ℓ : ℝ} {X : ℕ} {K : ℝ}
    (hℓ : 1 ≤ ℓ) (hT : 2 ≤ T) (hX : T ≤ (X : ℝ)) (hX' : (X : ℝ) ≤ 2 * T)
    (hlog : Real.log (2 * T) ≤ 2 * ℓ)
    (hleft : (∫ t in (0 : ℝ)..2 * T,
      ‖riemannZeta ((1 / 2 : ℂ) + I * t) * mollifier X ((1 / 2 : ℂ) + I * t) - 1‖ ^ (4 / 3 : ℝ))
        ≤ K * (2 * T) * (Real.log (2 * T)) ^ 2) (hK : 0 ≤ K) :
    let d := 1 / Real.log (X : ℝ)
    (∫ t in (1 : ℝ)..2 * T, ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ))
        ≤ 8 * K * T * ℓ ^ 2 ∧
    (∫ t in (1 : ℝ)..2 * T, ‖mollifiedError X (((1 + d : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 81 * movingRightMomentConstant 1 * ℓ ^ 3 := by
  dsimp only
  have hX2 : 2 ≤ X := by exact_mod_cast hT.trans hX
  have hXp : 0 < (X : ℝ) := by linarith
  have hR := actual_moving_right_error_moment_log_cube_le (δ := 1) (by norm_num)
    hX2 (H := 1) (T := 2 * T) (by linarith)
  have hR0 := (movingRightMomentConstant_pos (by norm_num : (0 : ℝ) < 1)).le
  constructor
  · have hc := (critical_error_continuous X).rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4 / 3))
    have hpos (t : ℝ) : 0 ≤ ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) := by
      positivity
    have hmono := intervalIntegral.integral_mono_interval (μ := volume)
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 2 * T) (le_refl (2 * T))
      (Filter.Eventually.of_forall hpos) (hc.intervalIntegrable 0 (2 * T))
    refine hmono.trans ((by simpa only [mollifiedError, mul_comm I _] using hleft :
      (∫ t in (0 : ℝ)..2 * T, ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ _)
        |>.trans ?_)
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 2) (show 0 ≤ K * (2 * T) by positivity)
    linarith
  · have hfrac : (2 * T - 1) / (X : ℝ) ≤ 2 := (div_le_iff₀ hXp).mpr (by linarith)
    have hXlog := (Real.log_le_log hXp hX').trans hlog
    have hpow := pow_le_pow_left₀ (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ X by linarith)] :
      0 ≤ 1 + Real.log (X : ℝ)) (show 1 + Real.log (X : ℝ) ≤ 3 * ℓ by linarith) 3
    have hmul := mul_le_mul
      (mul_le_mul_of_nonneg_left (show 1 + (2 * T - 1) / (X : ℝ) ≤ 3 by linarith) hR0)
      hpow (pow_nonneg (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ X by linarith)]) _)
      (by positivity)
    simp only [mollifiedError, mul_comm I _] at hR ⊢
    exact hR.trans (by linarith)

private theorem sum_two_edge_moments {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B)
    {s r K J T ℓ P U V : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hℓ : 0 ≤ ℓ)
    (ha : (∫ t in (1 : ℝ)..2 * T, A t) ≤ K * T * ℓ ^ 2)
    (hb : (∫ t in (1 : ℝ)..2 * T, B t) ≤ J * ℓ ^ 3)
    (hsl : s * T ≤ U * P * ℓ ^ 2) (hsr : r ≤ V * P * ℓ) :
    (∫ t in (1 : ℝ)..2 * T, 2 * (s * A t + r * B t)) ≤ 2 * (U * K + V * J) * P * ℓ ^ 4 := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (f := fun t => s * A t) (g := fun t => r * B t)
    ((continuous_const.mul hA).intervalIntegrable _ _)
    ((continuous_const.mul hB).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hl := mul_le_mul_of_nonneg_left ha hs
  have hl' := mul_le_mul_of_nonneg_right hsl (show 0 ≤ K * ℓ ^ 2 by positivity)
  have hrr := mul_le_mul_of_nonneg_left hb hr
  have hr' := mul_le_mul_of_nonneg_right hsr (show 0 ≤ J * ℓ ^ 3 by positivity)
  linarith

/-- A uniform logarithmic refinement of the fifth-power formulation.
All zeros in the closed right half-plane are counted with analytic multiplicity. -/
theorem exists_ingham_density_log_profile :
    ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      rightInclusiveCount T σ ≤
        C * (T / Real.log T) ^ (3 * (1 - σ) / (2 - σ)) * (Real.log T) ^ 5 := by
  obtain ⟨C, hC, hcount⟩ := exists_count_le_height_log
  obtain ⟨R, hR, hrow⟩ := exists_actual_cauchy_row_bound
  obtain ⟨K, hK, hm⟩ := exists_actual_critical_error_moment_log_bound
  let J := movingRightMomentConstant 1
  let S := 32 * Real.exp 1
  let U := 2 * S ^ (4 / 3 : ℝ)
  let V := 2 * S ^ 2 * Real.exp 4
  let G := 2 * (U * (8 * K) + V * (81 * J))
  let D := C * Real.exp 3 + 5 * C + 2 * R * G
  have hJ : 0 < J := movingRightMomentConstant_pos (by norm_num)
  have hS : 0 < S := by dsimp [S]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, Real.exp 16, hD.le, Real.one_lt_exp_iff.mpr (by norm_num), ?_⟩
  intro T hT σ hσ
  let ℓ := Real.log T
  let Y := T / ℓ
  let q := 3 * (1 - σ) / (2 - σ)
  let L := 3 * Real.log Y / (2 * (2 - σ))
  let P := Y ^ q
  let H := 1 + 4 * ℓ
  let X := Nat.ceil T
  let d := 1 / Real.log (X : ℝ)
  have hTp := (Real.exp_pos 16).trans_le hT
  have heT : T = Real.exp ℓ := (Real.exp_log hTp).symm
  have hℓ : 16 ≤ ℓ := by have h := Real.log_le_log (Real.exp_pos 16) hT; simpa [ℓ] using h
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓp : 0 < ℓ := by linarith
  have hbig : H ≤ T := by
    have h := Real.add_one_le_exp (ℓ / 2)
    have h2 := mul_self_le_mul_self (show 0 ≤ ℓ / 2 + 1 by linarith) h
    rw [← Real.exp_add, show ℓ / 2 + ℓ / 2 = ℓ by ring, ← heT] at h2
    dsimp [H]; nlinarith [mul_nonneg hℓp.le (show 0 ≤ ℓ - 16 by linarith)]
  have hT9 : 9 ≤ T := by dsimp [H] at hbig; linarith
  have hX : T ≤ (X : ℝ) := Nat.le_ceil _
  have hX' : (X : ℝ) ≤ 2 * T := by
    have hh := Nat.ceil_lt_add_one hTp.le
    dsimp [X]; linarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hXp : 0 < (X : ℝ) := by linarith
  have hlog2 : Real.log (2 * T) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hTp.ne']
    change Real.log 2 + ℓ ≤ 2 * ℓ
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hxlo : ℓ ≤ Real.log (X : ℝ) := Real.log_le_log hTp hX
  have hxhi := (Real.log_le_log hXp hX').trans hlog2
  have hxlog : 0 < Real.log (X : ℝ) := hℓp.trans_le hxlo
  have hd : 0 < d := one_div_pos.mpr hxlog
  have hdinv : 1 / d = Real.log (X : ℝ) := by simp [d]
  have hdsmall : ℓ * d ≤ 1 := by dsimp [d]; rw [mul_one_div]; exact (div_le_one hxlog).mpr hxlo
  have hdhalf : d ≤ 1 / 2 := by
    dsimp [d]
    exact (div_le_div_iff₀ hxlog (by norm_num)).mpr (by linarith)
  have hTY : T = Y * ℓ := by dsimp [Y]; field_simp
  have hY : 1 ≤ Y := (one_le_div hℓp).mpr (by dsimp [H] at hbig; linarith)
  have hYT : Y ≤ T := div_le_self hTp.le hℓ1
  obtain ⟨hL, hLY, hP, hleft, hright⟩ := balanced_tilt hY hσ
  change 0 ≤ L at hL
  change L ≤ 2 * Real.log Y at hLY
  change 1 ≤ P at hP
  change Y * Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ))) = P at hleft
  change Real.exp (2 * (L * (1 - σ))) = P at hright
  have hP0 : 0 ≤ P := by linarith
  have hLT : L ≤ 2 * ℓ := by
    have hh : Real.log Y ≤ ℓ := Real.log_le_log (by linarith) hYT
    linarith
  have hLd : L * d ≤ 2 := by linarith [mul_le_mul_of_nonneg_right hLT hd.le]
  have hscale : T * Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ))) = P * ℓ := by
    calc
      _ = (Y * Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ)))) * ℓ := by rw [hTY]; ring
      _ = _ := by rw [hleft]
  have hℓ25 : ℓ ^ 2 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ1 (by decide : 2 ≤ 5)
  change rightInclusiveCount T σ ≤ D * P * ℓ ^ 5
  by_cases hsep : d ≤ σ - 1 / 2
  · let b := 1 + d
    let A (t : ℝ) := ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)
    let B (t : ℝ) := ‖mollifiedError X ((b : ℂ) + (t : ℂ) * I)‖ ^ 2
    let s := (S * Real.exp (L * (1 / 2 - σ))) ^ (4 / 3 : ℝ) / d
    let r := (S * Real.exp (L * (b - σ))) ^ 2 / d
    let f (t : ℝ) := 2 * (s * A t + r * B t)
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hA : Continuous A :=
      (critical_error_continuous X).rpow_const (fun _ => Or.inr (by norm_num))
    have hB : Continuous B :=
      (vertical_error_continuous X (show b ≠ 1 by dsimp [b]; linarith)).pow 2
    have hf : Continuous f :=
      continuous_const.mul ((continuous_const.mul hA).add (continuous_const.mul hB))
    have hf0 (t : ℝ) : 0 ≤ f t := by dsimp [f, A, B]; positivity
    have hsl : s * T ≤ U * P * ℓ ^ 2 := by
      have eh : (Real.exp (L * (1 / 2 - σ))) ^ (4 / 3 : ℝ) =
          Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ))) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
      dsimp only [s, U]
      rw [Real.mul_rpow hS.le (Real.exp_pos _).le, eh]
      calc
        _ = S ^ (4 / 3 : ℝ) * (T * Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ)))) * (1 / d) := by ring
        _ ≤ S ^ (4 / 3 : ℝ) * (P * ℓ) * (2 * ℓ) := by
          rw [hscale, hdinv]; exact mul_le_mul_of_nonneg_left hxhi (by positivity)
        _ = _ := by ring
    have hsr : r ≤ V * P * ℓ := by
      have eh : (Real.exp (L * (b - σ))) ^ 2 = P * Real.exp (2 * (L * d)) := by
        rw [sq,← Real.exp_add,← hright,← Real.exp_add]; congr 1; dsimp [b]; ring
      dsimp only [r, V]; rw [mul_pow, eh]
      have hh : Real.exp (2 * (L * d)) ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith)
      calc
        _ = S ^ 2 * P * Real.exp (2 * (L * d)) * (1 / d) := by ring
        _ ≤ S ^ 2 * P * Real.exp 4 * (2 * ℓ) := by
          rw [hdinv]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity))
            hxhi hxlog.le (by positivity)
        _ = _ := by ring
    obtain ⟨ha, hb⟩ := actual_two_endpoint_moments hℓ1 (by linarith : 2 ≤ T) hX hX' hlog2
      (hm (2 * T) (by linarith) X hX1 hX') hK.le
    have hif : (∫ t in (1 : ℝ)..2 * T, f t) ≤ G * P * ℓ ^ 4 :=
      sum_two_edge_moments hA hB hs hr (by positivity : 0 ≤ 8 * K) (by positivity : 0 ≤ 81 * J)
        hℓp.le ha hb hsl hsr
    have obs (ρ : ℂ) (hρ : ρ ∈ cutoff T) (hl : H < ρ.im) (hsig : σ ≤ ρ.re) :
        (1 : ℝ) ≤ 0 + ∫ t in (1 : ℝ)..2 * T, f t * cauchyWeight (t - ρ.im) := by
      obtain ⟨hz, _, hh⟩ := mem_cutoff_iff_zeta.mp hρ
      simpa only [zero_add] using ingham_two_edge_observation hℓ heT hbig hL hLT hX'
        hd hdhalf hsep hsig (mem_cutoff.mp hρ).1.2.2 hl hh hz
    have hcounted := count_le_boundary_integral hbig (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 0) (by linarith : 1 ≤ 2 * T) hf hf0 (hrow T hTp.le) obs
    simp only [one_mul, mul_zero, add_zero] at hcounted
    have hH9 : 9 ≤ H := by dsimp [H]; linarith
    have hH' : H ≤ 5 * ℓ := by dsimp [H]; linarith
    have hlogH : Real.log H ≤ ℓ := Real.log_le_log (by linarith) hbig
    have hhead : (Ncount 0 H : ℝ) ≤ 5 * C * P * ℓ ^ 5 := by
      refine (hcount H hH9).trans ?_
      have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hH' hC.le) hlogH
        (Real.log_nonneg (by linarith)) (show 0 ≤ C * (5 * ℓ) by positivity)
      have hh := mul_le_mul (show 5 * C ≤ 5 * C * P from le_mul_of_one_le_right (by positivity) hP)
        hℓ25 (sq_nonneg _) (by positivity)
      linarith
    have hlogR : Real.log (T + 3) ≤ 2 * ℓ :=
      (Real.log_le_log (by positivity) (show T + 3 ≤ 2 * T by linarith)).trans hlog2
    have hrowTerm := mul_le_mul (mul_le_mul_of_nonneg_left hlogR hR.le) hif
      (intervalIntegral.integral_nonneg_of_forall (by linarith : 1 ≤ 2 * T) hf0)
      (show 0 ≤ R * (2 * ℓ) by positivity)
    dsimp only [D]
    linarith [show 0 ≤ C * Real.exp 3 * P * ℓ ^ 5 by positivity]
  · have hsmall : L * (σ - 1 / 2) ≤ 2 :=
      (mul_le_mul_of_nonneg_left (le_of_not_ge hsep) hL).trans hLd
    have he : Real.exp ((4 / 3 : ℝ) * (L * (σ - 1 / 2))) ≤ Real.exp 3 :=
      Real.exp_le_exp.mpr (by linarith)
    have hsmallT : T ≤ P * ℓ * Real.exp 3 := by
      calc
        _ = (T * Real.exp ((4 / 3 : ℝ) * (L * (1 / 2 - σ)))) *
            Real.exp ((4 / 3 : ℝ) * (L * (σ - 1 / 2))) := by
          rw [mul_assoc,← Real.exp_add]; ring_nf; simp
        _ ≤ _ := by rw [hscale]; exact mul_le_mul_of_nonneg_left he (by positivity)
    refine (rightInclusiveCount_le_count T σ).trans ((hcount T hT9).trans ?_)
    change C * T * ℓ ≤ _
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmallT hC.le) hℓp.le
    have hh' := mul_le_mul_of_nonneg_left hℓ25 (show 0 ≤ C * Real.exp 3 * P by positivity)
    have hcomp : C * Real.exp 3 ≤ D := by dsimp [D]; linarith [show 0 ≤ 2 * R * G by positivity]
    have hfin := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcomp hP0)
      (show 0 ≤ ℓ ^ 5 by positivity)
    linarith

/-- For every height at least two the actual inclusive count satisfies both the
total-count estimate and the refined density estimate, with one constant. -/
theorem exists_ingham_density_all_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      let q := 3 * (1 - σ) / (2 - σ)
      rightInclusiveCount T σ ≤ C * min (T * Real.log T)
        (T ^ q * (Real.log T) ^ (5 - q)) := by
  obtain ⟨B, H, hB, _, hb⟩ := exists_ingham_density_log_profile
  obtain ⟨A, hA, ha⟩ := exists_count_le_height_log
  let Z := max H 9
  let m := min (Real.log 2) ((Real.log 2) ^ 5)
  let F := (Ncount 0 Z : ℝ) / m
  let C := max (max A B) F
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm : 0 < m := lt_min hlog₂ (pow_pos hlog₂ _)
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_left _ _)
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_left _ _)
  have hC := hA.trans_le hAC
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  let q := 3 * (1 - σ) / (2 - σ)
  have hTp : 0 < T := by linarith
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hLp := hlog₂.trans_le hlog
  have hq : 0 ≤ q := div_nonneg (by linarith [hσ.2]) (by linarith [hσ.2])
  have hpow : 1 ≤ (T / Real.log T) ^ q :=
    Real.one_le_rpow ((one_le_div hLp).mpr (by linarith [Real.log_le_sub_one_of_pos hTp])) hq
  have heq : T ^ q * (Real.log T) ^ (5 - q) = (T / Real.log T) ^ q * (Real.log T) ^ 5 := by
    rw [Real.rpow_sub hLp, Real.div_rpow hTp.le hLp.le,
      show (Real.log T) ^ (5 : ℝ) = (Real.log T) ^ (5 : ℕ) by norm_cast]
    ring
  change rightInclusiveCount T σ ≤ C * min (T * Real.log T) (T ^ q * _)
  rw [heq, mul_min_of_nonneg _ _ hC.le]
  by_cases hlarge : Z ≤ T
  · refine le_min ?_ ?_
    · have ht := ha T ((le_max_right H 9).trans hlarge)
      exact (rightInclusiveCount_le_count T σ).trans (ht.trans (by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hTp.le) hLp.le))
    · have ht := hb T ((le_max_left H 9).trans hlarge) σ hσ
      exact ht.trans (by rw [← mul_assoc]; gcongr)
  · have hfinite : rightInclusiveCount T σ ≤ F * m := by
      rw [show F * m = (Ncount 0 Z : ℝ) from div_mul_cancel₀ _ hm.ne']
      exact (rightInclusiveCount_monotone_height σ (le_of_not_ge hlarge)).trans
        (rightInclusiveCount_le_count _ _)
    have hbase : F * m ≤ C * m :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hm.le
    refine hfinite.trans (hbase.trans (le_min ?_ ?_))
    · apply mul_le_mul_of_nonneg_left _ hC.le
      exact ((min_le_left _ _).trans hlog).trans (le_mul_of_one_le_left hLp.le (by linarith))
    · apply mul_le_mul_of_nonneg_left _ hC.le
      exact ((min_le_right _ _).trans (pow_le_pow_left₀ hlog₂.le hlog 5)).trans
        (le_mul_of_one_le_left (pow_nonneg hLp.le _) hpow)

/-- The classical Ingham proposition, with a single constant and threshold for
every real part in the closed half strip. -/
theorem inghamDensityBound : InghamDensityBound := by
  obtain ⟨C, H, hC, hH, h⟩ := exists_ingham_density_log_profile
  refine ⟨C, max H (Real.exp 1), hC, hH.trans_le (le_max_left _ _), ?_⟩
  intro T hT σ hσ
  have ht := (le_max_right H (Real.exp 1)).trans hT
  have hp := (Real.exp_pos 1).trans_le ht
  have hl : 1 ≤ Real.log T := by simpa using Real.log_le_log (Real.exp_pos 1) ht
  have hq : 0 ≤ 3 * (1 - σ) / (2 - σ) := div_nonneg (by linarith [hσ.2]) (by linarith [hσ.2])
  exact (h T ((le_max_left _ _).trans hT) σ hσ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hp.le (by linarith)) (div_le_self hp.le hl) hq) hC)
      (pow_nonneg (by linarith) _))

/-- Away from the critical line the inclusive dyadic count has a single
logarithm for every slope strictly below the fixed-strip threshold. -/
theorem exists_selberg_far_windows_on_fixed_strip {a η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 2) (ha : a < 4 / (3 - 2 * η)) :
    ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ σ ∈ Icc (1 / 2 + η) 1,
      rightInclusiveWindow (T / 2) T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T :=
  exists_selberg_far_windows_of_ingham_sharp ha hη hη' inghamDensityBound

end RiemannResearch.Analysis.ActualZeroOrdinate

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_density_log_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_density_log_profile

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.inghamDensityBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.inghamDensityBound

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_density_all_heights' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_density_all_heights
