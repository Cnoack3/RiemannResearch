import RiemannResearch.Analysis.ActualZeroDensityCauchyObservation
import RiemannResearch.Analysis.ActualInghamMixedMomentBound
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import Mathlib.Tactic

/-!
# Count the zeros detected by the tilted Cauchy integral

Summing the four-sided estimate over individual copies of the zeros preserves
analytic multiplicity. The existing uniform Cauchy row estimate controls summation
of the critical-line integrals. The second input is the unconditional mixed moment
for the actual zeta function and its finite Möbius mollifier.
-/

noncomputable section
open Complex Filter Set MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier MontgomeryPoisson MontgomeryLocalMass

private theorem continuous_cauchy_row (γ : ℝ) :
    Continuous (fun t : ℝ => cauchyWeight (t - γ)) := by
  unfold cauchyWeight
  exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun x => by dsimp; positivity)

private theorem count_low_copies {T H : ℝ} (h : H ≤ T) :
    (∑ i : Copies T, if (i.1.1).im ≤ H then (1 : ℝ) else 0) = (Ncount 0 H : ℝ) := by
  classical
  rw [← realSum_eq_copies T (fun ρ => if ρ.im ≤ H then (1 : ℝ) else 0)]
  have hef : (cutoff T).filter (fun ρ => ρ.im ≤ H) = cutoff H := by
    ext ρ
    simp only [Finset.mem_filter, mem_cutoff]
    grind
  rw [realSum, count_eq_sum]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hef, Nat.cast_sum]

/-- Sum an observation on the high zeros, retaining the low-height count. -/
theorem count_le_boundary_integral {T H σ W B M a b : ℝ} {f : ℝ → ℝ}
    (hHT : H ≤ T) (hW : 0 ≤ W) (hB : 0 ≤ B) (hab : a ≤ b)
    (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (hrow : ∀ t, (∑ i : Copies T, cauchyWeight (t - copyOrdinate T i)) ≤ M)
    (hobs : ∀ ρ ∈ cutoff T, H < ρ.im → σ ≤ ρ.re →
      W ≤ B + ∫ t in a..b, f t * cauchyWeight (t - ρ.im)) :
    W * rightInclusiveCount T σ ≤ W * (Ncount 0 H : ℝ) + (Ncount 0 T : ℝ) * B +
      M * (∫ t in a..b, f t) := by
  classical
  let k (i : Copies T) (t : ℝ) := cauchyWeight (t - copyOrdinate T i)
  have hk (i : Copies T) : Continuous (k i) := continuous_cauchy_row _
  have hk0 (i : Copies T) (t : ℝ) : 0 ≤ k i t := by dsimp [k,cauchyWeight]; positivity
  have hint (i : Copies T) : IntervalIntegrable (fun t => f t * k i t) volume a b :=
    (hf.mul (hk i)).intervalIntegrable a b
  have hsumI : (∑ i : Copies T, ∫ t in a..b, f t * k i t) ≤ M * ∫ t in a..b, f t := by
    rw [← intervalIntegral.integral_finsetSum (f := fun i t => f t * k i t) (fun i _ => hint i),
      ← intervalIntegral.integral_const_mul M f]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_finsetSum _ fun i _ => hf.mul (hk i)).intervalIntegrable _ _)
      ((continuous_const.mul hf).intervalIntegrable _ _)
    intro t _
    change (∑ i : Copies T, f t * k i t) ≤ M * f t
    rw [← Finset.mul_sum, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hrow t) (hf0 t)
  have hpt (i : Copies T) :
      W * (if σ ≤ i.1.1.re then (1 : ℝ) else 0) ≤
        W * (if i.1.1.im ≤ H then 1 else 0) + B + ∫ t in a..b, f t * k i t := by
    have hi : 0 ≤ ∫ t in a..b, f t * k i t :=
      intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
        (fun t => mul_nonneg (hf0 t) (hk0 i t))
    by_cases hσ : σ ≤ i.1.1.re
    · by_cases hl : i.1.1.im ≤ H
      · simp only [if_pos hσ, if_pos hl, mul_one]; linarith
      · simpa [hσ, hl, k, copyOrdinate] using hobs i.1.1 i.1.2 (lt_of_not_ge hl) hσ
    · by_cases hl : i.1.1.im ≤ H <;> simp [hσ, hl] <;> linarith
  have hall := Finset.sum_le_sum (s := (Finset.univ : Finset (Copies T))) (fun i _ => hpt i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, count_low_copies hHT] at hall
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies] at hall
  rw [rightInclusiveCount, realSum_eq_copies]
  linarith

private theorem critical_error_integral {X : ℕ} {T K : ℝ}
    (hT : 1 ≤ T)
    (hm : (∫ t in (0 : ℝ)..2 * T, ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤
      K * (2 * T) * (Real.log (2 * T)) ^ 2) :
    (∫ t in (1 : ℝ)..2 * T, ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖) ≤
      2 * T + K * (2 * T) * (Real.log (2 * T)) ^ 2 := by
  let A : ℝ → ℝ := fun t => ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖
  have ha : Continuous A := critical_error_continuous X
  have ha0 (t : ℝ) : 0 ≤ A t := norm_nonneg _
  have hp : Continuous (fun t => A t ^ (4 / 3 : ℝ)) := by
    exact ha.rpow_const fun _ => Or.inr (by norm_num)
  have hdom (t : ℝ) : A t ≤ 1 + A t ^ (4 / 3 : ℝ) := by
    by_cases h : A t ≤ 1
    · linarith [Real.rpow_nonneg (ha0 t) (4 / 3 : ℝ)]
    · have he := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by norm_num : (1 : ℝ) ≤ 4 / 3)
      rw [Real.rpow_one] at he
      linarith
  calc
    (∫ t in (1 : ℝ)..2 * T, A t) ≤ ∫ t in (0 : ℝ)..2 * T, A t :=
      intervalIntegral.integral_mono_interval (by norm_num) (by linarith) le_rfl
        (Filter.Eventually.of_forall ha0) (ha.intervalIntegrable _ _)
    _ ≤ ∫ t in (0 : ℝ)..2 * T, 1 + A t ^ (4 / 3 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) (ha.intervalIntegrable _ _)
        ((continuous_const.add hp).intervalIntegrable _ _) (fun t _ => hdom t)
    _ ≤ _ := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hp.intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
      exact add_le_add le_rfl hm

/-- A weak global density estimate for the actual inclusive count, obtained
from the two boundaries of the Möbius mollifier and the actual local zero count. -/
theorem uniformLogLossDensity_quarter_four : UniformLogLossDensity (1 / 4) 4 := by
  obtain ⟨C,hC,hcount⟩ := exists_count_le_height_log
  obtain ⟨R,hR,hrow⟩ := exists_actual_cauchy_row_bound
  obtain ⟨K,hK,hmoment⟩ := exists_actual_critical_error_moment_log_bound
  let e := Real.exp 1
  let G := (26 + 50 * K) * e
  let D := 4 * e * C + 2 * C + 160 * e * C + 5 * R * G
  have he : 0 < e := Real.exp_pos _
  have hG : 0 < G := by dsimp [G]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, Real.exp 16, hD.le, Real.one_lt_exp_iff.mpr (by norm_num), ?_⟩
  intro T ht σ hσ
  let L := (1 / 4 : ℝ) * Real.log T
  let H := Real.exp (2 * L)
  let X := Nat.ceil T
  let W := Real.exp (L * (σ - 1 / 2))
  have hTp : 0 < T := (Real.exp_pos _).trans_le ht
  have hlog : Real.log T = 4 * L := by dsimp [L]; ring
  have hT : T = Real.exp (4 * L) := by rw [← hlog, Real.exp_log hTp]
  have hL : 4 ≤ L := by have hh := Real.log_le_log (Real.exp_pos _) ht; rw [Real.log_exp,hlog] at hh; linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hW : 0 ≤ W := (Real.exp_pos _).le
  have hH9 : 9 ≤ H := by dsimp [H]; linarith [Real.add_one_le_exp (2 * L)]
  have hHT : H ≤ T := by rw [hT]; exact Real.exp_le_exp.mpr (by linarith)
  have hT9 := hH9.trans hHT
  have hX : T ≤ (X : ℝ) := Nat.le_ceil _
  have hX' : (X : ℝ) ≤ 2 * T := by have hh := Nat.ceil_lt_add_one hTp.le; dsimp [X]; linarith
  have hX1 : 1 ≤ X := by exact_mod_cast ((by linarith : (1 : ℝ) ≤ T).trans hX)
  have hlog2T : Real.log (2 * T) ≤ 5 * L := by
    rw [Real.log_mul (by norm_num) hTp.ne', hlog]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogplus : Real.log (T + 3) ≤ 5 * L :=
    (Real.log_le_log (by positivity) (show T + 3 ≤ 2 * T by linarith)).trans hlog2T
  have hpowers (n : ℕ) : 1 ≤ L ^ n := one_le_pow₀ hL1
  have hL4 : L ≤ L ^ 4 := by simpa using
    (pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 4))
  have hct (Z : ℝ) (hZ : 0 ≤ Z) : Z * T * L ≤ Z * T * L ^ 4 :=
    mul_le_mul_of_nonneg_left hL4 (by positivity)
  have hNt : (Ncount 0 T : ℝ) ≤ C * T * (4 * L) := by simpa [hlog] using hcount T hT9
  have hweighted : W * rightInclusiveCount T σ ≤ D * T * L ^ 4 := by
    by_cases hsep : 1 ≤ L * (σ - 1 / 2)
    · let A : ℝ → ℝ := fun t => ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖
      let f : ℝ → ℝ := fun t => 12 * e + L * e * A t
      have hA : Continuous A := critical_error_continuous X
      have hA0 (t : ℝ) : 0 ≤ A t := norm_nonneg _
      have hf : Continuous f := continuous_const.add (continuous_const.mul hA)
      have hf0 (t : ℝ) : 0 ≤ f t := by dsimp [f]; positivity
      have hm : (∫ t in (0 : ℝ)..2 * T, (A t) ^ (4 / 3 : ℝ)) ≤ K * (2 * T) * (Real.log (2 * T)) ^ 2 := by
        simpa only [A, mollifiedError, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat, mul_comm (I : ℂ) _] using
          hmoment (2 * T) (by linarith) X hX1 hX'
      have hiA : (∫ t in (1 : ℝ)..2 * T, A t) ≤ (2 + 50 * K) * T * L ^ 2 := by
        calc
          _ ≤ 2 * T + K * (2 * T) * (Real.log (2 * T)) ^ 2 :=
            critical_error_integral (by linarith) hm
          _ ≤ 2 * T * L ^ 2 + K * (2 * T) * (5 * L) ^ 2 := by
            apply add_le_add
            · exact le_mul_of_one_le_right (by positivity) (hpowers 2)
            · exact mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog2T 2) (by positivity)
          _ = _ := by ring
      have hiF : (∫ t in (1 : ℝ)..2 * T, f t) ≤ G * T * L ^ 3 := by
        change (∫ t in (1 : ℝ)..2 * T, 12 * e + (L * e) * A t) ≤ _
        rw [intervalIntegral.integral_add (f := fun _ : ℝ => 12 * e)
          (g := fun t => (L * e) * A t) intervalIntegrable_const
          ((continuous_const.mul hA).intervalIntegrable _ _), intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, smul_eq_mul]
        calc
          _ ≤ 2 * T * (12 * e) * L ^ 3 + (L * e) * ((2 + 50 * K) * T * L ^ 2) := by
            apply add_le_add
            · exact (mul_le_mul_of_nonneg_right (by linarith : 2 * T - 1 ≤ 2 * T) (by positivity)).trans
                (le_mul_of_one_le_right (by positivity) (hpowers 3))
            · exact mul_le_mul_of_nonneg_left hiA (by positivity)
          _ = _ := by dsimp [G]; ring
      have hobs (ρ : ℂ) (hr : ρ ∈ cutoff T) (hh : H < ρ.im) (hs : σ ≤ ρ.re) :
          W ≤ 40 * e + ∫ t in (1 : ℝ)..2 * T, f t * cauchyWeight (t - ρ.im) := by
        obtain ⟨hz,_,hγ⟩ := mem_cutoff_iff_zeta.mp hr
        have heq := mul_le_mul_of_nonneg_left (sub_le_sub_right hs (1 / 2)) hL0
        exact (Real.exp_le_exp.mpr heq).trans (cauchyDetector_one_zero (by linarith) hT
          hX hX' (hsep.trans heq) (mem_cutoff.mp hr).1.2.2 hh hγ hz)
      have hbase := count_le_boundary_integral hHT hW (by positivity : 0 ≤ 40 * e)
        (by linarith : 1 ≤ 2 * T) hf hf0 (hrow T hTp.le) hobs
      have hWH : W * H ≤ T := by
        rw [hT]; dsimp only [W,H]; rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hσ.2)])
      have hlow : W * (Ncount 0 H : ℝ) ≤ 2 * C * T * L := by
        calc
          _ ≤ W * (C * H * Real.log H) := mul_le_mul_of_nonneg_left (hcount H hH9) hW
          _ = (W * H) * (C * (2 * L)) := by simp [H]; ring
          _ ≤ T * (C * (2 * L)) := mul_le_mul_of_nonneg_right hWH (by positivity)
          _ = _ := by ring
      have hcon : (Ncount 0 T : ℝ) * (40 * e) ≤ 160 * e * C * T * L := by
        calc
          _ ≤ (C * T * (4 * L)) * (40 * e) := mul_le_mul_of_nonneg_right hNt (by positivity)
          _ = _ := by ring
      have hrowterm : (R * Real.log (T + 3)) * (∫ t in (1 : ℝ)..2 * T, f t) ≤ 5 * R * G * T * L ^ 4 := by
        calc
          _ ≤ (R * (5 * L)) * (G * T * L ^ 3) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlogplus hR.le) hiF
              (intervalIntegral.integral_nonneg_of_forall (by linarith) hf0) (by positivity)
          _ = _ := by ring
      calc
        _ ≤ _ := hbase
        _ ≤ 2 * C * T * L ^ 4 + 160 * e * C * T * L ^ 4 + 5 * R * G * T * L ^ 4 :=
          add_le_add (add_le_add (hlow.trans (hct _ (by positivity)))
            (hcon.trans (hct _ (by positivity)))) hrowterm
        _ ≤ _ := by dsimp [D]; nlinarith only [show 0 ≤ (4 * e * C) * T * L ^ 4 by positivity]
    · have hWe : W ≤ e := Real.exp_le_exp.mpr (le_of_not_ge hsep)
      calc
        _ ≤ e * (C * T * (4 * L)) := mul_le_mul hWe ((rightInclusiveCount_le_count T σ).trans hNt)
          (rightInclusiveCount_nonneg _ _) he.le
        _ = (4 * e * C) * T * L := by ring
        _ ≤ (4 * e * C) * T * L ^ 4 := hct _ (by positivity)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hTp.le
          dsimp [D]; linarith [show 0 ≤ 160 * e * C by positivity, show 0 ≤ 5 * R * G by positivity]
  have hLlog : L ^ 4 ≤ (Real.log T) ^ 4 := pow_le_pow_left₀ hL0 (by linarith [hlog]) 4
  have hfinal := hweighted.trans (mul_le_mul_of_nonneg_left hLlog (by positivity : 0 ≤ D * T))
  rw [show (Real.log T) ^ (4 : ℝ) = (Real.log T) ^ 4 by norm_cast,
    show -(1 / 4 * Real.log T) * (σ - 1 / 2) = -(L * (σ - 1 / 2)) by dsimp [L]; ring,
    Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [W, mul_comm (rightInclusiveCount T σ) _] using hfinal)

/-- The multiplicity-weighted sum of squared horizontal displacements of
the actual nontrivial zeta zeros is sublinear in the positive height cutoff. -/
theorem sublinearHorizontalEnergy : SublinearHorizontalEnergy :=
  sublinearHorizontalEnergy_of_logLossDensity (1 / 4) 4 (by norm_num)
    uniformLogLossDensity_quarter_four

end RiemannResearch.Analysis.ActualZeroOrdinate
