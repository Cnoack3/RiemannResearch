import RiemannResearch.RH.CriticalMellinCellAsymptotics
import RiemannResearch.RH.PowerCellMassSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!+# Sharp integral bounds for Mellin-mode energy

Source: the user-provided quantitative Mellin obstruction argument,
21 September 2026. Weighted Cauchy--Schwarz on each unit cell uses the
exact reciprocal-square mass `1 / (a * (a + 1))`.
-/

noncomputable section
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

private theorem interval_mul_integral_sq_le
    {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hgpos : 0 < ∫ x in a..b, (g x) ^ 2) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, (f x) ^ 2) * (∫ x in a..b, (g x) ^ 2) := by
  let A : ℝ := ∫ x in a..b, (f x) ^ 2
  let B : ℝ := ∫ x in a..b, f x * g x
  let C : ℝ := ∫ x in a..b, (g x) ^ 2
  have hf2 : IntervalIntegrable (fun x => (f x) ^ 2) volume a b := by
    have heq : f ^ 2 = (fun x => (f x) ^ 2) := by funext x; rfl
    rw [← heq]
    exact (hf.pow 2).intervalIntegrable (μ := volume)
  have hg2 : IntervalIntegrable (fun x => (g x) ^ 2) volume a b := by
    have heq : g ^ 2 = (fun x => (g x) ^ 2) := by funext x; rfl
    rw [← heq]
    exact (hg.pow 2).intervalIntegrable (μ := volume)
  have hfg : IntervalIntegrable (fun x => f x * g x) volume a b := by
    have heq : f * g = (fun x => f x * g x) := by funext x; rfl
    rw [← heq]
    exact (hf.mul hg).intervalIntegrable (μ := volume)
  have hp : 0 ≤ ∫ x in a..b, (C * f x - B * g x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun x => sq_nonneg _)
  have he : (fun x => (C * f x - B * g x) ^ 2) =
      (fun x => C ^ 2 * (f x) ^ 2 - (2 * C * B) * (f x * g x) +
        B ^ 2 * (g x) ^ 2) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_add
      ((hf2.const_mul _).sub (hfg.const_mul _)) (hg2.const_mul _),
    intervalIntegral.integral_sub (hf2.const_mul _) (hfg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hp
  change 0 ≤ C ^ 2 * A - (2 * C * B) * B + B ^ 2 * C at hp
  have hp' : 0 ≤ C * (A * C - B ^ 2) := by nlinarith only [hp]
  have hC : 0 < C := hgpos
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp' hC)

private theorem positive_cell_excludes_zero {a : ℝ} (ha : 0 < a) :
    (0 : ℝ) ∉ uIcc a (a + 1) := by
  rw [uIcc_of_le (by linarith)]
  intro h
  exact (not_le_of_gt ha) h.1

private theorem rpow_continuousOn_cell (r a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => x ^ r) (uIcc a (a + 1)) := by
  apply continuousOn_id.rpow_const
  intro x hx
  left
  rw [uIcc_of_le (by linarith)] at hx
  exact (lt_of_lt_of_le ha hx.1).ne'

theorem reciprocal_square_cell_integral (a : ℝ) (ha : 0 < a) :
    (∫ x in a..a + 1, x ^ (-2 : ℝ)) = 1 / (a * (a + 1)) := by
  rw [integral_rpow (Or.inr ⟨by norm_num, positive_cell_excludes_zero ha⟩)]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num]
  simp only [Real.rpow_neg_one, div_neg, div_one]
  field_simp [ha.ne', (show a + 1 ≠ 0 by positivity)]
  ring

/-- Cauchy--Schwarz with the reciprocal-square cell weight. -/
theorem real_power_cell_cauchy (β a : ℝ) (ha : 0 < a) :
    (∫ x in a..a + 1, x ^ (-β - 1)) ^ 2 ≤
      (∫ x in a..a + 1, x ^ (-2 * β)) / (a * (a + 1)) := by
  have hf := rpow_continuousOn_cell (-β) a ha
  have hg := rpow_continuousOn_cell (-1) a ha
  have hm : (∫ x in a..a + 1, x ^ (-β) * x ^ (-1 : ℝ)) =
      ∫ x in a..a + 1, x ^ (-β - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le (by linarith)] at hx
    rw [← Real.rpow_add (lt_of_lt_of_le ha hx.1), sub_eq_add_neg]
  have hf2 : (∫ x in a..a + 1, (x ^ (-β)) ^ 2) =
      ∫ x in a..a + 1, x ^ (-2 * β) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le (by linarith)] at hx
    rw [sq, ← Real.rpow_add (lt_of_lt_of_le ha hx.1)]
    congr 1
    ring
  have hg2 : (∫ x in a..a + 1, (x ^ (-1 : ℝ)) ^ 2) =
      1 / (a * (a + 1)) := by
    calc
      _ = ∫ x in a..a + 1, x ^ (-2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [uIcc_of_le (by linarith)] at hx
        rw [sq, ← Real.rpow_add (lt_of_lt_of_le ha hx.1)]
        congr 1
        norm_num
      _ = _ := reciprocal_square_cell_integral a ha
  have hcs := interval_mul_integral_sq_le (show a ≤ a + 1 by linarith) hf hg
    (show 0 < ∫ x in a..a + 1, (x ^ (-1 : ℝ)) ^ 2 by rw [hg2]; positivity)
  rw [hm, hf2, hg2] at hcs
  simpa only [mul_one_div] using hcs

theorem mellin_power_difference_norm_le_integral (s : ℂ) (hs : 0 < s.re)
    (a : ℝ) (ha : 0 < a) :
    ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * (∫ x in a..a + 1, x ^ (-s.re - 1)) := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have he : -s - 1 ≠ (-1 : ℂ) := by
    intro h
    apply hs0
    linear_combination -h
  have hid : (a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s) =
      s * (∫ x : ℝ in a..a + 1, (x : ℂ) ^ (-s - 1)) := by
    rw [integral_cpow (Or.inr ⟨he, positive_cell_excludes_zero ha⟩)]
    rw [show -s - 1 + 1 = -s by ring]
    field_simp [hs0]
    ring
  rw [hid, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
  calc
    _ ≤ ∫ x in a..a + 1, ‖(x : ℂ) ^ (-s - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [uIcc_of_le (by linarith)] at hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hx.1)]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]

/-- The sharp energy estimate for one actual Mellin difference. -/
theorem mellin_power_difference_energy_cell_le (s : ℂ) (hs : 0 < s.re)
    (a : ℝ) (ha : 0 < a) :
    a * (a + 1) * ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ^ 2 ≤
      ‖s‖ ^ 2 * (∫ x in a..a + 1, x ^ (-2 * s.re)) := by
  let J : ℝ := ∫ x in a..a + 1, x ^ (-s.re - 1)
  let M : ℝ := ∫ x in a..a + 1, x ^ (-2 * s.re)
  have hJ : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    exact Real.rpow_nonneg (le_trans ha.le hx.1) _
  have hd := mellin_power_difference_norm_le_integral s hs a ha
  have hd2 : ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ^ 2 ≤
      ‖s‖ ^ 2 * J ^ 2 := by
    change ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * J at hd
    nlinarith [norm_nonneg ((a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)),
      mul_nonneg (norm_nonneg s) hJ]
  have hcs : J ^ 2 ≤ M / (a * (a + 1)) := real_power_cell_cauchy s.re a ha
  calc
    _ ≤ a * (a + 1) * (‖s‖ ^ 2 * J ^ 2) :=
      mul_le_mul_of_nonneg_left hd2 (by positivity)
    _ ≤ a * (a + 1) * (‖s‖ ^ 2 * (M / (a * (a + 1)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcs (sq_nonneg _)) (by positivity)
    _ = _ := by
      dsimp only [M]
      field_simp [ha.ne', (show a + 1 ≠ 0 by positivity)]

theorem mellinMode_energy_cell_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    paretoWeight n * ‖mellinMode s n‖ ^ 2 ≤
      ‖s‖ ^ 2 * (∫ x in (n : ℝ) + 1..(n : ℝ) + 2, x ^ (-2 * s.re)) := by
  have h := mellin_power_difference_energy_cell_le s hs ((n : ℝ) + 1) (by positivity)
  have he : paretoWeight n * ‖mellinMode s n‖ ^ 2 =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) *
        ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
          (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s)‖ ^ 2 := by
    have hc : ((n : ℂ) + 1) * ((n : ℂ) + 2) =
        ((((n : ℝ) + 1) * ((n : ℝ) + 2) : ℝ) : ℂ) := by push_cast; rfl
    rw [mellinMode, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    simp only [paretoWeight, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    field_simp
  rw [he]
  simpa only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using h

private theorem mellinMode_energy_le_powerCellMass (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    paretoWeight n * ‖mellinMode s n‖ ^ 2 ≤ ‖s‖ ^ 2 * powerCellMass s.re 1 n := by
  simpa only [powerCellMass, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    using mellinMode_energy_cell_le s hs n

private theorem mellinMode_tail_energy_le_powerCellMass (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    paretoWeight (n + 1) * ‖mellinMode s (n + 1)‖ ^ 2 ≤
      ‖s‖ ^ 2 * powerCellMass s.re 2 n := by
  have hlo : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have hhi : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 2 + 1 := by push_cast; ring
  simpa only [powerCellMass, hlo, hhi] using mellinMode_energy_cell_le s hs (n + 1)

/-- Every Mellin mode strictly to the right of the critical line has finite energy. -/
theorem mellinMode_energy_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun n : ℕ => paretoWeight n * ‖mellinMode s n‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => by unfold paretoWeight; positivity)
    (mellinMode_energy_le_powerCellMass s (by linarith))
    ((powerCellMass_summable s.re 1 hs (by norm_num)).mul_left (‖s‖ ^ 2))

/-- Sharp integral upper bound for the full actual Mellin energy. -/
theorem mellinMode_energy_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n : ℕ, paretoWeight n * ‖mellinMode s n‖ ^ 2) ≤
      ‖s‖ ^ 2 / (2 * s.re - 1) := by
  calc
    _ ≤ ∑' n : ℕ, ‖s‖ ^ 2 * powerCellMass s.re 1 n :=
      Summable.tsum_le_tsum (mellinMode_energy_le_powerCellMass s (by linarith))
        (mellinMode_energy_summable s hs)
        ((powerCellMass_summable s.re 1 hs (by norm_num)).mul_left (‖s‖ ^ 2))
    _ = _ := by
      rw [tsum_mul_left, powerCellMass_tsum s.re 1 hs (by norm_num), Real.one_rpow]
      ring

theorem mellinMode_tail_energy_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun n : ℕ => paretoWeight (n + 1) * ‖mellinMode s (n + 1)‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => by unfold paretoWeight; positivity)
    (mellinMode_tail_energy_le_powerCellMass s (by linarith))
    ((powerCellMass_summable s.re 2 hs (by norm_num)).mul_left (‖s‖ ^ 2))

/-- The tail begins at physical index two; its integral mass is `2^(1-2*Re(s))`. -/
theorem mellinMode_tail_energy_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n : ℕ, paretoWeight (n + 1) * ‖mellinMode s (n + 1)‖ ^ 2) ≤
      ‖s‖ ^ 2 * Real.rpow 2 (1 - 2 * s.re) / (2 * s.re - 1) := by
  calc
    _ ≤ ∑' n : ℕ, ‖s‖ ^ 2 * powerCellMass s.re 2 n :=
      Summable.tsum_le_tsum (mellinMode_tail_energy_le_powerCellMass s (by linarith))
        (mellinMode_tail_energy_summable s hs)
        ((powerCellMass_summable s.re 2 hs (by norm_num)).mul_left (‖s‖ ^ 2))
    _ = _ := by
      rw [tsum_mul_left, powerCellMass_tsum s.re 2 hs (by norm_num)]
      change ‖s‖ ^ 2 * ((2 : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)) =
        ‖s‖ ^ 2 * (2 : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)
      ring

end RiemannResearch.RH.Pareto.SpectralObstruction
