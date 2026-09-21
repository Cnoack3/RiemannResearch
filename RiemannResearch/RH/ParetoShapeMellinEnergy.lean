import RiemannResearch.RH.MellinModeEnergyBounds

/-!
# Pareto shape and the Mellin certificate threshold

Source: user-provided `RH_Pareto_Capacity_Exact_Bounds_and_Critical_Shape_2026-09-21.md`.
The analytic statements below use the actual power differences and actual Pareto
cell masses. No zeta-zero, RH, or arithmetic provider assumption is used.

-/

noncomputable section
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ShapeCapacity
open RiemannResearch.RH.Pareto.SpectralObstruction

/-- Pareto shape-alpha mass of the positive unit cell `[a,a+1)`. -/
def shapeCellWeight (α a : ℝ) : ℝ := a ^ (-α) - (a + 1) ^ (-α)

theorem shapeCellWeight_pos (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    0 < shapeCellWeight α a := by
  exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg ha (by linarith) (by linarith))

theorem shapeCellWeight_one (n : ℕ) :
    shapeCellWeight 1 ((n : ℝ) + 1) = paretoWeight n := by
  simp only [shapeCellWeight, Real.rpow_neg_one, paretoWeight]
  field_simp
  ring

private theorem power_continuousOn_cell (r a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => x ^ r) (uIcc a (a + 1)) := by
  apply continuousOn_id.rpow_const
  intro x hx
  left
  rw [uIcc_of_le (by linarith)] at hx
  exact (lt_of_lt_of_le ha hx.1).ne'

theorem shapeCellWeight_integral (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    (∫ x in a..a + 1, x ^ (-α - 1)) = shapeCellWeight α a / α := by
  have hzero : (0 : ℝ) ∉ uIcc a (a + 1) := by
    rw [uIcc_of_le (by linarith)]
    intro hz
    exact (not_le_of_gt ha) hz.1
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  rw [show -α - 1 + 1 = -α by ring]
  dsimp only [shapeCellWeight]
  rw [div_neg]
  ring

/-- Weighted Cauchy--Schwarz on the actual shape-alpha cell. -/
theorem shape_power_cell_cauchy (α β a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    (∫ x in a..a + 1, x ^ (-β - 1)) ^ 2 ≤
      (∫ x in a..a + 1, x ^ (α - 2 * β - 1)) * shapeCellWeight α a / α := by
  let f : ℝ → ℝ := fun x => x ^ ((α - 2 * β - 1) / 2)
  let g : ℝ → ℝ := fun x => x ^ ((-α - 1) / 2)
  have hf : ContinuousOn f (uIcc a (a + 1)) := power_continuousOn_cell _ a ha
  have hg : ContinuousOn g (uIcc a (a + 1)) := power_continuousOn_cell _ a ha
  have hf2 : IntervalIntegrable (fun x => (f x) ^ 2) volume a (a + 1) := by
    have heq : f ^ 2 = (fun x => (f x) ^ 2) := by funext x; rfl
    rw [← heq]
    exact (hf.pow 2).intervalIntegrable (μ := volume)
  have hg2 : IntervalIntegrable (fun x => (g x) ^ 2) volume a (a + 1) := by
    have heq : g ^ 2 = (fun x => (g x) ^ 2) := by funext x; rfl
    rw [← heq]
    exact (hg.pow 2).intervalIntegrable (μ := volume)
  have hfg : IntervalIntegrable (fun x => f x * g x) volume a (a + 1) := by
    have heq : f * g = (fun x => f x * g x) := by funext x; rfl
    rw [← heq]
    exact (hf.mul hg).intervalIntegrable (μ := volume)
  have hm : (∫ x in a..a + 1, f x * g x) =
      ∫ x in a..a + 1, x ^ (-β - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only [f, g]
    rw [uIcc_of_le (by linarith)] at hx
    rw [← Real.rpow_add (lt_of_lt_of_le ha hx.1)]
    congr 1
    ring
  have hff : (∫ x in a..a + 1, (f x) ^ 2) =
      ∫ x in a..a + 1, x ^ (α - 2 * β - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only [f]
    rw [uIcc_of_le (by linarith)] at hx
    rw [sq, ← Real.rpow_add (lt_of_lt_of_le ha hx.1)]
    congr 1
    ring
  have hgg : (∫ x in a..a + 1, (g x) ^ 2) = shapeCellWeight α a / α := by
    calc
      _ = ∫ x in a..a + 1, x ^ (-α - 1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only [g]
        rw [uIcc_of_le (by linarith)] at hx
        rw [sq, ← Real.rpow_add (lt_of_lt_of_le ha hx.1)]
        congr 1
        ring
      _ = _ := shapeCellWeight_integral α a hα ha
  let A : ℝ := ∫ x in a..a + 1, (f x) ^ 2
  let B : ℝ := ∫ x in a..a + 1, f x * g x
  let C : ℝ := ∫ x in a..a + 1, (g x) ^ 2
  have hp : 0 ≤ ∫ x in a..a + 1, (C * f x - B * g x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by linarith) (fun x => sq_nonneg _)
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
  have hC : 0 < C := by
    dsimp only [C]
    rw [hgg]
    exact div_pos (shapeCellWeight_pos α a hα ha) hα
  have hcs : B ^ 2 ≤ A * C := sub_nonneg.mp (nonneg_of_mul_nonneg_right hp' hC)
  dsimp only [A, B, C] at hcs
  rw [hm, hff, hgg] at hcs
  simpa only [mul_div_assoc] using hcs

/-- Energy of the actual unnormalized Mellin cell difference. Normalization
by `s` divides this expression by `‖s‖²`. -/
def shapeMellinCellEnergy (α : ℝ) (s : ℂ) (a : ℝ) : ℝ :=
  ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ^ 2 / shapeCellWeight α a

theorem shapeMellinCellEnergy_nonneg (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (ha : 0 < a) : 0 ≤ shapeMellinCellEnergy α s a :=
  div_nonneg (sq_nonneg _) (shapeCellWeight_pos α a hα ha).le

theorem shapeMellinCellEnergy_le_integral (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (hs : 0 < s.re) (ha : 0 < a) :
    shapeMellinCellEnergy α s a ≤
      (‖s‖ ^ 2 / α) * (∫ x in a..a + 1, x ^ (α - 2 * s.re - 1)) := by
  let J : ℝ := ∫ x in a..a + 1, x ^ (-s.re - 1)
  let I : ℝ := ∫ x in a..a + 1, x ^ (α - 2 * s.re - 1)
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
  have hcs : J ^ 2 ≤ I * shapeCellWeight α a / α :=
    shape_power_cell_cauchy α s.re a hα ha
  apply (div_le_iff₀ (shapeCellWeight_pos α a hα ha)).2
  calc
    _ ≤ ‖s‖ ^ 2 * J ^ 2 := hd2
    _ ≤ ‖s‖ ^ 2 * (I * shapeCellWeight α a / α) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by dsimp only [I]; ring

theorem shapeMellinCellEnergy_le_mass (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (hs : 0 < s.re) (ha : 0 < a) (n : ℕ) :
    shapeMellinCellEnergy α s ((n : ℝ) + a) ≤
      (‖s‖ ^ 2 / α) * powerCellMass ((2 * s.re + 1 - α) / 2) a n := by
  have he : -2 * ((2 * s.re + 1 - α) / 2) = α - 2 * s.re - 1 := by ring
  simpa only [powerCellMass, he] using
    shapeMellinCellEnergy_le_integral α s ((n : ℝ) + a) hα hs (by positivity)

/-- The actual dual-energy series is finite whenever `α < 2 Re(s)`. -/
theorem shapeMellinEnergy_summable (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (hs : α < 2 * s.re) (ha : 0 < a) :
    Summable (fun n : ℕ => shapeMellinCellEnergy α s ((n : ℝ) + a)) := by
  apply Summable.of_nonneg_of_le
    (fun n => shapeMellinCellEnergy_nonneg α s _ hα (by positivity))
    (shapeMellinCellEnergy_le_mass α s a hα (by linarith) ha)
    ((powerCellMass_summable ((2 * s.re + 1 - α) / 2) a
      (by linarith) ha).mul_left (‖s‖ ^ 2 / α))

theorem shapeMellinEnergy_le (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (hs : α < 2 * s.re) (ha : 0 < a) :
    (∑' n : ℕ, shapeMellinCellEnergy α s ((n : ℝ) + a)) ≤
      ‖s‖ ^ 2 * a ^ (α - 2 * s.re) / (α * (2 * s.re - α)) := by
  calc
    _ ≤ ∑' n : ℕ, (‖s‖ ^ 2 / α) *
        powerCellMass ((2 * s.re + 1 - α) / 2) a n :=
      Summable.tsum_le_tsum
        (shapeMellinCellEnergy_le_mass α s a hα (by linarith) ha)
        (shapeMellinEnergy_summable α s a hα hs ha)
        ((powerCellMass_summable ((2 * s.re + 1 - α) / 2) a
          (by linarith) ha).mul_left (‖s‖ ^ 2 / α))
    _ = _ := by
      rw [tsum_mul_left, powerCellMass_tsum ((2 * s.re + 1 - α) / 2) a
        (by linarith) ha]
      rw [show 1 - 2 * ((2 * s.re + 1 - α) / 2) = α - 2 * s.re by ring,
        show 2 * ((2 * s.re + 1 - α) / 2) - 1 = 2 * s.re - α by ring]
      field_simp [hα.ne', (sub_pos.mpr hs).ne']

/-- The shape-below-one integral upper bound for the complete physical tail
starting at site two, for every critical-line ordinate. -/
theorem criticalShapeMellinTailEnergy_le (α t : ℝ)
    (hα : 0 < α) (hα1 : α < 1) :
    (∑' n : ℕ, shapeMellinCellEnergy α (MellinFrequency.criticalPoint t)
      ((n : ℝ) + 2)) ≤
      ‖MellinFrequency.criticalPoint t‖ ^ 2 * (2 : ℝ) ^ (α - 1) /
        (α * (1 - α)) := by
  have hs : α < 2 * (MellinFrequency.criticalPoint t).re := by
    simp only [MellinFrequency.criticalPoint_re]
    linarith
  simpa only [MellinFrequency.criticalPoint_re, show 2 * (1 / 2 : ℝ) = 1 by norm_num]
    using shapeMellinEnergy_le α (MellinFrequency.criticalPoint t) 2 hα hs (by norm_num)

theorem shapeMellinCellEnergy_one (s : ℂ) (n : ℕ) :
    shapeMellinCellEnergy 1 s ((n : ℝ) + 1) =
      paretoWeight n * ‖mellinMode s n‖ ^ 2 := by
  have hc : ((n : ℂ) + 1) * ((n : ℂ) + 2) =
      ((((n : ℝ) + 1) * ((n : ℝ) + 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [shapeMellinCellEnergy, shapeCellWeight_one, mellinMode, norm_mul, hc,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  simp only [paretoWeight, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp

/-- At the boundary shape the real cell energy has an unconditional
harmonic lower bound, uniform in the ordinate. -/
theorem criticalShapeMellinCellEnergy_lower (t : ℝ) (n : ℕ) :
    1 / (4 * ((n : ℝ) + 2)) ≤
      shapeMellinCellEnergy 1 (MellinFrequency.criticalPoint t) ((n : ℝ) + 1) := by
  rw [shapeMellinCellEnergy_one]
  exact criticalMode_energy_lower t n

theorem criticalShapeMellinEnergy_not_summable (t : ℝ) :
    ¬ Summable (fun n : ℕ =>
      shapeMellinCellEnergy 1 (MellinFrequency.criticalPoint t) ((n : ℝ) + 1)) := by
  simpa only [shapeMellinCellEnergy_one] using criticalMode_not_summable t

/-- Removing the first cell cannot repair the boundary divergence. -/
theorem criticalShapeMellinTailEnergy_not_summable (t : ℝ) :
    ¬ Summable (fun n : ℕ =>
      shapeMellinCellEnergy 1 (MellinFrequency.criticalPoint t) ((n : ℝ) + 2)) := by
  intro hs
  apply criticalShapeMellinEnergy_not_summable t
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs

/-- The literal normalized certificate `m_s(a)` from the research note. -/
def mellinCellCertificate (s : ℂ) (a : ℝ) : ℂ :=
  ((a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)) / s

theorem normalized_cell_energy_eq (α : ℝ) (s : ℂ) (a : ℝ) :
    ‖mellinCellCertificate s a‖ ^ 2 / shapeCellWeight α a =
      shapeMellinCellEnergy α s a / ‖s‖ ^ 2 := by
  rw [mellinCellCertificate, norm_div, div_pow, shapeMellinCellEnergy]
  ring

theorem normalizedShapeMellinEnergy_summable (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (hs : α < 2 * s.re) (ha : 0 < a) :
    Summable (fun n : ℕ => ‖mellinCellCertificate s ((n : ℝ) + a)‖ ^ 2 /
      shapeCellWeight α ((n : ℝ) + a)) := by
  simp_rw [normalized_cell_energy_eq]
  exact (shapeMellinEnergy_summable α s a hα hs ha).div_const _

theorem normalizedShapeMellinEnergy_le (α : ℝ) (s : ℂ) (a : ℝ)
    (hα : 0 < α) (hs : α < 2 * s.re) (ha : 0 < a) :
    (∑' n : ℕ, ‖mellinCellCertificate s ((n : ℝ) + a)‖ ^ 2 /
      shapeCellWeight α ((n : ℝ) + a)) ≤
      a ^ (α - 2 * s.re) / (α * (2 * s.re - α)) := by
  have hs0 : s ≠ 0 := by
    intro hz
    simp only [hz, Complex.zero_re, mul_zero] at hs
    linarith
  have hn0 : ‖s‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr hs0).ne'
  simp_rw [normalized_cell_energy_eq]
  rw [tsum_div_const]
  calc
    _ ≤ (‖s‖ ^ 2 * a ^ (α - 2 * s.re) / (α * (2 * s.re - α))) / ‖s‖ ^ 2 :=
      div_le_div_of_nonneg_right (shapeMellinEnergy_le α s a hα hs ha) (sq_nonneg _)
    _ = _ := by field_simp [hn0, hα.ne', (sub_pos.mpr hs).ne']

/-- The exact coefficient stated for every Pareto shape below one. -/
theorem criticalNormalizedTailEnergy_le (α t : ℝ)
    (hα : 0 < α) (hα1 : α < 1) :
    (∑' n : ℕ, ‖mellinCellCertificate (MellinFrequency.criticalPoint t)
      ((n : ℝ) + 2)‖ ^ 2 / shapeCellWeight α ((n : ℝ) + 2)) ≤
      (2 : ℝ) ^ (α - 1) / (α * (1 - α)) := by
  have hs : α < 2 * (MellinFrequency.criticalPoint t).re := by
    simp only [MellinFrequency.criticalPoint_re]
    linarith
  simpa only [MellinFrequency.criticalPoint_re, show 2 * (1 / 2 : ℝ) = 1 by norm_num]
    using normalizedShapeMellinEnergy_le α (MellinFrequency.criticalPoint t)
      2 hα hs (by norm_num)

theorem criticalNormalizedTailEnergy_not_summable (t : ℝ) :
    ¬ Summable (fun n : ℕ =>
      ‖mellinCellCertificate (MellinFrequency.criticalPoint t) ((n : ℝ) + 2)‖ ^ 2 /
        shapeCellWeight 1 ((n : ℝ) + 2)) := by
  simp_rw [normalized_cell_energy_eq]
  rw [summable_div_const_iff
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (MellinFrequency.criticalPoint_ne_zero t)))]
  exact criticalShapeMellinTailEnergy_not_summable t

end RiemannResearch.RH.Pareto.ShapeCapacity
