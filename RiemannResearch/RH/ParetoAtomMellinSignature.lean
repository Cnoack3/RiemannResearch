import RiemannResearch.Analysis.MellinNormalizedResidue
import RiemannResearch.RH.ParetoUnscaledDilation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Mellin and zeta signatures of the literal normalized Pareto atoms

The atom is `(k % d) / d`, embedded in the actual Pareto Hilbert space.
The Mellin transform is the existing Bochner integral of its physical step
sequence. Its all-positive-half-plane arithmetic identity includes the
removable point `s = 1`. No zeta identity or continuation is an assumption.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace RiemannResearch.RH.ParetoAtomMellinSignature

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ZetaConductorRegularization

/-- The actual physical step atom is the corrected Beurling fractional-part atom. -/
theorem normalizedAtom_floor_eq_corrected_fract (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    normalizedAtom d ⌊x⌋₊ = Int.fract (x / (d : ℝ)) - Int.fract x / (d : ℝ) := by
  have hfloor : (⌊x⌋₊ : ℤ) = ⌊x⌋ := Int.natCast_floor_eq_floor hx
  have he : Int.fract (x / (d : ℝ)) - Int.fract x / (d : ℝ) =
      Int.fract ((⌊x⌋₊ : ℝ) / (d : ℝ)) := by
    unfold Int.fract
    rw [Int.floor_div_natCast x d, Int.floor_div_natCast (⌊x⌋₊ : ℝ) d,
      Int.floor_natCast, ← hfloor]
    simp only [Int.cast_natCast]
    ring
  rw [he, Int.fract_div_natCast_eq_div_natCast_mod]
  rfl

/-- Absolute integrability of the corrected atom on the full positive half-plane. -/
theorem corrected_fract_integrable (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      ((Int.fract (x / (d : ℝ)) - Int.fract x / (d : ℝ) : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hmeas : Measurable (fun x : ℝ => (normalizedAtom d ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) := by
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_of_countable (normalizedAtom d)).comp Nat.measurable_floor)).mul
      (Complex.continuous_ofReal.measurable.pow_const (-s - 1))
  have hi := integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)
  have hstep : IntegrableOn (fun x : ℝ => (normalizedAtom d ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
    apply hi.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    calc
      _ ≤ 1 * x ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right (normalizedAtom_abs_le_one d ⌊x⌋₊ hd)
          (Real.rpow_nonneg hx0.le _)
      _ = _ := one_mul _
  apply hstep.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [normalizedAtom_floor_eq_corrected_fract d x (le_of_lt (lt_trans zero_lt_one hx))]

/-- Actual integral equals the pole-removed zeta expression, also at `s = 1`. -/
theorem paretoMellin_normalizedResidue_conductor (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (normalizedResidueHilbert d hd) s = conductorZeta d s / s := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  have hraw := normalizedResidue_mellin_conductor d hd s hs
  rw [nymanConductorLFunction_eq_conductorZeta] at hraw
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  apply (eq_div_iff hs0).mpr
  simpa only [mul_comm] using hraw

/-- The corrected fractional-part Mellin integral includes the removable point. -/
theorem corrected_fract_integral_eq_conductor (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ),
      ((Int.fract (x / (d : ℝ)) - Int.fract x / (d : ℝ) : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 1)) = conductorZeta d s / s := by
  rw [← paretoMellin_normalizedResidue_conductor d hd s hs,
    paretoMellin_eq_step_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [normalizedResidueHilbert_sequence]
  change _ = (normalizedAtom d ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)
  rw [normalizedAtom_floor_eq_corrected_fract d x (le_of_lt (lt_trans zero_lt_one hx))]

/-- The normalized atom has exactly the corrected integer Beurling signature. -/
theorem paretoMellin_normalizedResidue_zeta (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    paretoMellin (normalizedResidueHilbert d hd) s =
      riemannZeta s / s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) := by
  rw [paretoMellin_normalizedResidue_conductor d hd s hs,
    conductorZeta_of_ne_one d hs1, conductorSymbol_eq_cpow d hd]
  ring

/-- The classical corrected fractional-part formula uses the actual analytic zeta. -/
theorem corrected_fract_integral_eq_zeta (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ),
      ((Int.fract (x / (d : ℝ)) - Int.fract x / (d : ℝ) : ℝ) : ℂ) *
        (x : ℂ) ^ (-s - 1)) =
      riemannZeta s / s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) := by
  rw [corrected_fract_integral_eq_conductor d hd s hs,
    conductorZeta_of_ne_one d hs1, conductorSymbol_eq_cpow d hd]
  ring

/-- The fractional-part mean is evaluated through the removable continuation. -/
theorem corrected_fract_integral_one (d : ℕ) (hd : 0 < d) :
    (∫ x in Ioi (1 : ℝ),
      ((Int.fract (x / (d : ℝ)) - Int.fract x / (d : ℝ) : ℝ) : ℂ) *
        (x : ℂ) ^ (-2 : ℂ)) = (Real.log d : ℂ) / d := by
  have h := corrected_fract_integral_eq_conductor d hd 1 (by norm_num)
  simpa only [show -(1 : ℂ) - 1 = (-2 : ℂ) by norm_num,
    conductorZeta_one, div_one] using h

/-- The punctured zeta quotient has the correct normalized mean as its limit. -/
theorem tendsto_normalizedResidue_zeta_one (d : ℕ) (hd : 0 < d) :
    Tendsto (fun s : ℂ => riemannZeta s / s *
        ((1 / (d : ℂ)) - (d : ℂ) ^ (-s))) (𝓝[≠] 1)
      (𝓝 ((Real.log d : ℂ) / d)) := by
  have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_zeta_mul_conductorSymbol_one d hd).div hid
    (by norm_num : (1 : ℂ) ≠ 0)
  simp only [div_one] at hlim
  convert hlim using 1
  funext s
  change riemannZeta s / s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) =
    (riemannZeta s * RiemannResearch.RH.ArithmeticConductorCommonZeros.conductorSymbol d s) / s
  rw [conductorSymbol_eq_cpow d hd]
  ring

/-- Holomorphic actual normalized-atom transform throughout `Re(s) > 0`. -/
theorem analyticAt_paretoMellin_normalizedResidue (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => paretoMellin (normalizedResidueHilbert d hd) z) s := by
  have hb : ∀ k, |hilbertSequence (normalizedResidueHilbert d hd) k| ≤ (1 : ℝ) := by
    intro k
    rw [normalizedResidueHilbert_sequence]
    change |normalizedAtom d k| ≤ 1
    exact normalizedAtom_abs_le_one d k hd
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [he] with z hz
  exact paretoMellin_differentiableAt_of_bounded (normalizedResidueHilbert d hd) hb z hz

/-- Every actual zeta zero away from the pole annihilates the actual atom integral. -/
theorem paretoMellin_normalizedResidue_zero_of_zeta_zero (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    paretoMellin (normalizedResidueHilbert d hd) s = 0 := by
  rw [paretoMellin_normalizedResidue_zeta d hd s hs hs1, hz, zero_div, zero_mul]

end RiemannResearch.RH.ParetoAtomMellinSignature
