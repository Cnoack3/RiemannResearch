/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.CRTCarryArithmetic
import RiemannResearch.RH.ParetoBoundedMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # A two-transform detector from a summable physical residue expansion

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§§3 and 5. Bagchi, Proc. Indian Acad. Sci. Math. Sci. 116 (2006), 137–146,
supplies the atom transform in the imported physical normalization.
The first transform may use any absolutely summable sequence of atom
coefficients. The second adds the paper's periodic difference in the
proportion associated with the first lift three. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.PrimeTreeTwoCarry

open ArithmeticCumulative CRTCarryArithmetic ZetaTwoHilbert ZetaTwoParetoTransfer QMellinTransfer

def readout (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), f ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)

def atomSeries (d : ℕ → ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑' k, c k * (residueFraction (d k) n : ℂ)

private theorem atom_norm_le (d n : ℕ) : ‖(residueFraction d n : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using residueFraction_abs_le_one d n

private theorem coeff_bound (d : ℕ → ℕ) (c : ℕ → ℂ) (k n : ℕ) :
    ‖c k * (residueFraction (d k) n : ℂ)‖ ≤ ‖c k‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (atom_norm_le _ _)

private theorem kernel_norm_integrable (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (-s - 1)‖) (Ioi 1) := by
  have he : (-s - 1).re < -1 := by simpa using (show -s.re - 1 < -1 by linarith)
  apply (integrableOn_Ioi_rpow_of_lt he (zero_lt_one : (0 : ℝ) < 1)).congr_fun _ measurableSet_Ioi
  intro x hx
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx) _).symm

private theorem bounded_integrable (f : ℕ → ℂ) (C : ℝ) (hf : ∀ n, ‖f n‖ ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => f ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hm : Measurable (fun x : ℝ => f ⌊x⌋₊) :=
    (measurable_of_countable f).comp (by fun_prop)
  apply ((kernel_norm_integrable s hs).const_mul C).mono'
  · exact (hm.mul (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _))

private theorem atom_readout (d : ℕ) (hd : 0 < d) (s : ℂ) (hs : 0 < s.re)
    (hone : s ≠ 1) :
    readout (fun n => (residueFraction d n : ℂ)) s =
      riemannZeta s / s * (1 / (d : ℂ) - (d : ℂ) ^ (-s)) := by
  simpa only [readout, qMellin_eq_step_integral, qSequence_qResidue] using
    qMellin_residue_zeta d hd s hs hone

/-- Mellin evaluation commutes with the atom sum throughout the positive
half-plane, including the removable point one. -/
theorem atomSeries_readout_hasSum_atoms (d : ℕ → ℕ)
    (c : ℕ → ℂ) (hc : Summable fun k => ‖c k‖) (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k => c k * readout (fun n => (residueFraction (d k) n : ℂ)) s)
      (readout (atomSeries d c) s) := by
  let F (k : ℕ) (x : ℝ) : ℂ := c k * ((residueFraction (d k) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
  let b (k : ℕ) (x : ℝ) : ℝ := ‖c k‖ * ‖(x : ℂ) ^ (-s - 1)‖
  have hF (k : ℕ) : IntegrableOn (F k) (Ioi 1) :=
    (bounded_integrable (fun n => (residueFraction (d k) n : ℂ)) 1 (atom_norm_le _) s hs).const_mul _
  have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := F) (f := fun x : ℝ => atomSeries d c ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) b
    (fun k => (hF k).aestronglyMeasurable)
    (fun k => ae_of_all _ (fun x => by
      dsimp [F, b]
      rw [← mul_assoc, norm_mul]
      exact mul_le_mul_of_nonneg_right (coeff_bound d c k _) (norm_nonneg _)))
    (ae_of_all _ (fun x => hc.mul_right _))
    (by simpa only [b, tsum_mul_right] using (kernel_norm_integrable s hs).const_mul (∑' k, ‖c k‖))
    (ae_of_all _ (fun x => by
      have ha : Summable (fun k => c k * (residueFraction (d k) ⌊x⌋₊ : ℂ)) :=
        Summable.of_norm_bounded hc (fun k => coeff_bound d c k _)
      simpa only [F, atomSeries, mul_assoc] using ha.hasSum.mul_right ((x : ℂ) ^ (-s - 1))))
  have he (k : ℕ) : (∫ x in Ioi (1 : ℝ), F k x) =
      c k * readout (fun n => (residueFraction (d k) n : ℂ)) s := by
    simp only [F, integral_const_mul, readout]
  simpa only [he, readout] using h

/-- The zeta-factor expression holds off the pole. -/
theorem atomSeries_readout_hasSum (d : ℕ → ℕ) (hd : ∀ k, 0 < d k)
    (c : ℕ → ℂ) (hc : Summable fun k => ‖c k‖) (s : ℂ) (hs : 0 < s.re) (hone : s ≠ 1) :
    HasSum (fun k => c k * (riemannZeta s / s * (1 / (d k : ℂ) - (d k : ℂ) ^ (-s))))
      (readout (atomSeries d c) s) := by
  have ha (k : ℕ) := atom_readout (d k) (hd k) s hs hone
  simpa only [ha] using atomSeries_readout_hasSum_atoms d c hc s hs

/-- Value of the single-atom physical observation at the removable point. -/
theorem atom_readout_one (d : ℕ) (hd : 0 < d) :
    readout (fun n => (residueFraction d n : ℂ)) 1 = (Real.log d : ℂ) / d := by
  have he : qMellin (qResidue d) 1 = (Real.log d : ℂ) / d := by
    rw [qMellin, toPareto_qResidue d hd, Pareto.BaezDuarte.residueVector, dif_pos hd,
      ParetoAtomMellinSignature.paretoMellin_normalizedResidue_conductor d hd 1 (by norm_num),
      ZetaConductorRegularization.conductorZeta_one, div_one]
  simpa only [readout, qMellin_eq_step_integral, qSequence_qResidue] using he

/-- The periodic combination equals (a₂ − a₃)/2 in the paper's
unnormalized residue notation. -/
def periodicDifference (n : ℕ) : ℂ :=
  (residueFraction 2 n : ℂ) - (3/2 : ℂ) * (residueFraction 3 n : ℂ)

def periodicFactor (s : ℂ) : ℂ :=
  (3/2 : ℂ) * (3 : ℂ) ^ (-s) - (2 : ℂ) ^ (-s)

theorem periodicFactor_ne_zero (s : ℂ) (hs : s.re < 1) : periodicFactor s ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  have hn (n : ℕ) (hn : 0 < n) : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < (n : ℝ) by exact_mod_cast hn) (-s)
  change ‖(3/2 : ℂ) * (3 : ℂ) ^ (-s)‖ = ‖(2 : ℂ) ^ (-s)‖ at he
  have h3 : ‖(3 : ℂ) ^ (-s)‖ = (3 : ℝ) ^ (-s.re) := hn 3 (by decide)
  have h2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := hn 2 (by decide)
  rw [norm_mul, h3, h2, norm_div] at he
  norm_num at he
  have hlt := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (2 : ℝ) < 3) (show 0 < 1 + -s.re by linarith)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_one, Real.rpow_one] at hlt
  linarith

theorem periodicDifference_readout (s : ℂ) (hs : 0 < s.re) (hone : s ≠ 1) :
    readout periodicDifference s = riemannZeta s / s * periodicFactor s := by
  let f (d : ℕ) (x : ℝ) := (residueFraction d ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)
  have hf (d : ℕ) : IntegrableOn (f d) (Ioi 1) :=
    bounded_integrable (fun n => (residueFraction d n : ℂ)) 1 (atom_norm_le _) s hs
  have he (x : ℝ) : periodicDifference ⌊x⌋₊ * (x : ℂ) ^ (-s - 1) =
      f 2 x - (3/2 : ℂ) * f 3 x := by dsimp [periodicDifference, f]; ring
  have hat (d : ℕ) (hd : 0 < d) : (∫ x in Ioi (1 : ℝ), f d x) =
      riemannZeta s / s * (1 / (d : ℂ) - (d : ℂ) ^ (-s)) := atom_readout d hd s hs hone
  unfold readout
  simp_rw [he]
  rw [integral_sub (hf 2) ((hf 3).const_mul _), integral_const_mul, hat 2 (by decide),
    hat 3 (by decide), periodicFactor]
  push_cast
  ring

/-- The exact affine change in the physical series when the first lift goes
from one to three, written so the shared infinite remainder is explicit. -/
def thirdLift (f : ℕ → ℂ) (n : ℕ) : ℂ := (2/3 : ℂ) * periodicDifference n + (1/3 : ℂ) * f n

/-- The joint zeros of the two integrals are exactly the zeta zeros in the
open strip for any common absolutely summable atom remainder. -/
theorem paired_readout_zero_iff (d : ℕ → ℕ) (hd : ∀ k, 0 < d k)
    (c : ℕ → ℂ) (hc : Summable fun k => ‖c k‖) (s : ℂ) (hs : 0 < s.re) (hlt : s.re < 1) :
    (readout (atomSeries d c) s = 0 ∧ readout (thirdLift (atomSeries d c)) s = 0) ↔
      riemannZeta s = 0 := by
  have hone : s ≠ 1 := by rintro rfl; norm_num at hlt
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hsum := atomSeries_readout_hasSum d hd c hc s hs hone
  have hf : IntegrableOn (fun x : ℝ => atomSeries d c ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    bounded_integrable _ (∑' k, ‖c k‖)
      (fun n => tsum_of_norm_bounded hc.hasSum (fun k => coeff_bound d c k n)) s hs
  have hp : IntegrableOn (fun x : ℝ => periodicDifference ⌊x⌋₊ * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
    apply bounded_integrable _ (1 + ‖(3/2 : ℂ)‖) _ s hs
    intro n
    refine (norm_sub_le _ _).trans (add_le_add (atom_norm_le _ _) ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (atom_norm_le _ _)
  have hmix : readout (thirdLift (atomSeries d c)) s =
      (2/3 : ℂ) * readout periodicDifference s + (1/3 : ℂ) * readout (atomSeries d c) s := by
    unfold readout thirdLift
    simp only [add_mul, mul_assoc]
    rw [integral_add (hp.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul]
  constructor
  · rintro ⟨h1, h3⟩
    rw [hmix, h1, mul_zero, add_zero, periodicDifference_readout s hs hone] at h3
    simpa [periodicFactor_ne_zero s hlt, hs0] using h3
  · intro hz
    have h1 : readout (atomSeries d c) s = 0 := by
      rw [← hsum.tsum_eq]
      simp [hz]
    exact ⟨h1, by rw [hmix, h1, periodicDifference_readout s hs hone, hz]; simp⟩

end RiemannResearch.RH.PrimeTreeTwoCarry
