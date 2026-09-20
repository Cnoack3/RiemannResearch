import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoLegalStructure

/-!
# Exact finite digamma formula for the complete residue Gram entries

Source: user-provided Gram-coefficient conversation, 20 September 2026.
The progression identity is the standard digamma partial-fraction identity
https://dlmf.nist.gov/5.9#E16, already proved in ParetoProgressionDigamma.
We specialize its full infinite Pareto sum to the residue Gram matrix.
Representatives run from 1 to lcm(a,b); the final zero-class term vanishes.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open CoefficientStabilization

theorem normalizedResidueHilbert_inner (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    inner ℝ (normalizedResidueHilbert a ha) (normalizedResidueHilbert b hb) =
      paretoInner (residue a) (residue b) / ((a : ℝ) * (b : ℝ)) := by
  rw [normalizedResidueHilbert, normalizedResidueHilbert,
    real_inner_smul_left, inner_smul_right, hilbert_inner_weighted,
    hilbertSequence_digitHilbert, hilbertSequence_digitHilbert]
  have hd (d : ℕ) : digitSequence d 1 = residue d := by
    funext k
    simp [digitSequence, residue]
  rw [hd, hd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Finite exact formula for the full Gram entry, including every progression tail. -/
theorem normalizedResidueHilbert_inner_digamma (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    inner ℝ (normalizedResidueHilbert a ha) (normalizedResidueHilbert b hb) =
      1 / ((a : ℝ) * (b : ℝ) * (Nat.lcm a b : ℝ)) *
        ∑ r : Fin (Nat.lcm a b),
          (((r.val + 1) % a : ℕ) : ℝ) * (((r.val + 1) % b : ℕ) : ℝ) *
            ((Complex.digamma
                ((((r.val + 2 : ℕ) : ℝ) / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re -
             (Complex.digamma
                ((((r.val + 1 : ℕ) : ℝ) / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re) := by
  have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  rw [normalizedResidueHilbert_inner,
    periodic_paretoInner_mixed (Nat.lcm a b) hL (residue a) (residue b)
      (fun k => residue_abs_le a k ha) (fun k => residue_abs_le b k hb)
      (residue_period_of_dvd (Nat.dvd_lcm_left a b))
      (residue_period_of_dvd (Nat.dvd_lcm_right a b)),
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [progressionWeight_eq_digamma (Nat.lcm a b) (r.val + 1) hL (by omega) (by omega)]
  simp only [residue, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The first actual Gram entry is log(2)/4. -/
theorem residueAtom_zero_norm_sq : ‖residueAtom 0‖^2 = Real.log 2 / 4 := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (normalizedResidueHilbert 2 _) (normalizedResidueHilbert 2 _) = _
  rw [normalizedResidueHilbert_inner, paretoInner_residue_two]
  norm_num

theorem residueAtom_zero_norm : ‖residueAtom 0‖ = Real.sqrt (Real.log 2) / 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := Real.sq_sqrt hlog.le
  have hn := residueAtom_zero_norm_sq
  have hnn := norm_nonneg (residueAtom 0)
  have hsn := Real.sqrt_nonneg (Real.log 2)
  nlinarith

/-- Exact first mode e₂ = 2g₂/sqrt(log 2). -/
theorem residueMode_zero : residueMode 0 =
    (2 / Real.sqrt (Real.log 2)) • residueAtom 0 := by
  change (‖InnerProductSpace.gramSchmidt ℝ residueAtom (0 : ℕ)‖ : ℝ)⁻¹ •
    InnerProductSpace.gramSchmidt ℝ residueAtom (0 : ℕ) = _
  have hg : InnerProductSpace.gramSchmidt ℝ residueAtom (0 : ℕ) = residueAtom 0 := by
    exact InnerProductSpace.gramSchmidt_bot ℝ residueAtom
  rw [hg, residueAtom_zero_norm]
  congr 1
  simp [div_eq_mul_inv, mul_inv_rev]

theorem modeCoefficient_two_zero : modeCoefficient 2 0 = 2 / Real.sqrt (Real.log 2) := by
  rw [modeCoefficient, residueMode_zero, map_smul]
  have hc := coefficientCLM_biorthogonal 0 0
  norm_num at hc
  rw [hc]
  simp

theorem modeAlpha_zero : modeAlpha 0 = Real.sqrt (Real.log 2) := by
  rw [modeAlpha, residueMode_zero, real_inner_smul_left, residueAtom_inner_one]
  norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_ofNat, zero_add]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Real.sqrt (Real.log 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlog)
  have hsq := Real.sq_sqrt hlog.le
  field_simp [hs]
  nlinarith

end RiemannResearch.RH.Pareto
