import RiemannResearch.RH.DyadicResidueFourierBridge
import RiemannResearch.RH.DyadicTriadicFourierComparison
import RiemannResearch.RH.DyadicArithmeticResidueTelescoping

/-!
# Exact residue Fourier cocycle under all integer dilations

Source: independently developed from the actual residue Fourier expansion in
the user-provided FourierResidueBridgeVerification20260911(1).md.
The signed difference of successive conductors factors through a unit phase.
Consequently this actual arithmetic difference has no conductor norm cost.
Every identity includes the removable zero mode.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

@[simp] theorem dyadicIntegerFourierPhase_zero (n : ℕ) :
    dyadicIntegerFourierPhase 0 n = 1 := by
  simp [dyadicIntegerFourierPhase]

theorem dyadicIntegerFourierPhase_mul (h : ℤ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    dyadicIntegerFourierPhase h (a * b) =
      dyadicIntegerFourierPhase h a * dyadicIntegerFourierPhase h b := by
  rw [dyadicIntegerFourierPhase_eq_exp, dyadicIntegerFourierPhase_eq_exp,
    dyadicIntegerFourierPhase_eq_exp, Nat.cast_mul,
    Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem dyadicIntegerFourierPhase_pow (h : ℤ) (a : ℕ) (ha : 0 < a) (j : ℕ) :
    dyadicIntegerFourierPhase h (a ^ j) = dyadicIntegerFourierPhase h a ^ j := by
  induction j with
  | zero => simp [dyadicIntegerFourierPhase]
  | succ j ih =>
      rw [pow_succ, dyadicIntegerFourierPhase_mul h (a ^ j) a (by positivity) ha,
        ih, pow_succ]

theorem dyadicIntegerFourierPhase_three (h : ℤ) :
    dyadicIntegerFourierPhase h 3 = dyadicTriadicFourierPhase h := by
  simpa only [dyadicIntegerFourierPhase, Nat.cast_ofNat] using
    (dyadicTriadicFourierPhase_eq_fourier h).symm

/-- Actual dilation phases, with no abstract spectral identification. -/
theorem dyadicIntegerFourierPhase_mul_triadic_pow
    (h : ℤ) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    dyadicIntegerFourierPhase h (n * 3 ^ j) =
      dyadicIntegerFourierPhase h n * dyadicTriadicFourierPhase h ^ j := by
  rw [dyadicIntegerFourierPhase_mul h n (3 ^ j) hn (by positivity),
    dyadicIntegerFourierPhase_pow h 3 (by norm_num), dyadicIntegerFourierPhase_three]

/-- The exact signed residue cocycle, valid also at frequency zero. -/
theorem dyadicResidueFourierSymbol_mul_sub (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    dyadicResidueFourierSymbol (a * b) h - dyadicResidueFourierSymbol a h =
      dyadicIntegerFourierPhase h a * dyadicResidueFourierSymbol b h := by
  by_cases hh : h = 0
  · subst h
    simp only [dyadicResidueFourierSymbol,
      dyadicIntegerFourierPhase_zero, one_mul, Nat.cast_mul]
    rw [Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
    push_cast
    ring
  · simp only [dyadicResidueFourierSymbol, if_neg hh,
      dyadicIntegerFourierPhase_mul h a b ha hb]
    ring

/-- Taking the norm after signed cancellation removes all dependence on `a`. -/
theorem norm_dyadicResidueFourierSymbol_mul_sub (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    ‖dyadicResidueFourierSymbol (a * b) h - dyadicResidueFourierSymbol a h‖ =
      ‖dyadicResidueFourierSymbol b h‖ := by
  rw [dyadicResidueFourierSymbol_mul_sub a b ha hb h,
    norm_mul, norm_dyadicIntegerFourierPhase, one_mul]

/-- Every actual dilated residue has the phase-translated Fourier row. -/
theorem dyadicBoundaryCoordinate_residue_dilation_hasSum_fourier
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (i : ℕ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      (dyadicIntegerFourierPhase h a * dyadicResidueFourierSymbol b h))
      (dyadicBoundaryCoordinate
        (hilbertDilation a ha (hilbertResidue b hb)) i : ℂ) := by
  have hs := (dyadicBoundaryCoordinate_residue_hasSum_fourier
    (a * b) (Nat.mul_pos ha hb) i).sub
      (dyadicBoundaryCoordinate_residue_hasSum_fourier a ha i)
  have hfun : (fun h : ℤ =>
      dyadicTentMellinCoefficient i h * dyadicResidueFourierSymbol (a * b) h -
        dyadicTentMellinCoefficient i h * dyadicResidueFourierSymbol a h) =
      (fun h : ℤ => dyadicTentMellinCoefficient i h *
        (dyadicIntegerFourierPhase h a * dyadicResidueFourierSymbol b h)) := by
    funext h
    rw [← mul_sub, dyadicResidueFourierSymbol_mul_sub a b ha hb h]
  rw [hfun] at hs
  have hv : (dyadicBoundaryCoordinate (hilbertResidue (a * b) (Nat.mul_pos ha hb)) i : ℂ) -
      (dyadicBoundaryCoordinate (hilbertResidue a ha) i : ℂ) =
      (dyadicBoundaryCoordinate (hilbertDilation a ha (hilbertResidue b hb)) i : ℂ) := by
    rw [hilbertDilation_residue_eq_sub a b ha hb, dyadicBoundaryCoordinate_sub,
      Complex.ofReal_sub]
  rwa [hv] at hs

/-- The genuine double arithmetic index has this exact Fourier expansion. -/
theorem dyadicBoundaryCoordinate_triadic_residue_hasSum_fourier
    (n : ℕ) (hn : 0 < n) (j i : ℕ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      (dyadicIntegerFourierPhase h n * dyadicTriadicFourierPhase h ^ j *
        dyadicResidueFourierSymbol 3 h))
      (dyadicBoundaryCoordinate
        (hilbertDilation (n * 3 ^ j) (by positivity)
          (hilbertResidue 3 (by norm_num))) i : ℂ) := by
  have hs := dyadicBoundaryCoordinate_residue_dilation_hasSum_fourier
    (n * 3 ^ j) 3 (by positivity) (by norm_num) i
  convert hs using 1
  funext h
  rw [dyadicIntegerFourierPhase_mul_triadic_pow h n hn j]

end
end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Absolute scalar Fourier interchange for genuine dilates of a fixed residue.
The conductor phases have norm one; signed cancellation precedes estimation. -/
theorem dyadicBoundaryCoordinate_summable_residue_dilation_packet_hasSum_fourier
    {α : Type*} (i : ℕ) (b : ℕ) (hb : 0 < b)
    (m : α → ℕ) (hm : ∀ a, 0 < m a)
    (w : α → ℝ) (hw : Summable (fun a => |w a|)) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ((∑' a, (w a : ℂ) * dyadicIntegerFourierPhase h (m a)) *
        dyadicResidueFourierSymbol b h))
      (∑' a, (w a : ℂ) *
        (dyadicBoundaryCoordinate (hilbertDilation (m a) (hm a)
          (hilbertResidue b hb)) i : ℂ)) := by
  let f : α → ℤ → ℂ := fun a h => (w a : ℂ) *
    (dyadicTentMellinCoefficient i h *
      (dyadicIntegerFourierPhase h (m a) * dyadicResidueFourierSymbol b h))
  have hbase := (dyadicBoundaryCoordinate_residue_hasSum_fourier b hb i).summable.norm
  have hmajor := hw.mul_of_nonneg hbase (fun a => abs_nonneg _) (fun h => norm_nonneg _)
  have hf : Summable (Function.uncurry f) := by
    apply hmajor.of_norm_bounded
    intro p
    simp only [f, Function.uncurry, norm_mul, norm_dyadicIntegerFourierPhase,
      Complex.norm_real, Real.norm_eq_abs, one_mul]
    ring_nf
    exact le_rfl
  have hrow : Summable (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ((∑' a, (w a : ℂ) * dyadicIntegerFourierPhase h (m a)) *
        dyadicResidueFourierSymbol b h)) := by
    apply hf.prod_symm.prod.congr
    intro h
    change (∑' a, f a h) = _
    rw [← tsum_mul_right, ← tsum_mul_left]
    apply tsum_congr
    intro a
    dsimp [f]
    ring
  apply hrow.hasSum_iff.mpr
  calc
    _ = ∑' h, ∑' a, f a h := by
      apply tsum_congr
      intro h
      rw [← tsum_mul_right, ← tsum_mul_left]
      apply tsum_congr
      intro a
      dsimp [f]
      ring
    _ = ∑' a, ∑' h, f a h := hf.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro a
      exact (HasSum.mul_left (w a : ℂ)
        (dyadicBoundaryCoordinate_residue_dilation_hasSum_fourier
          (m a) b (hm a) hb i)).tsum_eq

end
end RiemannResearch.RH.Pareto
