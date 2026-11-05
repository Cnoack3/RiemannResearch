import RiemannResearch.RH.QMellinWitness
import RiemannResearch.RH.CriticalMellinMixtureEnergy
import RiemannResearch.RH.CriticalMellinCellAsymptotics
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Unbounded critical-line Mellin evaluation on the physical Hilbert space

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, §8.
This gives the single-coordinate Riesz argument on the real input space
at every fixed critical-line ordinate. -/

noncomputable section
namespace RiemannResearch.RH.PrimeTreeMellinEndpoint
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QMellinTransfer QMellinCell
open Pareto Pareto.SpectralObstruction RiemannResearch.Analysis.Cesaro

private def unitCell (n : ℕ) : QHilbert := lp.single 2 n (1 : ℝ)

private theorem real_row_summable (ell : QHilbert →L[ℝ] ℝ) :
    Summable (fun n => (ell (unitCell n)) ^ 2) := by
  let v := (InnerProductSpace.toDual ℝ QHilbert).symm ell
  have row (n : ℕ) : ell (unitCell n) = v n := by
    calc
      ell (unitCell n) = inner ℝ v (unitCell n) := InnerProductSpace.toDual_symm_apply.symm
      _ = v n := by simp [unitCell, lp.inner_single_right, RCLike.inner_apply]
  exact (qCoordinate_square_summable v).congr fun n => by rw [row]

private theorem complex_row_summable (ell : QHilbert →L[ℝ] ℂ) :
    Summable (fun n => ‖ell (unitCell n)‖ ^ 2) := by
  have h := (real_row_summable (Complex.reCLM.comp ell)).add
    (real_row_summable (Complex.imCLM.comp ell))
  apply h.congr
  intro n
  change (ell (unitCell n)).re ^ 2 + (ell (unitCell n)).im ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem cell_value (s : ℂ) (hs : 0 < s.re) (i : ℕ) :
    s * qMellin (unitCell i) s =
      mellinFirst s (i + 1) * ((1 / Real.sqrt (qWeight i) : ℝ) : ℂ) := by
  have hi : 0 < Real.sqrt (qWeight i) := Real.sqrt_pos.mpr (qWeight_pos i)
  have hseq (n : ℕ) : qSequence (unitCell i) (n + 1) =
      if n = i then 1 / Real.sqrt (qWeight i) else 0 := by
    by_cases hn : n = i
    · simp [hn, qSequence_succ, unitCell]
    · simp [qSequence_succ, unitCell, lp.single_apply, hn]
  have hb (n : ℕ) : |hilbertSequence (toPareto (unitCell i)) n| ≤ 1 / Real.sqrt (qWeight i) := by
    rw [toPareto_sequence]
    cases n with
    | zero => simp
    | succ n =>
      rw [hseq]
      split <;> simp [abs_of_pos hi, hi.le]
  have hh := (hasSum_first_mellin_pairing_of_bounded (toPareto (unitCell i)) _ hb s hs).tsum_eq
  change s * paretoMellin (toPareto (unitCell i)) s = _
  rw [← hh, toPareto_sequence, tsum_eq_single i]
  · rw [hseq i, if_pos rfl]
  · intro n hn
    simp only [hseq n, if_neg hn, Complex.ofReal_zero, mul_zero]

/-- The squared dual row diverges at every ordinate, including t=0. -/
theorem critical_qCellEnergy_not_summable (t : ℝ) :
    ¬ Summable (qMellinCellEnergy (MellinFrequency.criticalPoint t)) := by
  intro h
  apply criticalMode_not_summable t
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (paretoWeight_pos n).le (sq_nonneg _))
    _ (h.mul_left 2)
  intro n
  rw [qMellinCellEnergy_eq_ratio_pareto]
  have hr : (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) :=
    (le_div_iff₀ (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hpos : 0 ≤ paretoWeight n * ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ^ 2 :=
    mul_nonneg (paretoWeight_pos n).le (sq_nonneg _)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hr) hpos]

/-- Already on the one-site cells the genuine physical Mellin integrals at
the endpoint disagree with every continuous real-linear functional. -/
theorem no_continuous_critical_evaluation (t : ℝ) :
    ¬ ∃ ell : QHilbert →L[ℝ] ℂ, ∀ n : ℕ,
      ell (lp.single 2 n (1 : ℝ)) =
        qMellin (lp.single 2 n (1 : ℝ)) (MellinFrequency.criticalPoint t) := by
  rintro ⟨ell, hL⟩
  let s := MellinFrequency.criticalPoint t
  have hs : 0 < s.re := by simp [s, MellinFrequency.criticalPoint]
  have hrow := (complex_row_summable ell).mul_left (‖s‖ ^ 2 / zetaTwo)
  apply critical_qCellEnergy_not_summable t
  apply hrow.congr
  intro n
  have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) (cell_value s hs n)
  have hw : ‖((1 / Real.sqrt (qWeight n) : ℝ) : ℂ)‖ ^ 2 = 1 / qWeight n := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow,
      Real.sq_sqrt (qWeight_pos n).le]
  simp only [norm_mul, mul_pow, hw] at hn
  have hd := QMellinWitness.dual_cell_eq s n
  change ‖s‖ ^ 2 / zetaTwo * ‖ell (lp.single 2 n (1 : ℝ))‖ ^ 2 = _
  rw [hL, show qMellin (lp.single 2 n (1 : ℝ)) (MellinFrequency.criticalPoint t) =
    qMellin (unitCell n) s from rfl]
  calc
    _ = (‖s‖ ^ 2 * ‖qMellin (unitCell n) s‖ ^ 2) / zetaTwo := by ring
    _ = qMellinCellEnergy s n := by
      rw [hn, mul_one_div, hd, mul_div_cancel_left₀ _ zetaTwo_pos.ne']

end RiemannResearch.RH.PrimeTreeMellinEndpoint
