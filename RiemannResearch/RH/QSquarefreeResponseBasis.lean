/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QSquarefreeHeadBoundary
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.QSquarefreeEvaluationBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QSquarefreeHeadPrediction
import RiemannResearch.RH.QSquarefreeTailResponse
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Lean.Elab.Tactic.Omega

/-!
# The ordered basis realizes the exact head/tail response split

Source: user-provided Head Boundary / Tail Response handoff, R2.
The basis coefficients keep their signs and use complete Hilbert norms.
This identifies the existing minimum-norm head extension, without claiming
that its physical reconstruction is uniformly bounded.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeResponseBasis
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QSquarefreeCorrectionKernel QSquarefreeTailResponse
open QSquarefreeEvaluationBasis QSquarefreeHeadPrediction
open InnerProductSpace

theorem orderedVector_mem_headKernelSpace (N H : ℕ) (i : Fin (N + 1))
    (hi : i.val < H) : orderedVector N i ∈ headKernelSpace N H := by
  change ‖innovation N i‖⁻¹ • innovation N i ∈ _
  apply Submodule.smul_mem
  have hs : Submodule.span ℝ (evaluationFamily N '' Set.Iic i) ≤
      headKernelSpace N H := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    have hjH : j.val < H := lt_of_le_of_lt (show j.val ≤ i.val from hj) hi
    exact kernel_mem_headKernelSpace N H ⟨j.val, hjH⟩
  exact hs (gramSchmidt_mem_span ℝ (evaluationFamily N) (le_refl i))

theorem orderedVector_mem_tailStage (N H : ℕ) (i : Fin (N + 1))
    (hi : H ≤ i.val) : orderedVector N i ∈ tailStage N H := by
  refine ⟨orderedVector_mem_stage N i, ?_⟩
  intro n hn
  exact orderedVector_onset N i n (lt_of_lt_of_le hn hi)

theorem low_coefficient_zero_of_tailStage (N H : ℕ) (f : QHilbert)
    (hf : f ∈ tailStage N H) (i : Fin (N + 1)) (hi : i.val < H) :
    inner ℝ f (orderedVector N i) = 0 := by
  have hu := orderedVector_mem_headKernelSpace N H i hi
  rw [headKernelSpace_eq] at hu
  exact Submodule.inner_right_of_mem_orthogonal hf hu.2

theorem high_coefficient_zero_of_headKernelSpace (N H : ℕ) (f : QHilbert)
    (hf : f ∈ headKernelSpace N H) (i : Fin (N + 1)) (hi : H ≤ i.val) :
    inner ℝ f (orderedVector N i) = 0 := by
  rw [headKernelSpace_eq] at hf
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (orderedVector_mem_tailStage N H i hi) hf.2

theorem headResponse_coefficient (N H : ℕ) (i : Fin (N + 1)) :
    inner ℝ (headResponse N H) (orderedVector N i) =
      if i.val < H then inner ℝ (movingCorrection N) (orderedVector N i) else 0 := by
  by_cases hi : i.val < H
  · rw [if_pos hi, headResponse, inner_sub_left,
      low_coefficient_zero_of_tailStage N H _ (tailResponse_mem N H) i hi, sub_zero]
  · rw [if_neg hi]
    exact high_coefficient_zero_of_headKernelSpace N H _
      (headResponse_mem_headKernelSpace N H) i (by omega)

theorem tailResponse_coefficient (N H : ℕ) (i : Fin (N + 1)) :
    inner ℝ (tailResponse N H) (orderedVector N i) =
      if H ≤ i.val then inner ℝ (movingCorrection N) (orderedVector N i) else 0 := by
  by_cases hi : H ≤ i.val
  · rw [if_pos hi]
    have h := congrArg (fun f : QHilbert => inner ℝ f (orderedVector N i))
      (response_split N H)
    rw [inner_add_left,
      high_coefficient_zero_of_headKernelSpace N H _
        (headResponse_mem_headKernelSpace N H) i hi, zero_add] at h
    exact h.symm
  · rw [if_neg hi]
    exact low_coefficient_zero_of_tailStage N H _ (tailResponse_mem N H) i (by omega)

/-- The actual minimum-norm head extension is exactly the low-onset synthesis. -/
theorem headResponse_synthesis (N H : ℕ) :
    headResponse N H = ∑ i : Fin (N + 1),
      if i.val < H then
        inner ℝ (movingCorrection N) (orderedVector N i) • orderedVector N i
      else 0 := by
  conv_lhs => rw [stage_synthesis N _ (headResponse_mem_stage N H)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [headResponse_coefficient]
  split_ifs <;> simp

/-- The already controlled complete-tail response is the high-onset synthesis. -/
theorem tailResponse_synthesis (N H : ℕ) :
    tailResponse N H = ∑ i : Fin (N + 1),
      if H ≤ i.val then
        inner ℝ (movingCorrection N) (orderedVector N i) • orderedVector N i
      else 0 := by
  conv_lhs => rw [stage_synthesis N _ (tailResponse_mem N H).1]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tailResponse_coefficient]
  split_ifs <;> simp

open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoParetoTransfer
open Pareto Pareto.CoefficientStabilization SquarefreeMobiusProjection
open QSquarefreeHeadBoundary QSquarefreeHeadPrediction
open QSquarefreeEvaluationBasis QSquarefreeTailResponse

/-- At a physical onset, the Möbius coefficient is minus the onset value. -/
private theorem coefficient_eq_neg_onset (f : QHilbert) (m : ℕ) (hm : 0 < m)
    (hf : ∀ n : ℕ, n < m → qSequence f n = 0) :
    qCoefficientCLM m f = -qSequence f m := by
  change -mobiusDifferenceCLM m (toPareto f) = _
  simp only [mobiusDifferenceCLM_apply, toPareto_sequence, mobiusDifference]
  congr 1
  rw [Finset.sum_eq_single m]
  · simp [Nat.div_self hm, hf (m - 1) (by omega)]
  · intro d hd hdm
    have hdle : d ≤ m := Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)
    have hdp : 0 < d := Nat.pos_of_mem_divisors hd
    rw [hf d (by omega), hf (d - 1) (by omega), sub_self, mul_zero]
  · intro hnot
    simp [Nat.mem_divisors, ne_of_gt hm] at hnot

/-- The actual ordered basis has no nonzero nonsquarefree physical pivot. -/
theorem orderedVector_eq_zero_of_nonsquarefree (N : ℕ) (i : Fin (N + 1))
    (hi : 1 < i.val + 1) (hs : ¬Squarefree (i.val + 1)) :
    orderedVector N i = 0 := by
  have he : (i.val + 1) - 2 + 2 = i.val + 1 := by omega
  have hc := omitted_coordinate_zero_of_mem_stage N (orderedVector N i)
    (orderedVector_mem_stage N i) ((i.val + 1) - 2) (by simpa only [he] using hs)
  rw [he, coefficient_eq_neg_onset _ _ (by omega)
    (orderedVector_physical_zero N i)] at hc
  have hp : qSequence (orderedVector N i) (i.val + 1) = 0 := neg_eq_zero.mp hc
  have ht : orderedVector N i ∈ tailStage N (i.val + 1) := by
    refine ⟨orderedVector_mem_stage N i, ?_⟩
    apply mem_headNull_of_physical_zero
    intro n hn
    rcases lt_or_eq_of_le hn with hlt | rfl
    · exact orderedVector_physical_zero N i n hlt
    · exact hp
  have hh := orderedVector_mem_headKernelSpace N (i.val + 1) i (by omega)
  rw [headKernelSpace_eq] at hh
  have hz := Submodule.inner_right_of_mem_orthogonal ht hh.2
  have hnorm : ‖orderedVector N i‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hz
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (orderedVector N i)])

open QSquarefreeHeadBoundary SquarefreeMobiusProjection
open RiemannResearch.Analysis.ExhaustiveWalk

/-- A literal onset witness forces its ordered evaluation pivot to survive. -/
theorem orderedVector_ne_zero_of_onset_witness
    (N : ℕ) (i : Fin (N + 1)) (f : QHilbert)
    (hf : f ∈ tailStage N i.val)
    (hm : qSequence f (i.val + 1) ≠ 0) : orderedVector N i ≠ 0 := by
  classical
  intro hi
  apply hm
  rw [stage_physical_synthesis N (i.val + 1) f hf.1]
  apply Finset.sum_eq_zero
  intro j hj
  rcases lt_trichotomy j.val i.val with hji | hji | hji
  · rw [low_coefficient_zero_of_tailStage N i.val f hf j hji, zero_mul]
  · have he : j = i := Fin.ext hji
    subst j
    simp [hi]
  · rw [orderedVector_physical_zero N j (i.val + 1) (by omega), mul_zero]

/-- Every active squarefree conductor below another active conductor supplies
a nonzero pivot, by their normalized contrast. -/
theorem orderedVector_ne_zero_of_active_lt
    (N : ℕ) (a d : Fin N)
    (ha : Squarefree (a.val + 2)) (hd : Squarefree (d.val + 2))
    (had : a.val < d.val) :
    orderedVector N ⟨a.val + 1, by omega⟩ ≠ 0 := by
  let f : QHilbert := ((a.val + 2 : ℕ) : ℝ) • qResidue (a.val + 2) -
    ((d.val + 2 : ℕ) : ℝ) • qResidue (d.val + 2)
  apply orderedVector_ne_zero_of_onset_witness N ⟨a.val + 1, by omega⟩ f
  · exact normalized_contrast_mem_tailStage N (a.val + 1) a d ha hd
      (by omega) (by omega)
  · change qSequenceLinear f (a.val + 1 + 1) ≠ 0
    dsimp only [f]
    rw [map_sub, map_smul, map_smul]
    change ((a.val + 2 : ℕ) : ℝ) * qSequence (qResidue (a.val + 2)) (a.val + 2) -
      ((d.val + 2 : ℕ) : ℝ) * qSequence (qResidue (d.val + 2)) (a.val + 2) ≠ 0
    rw [qSequence_qResidue, qSequence_qResidue]
    simp only [ArithmeticCumulative.residueFraction, Nat.mod_self,
      Nat.mod_eq_of_lt (show a.val + 2 < d.val + 2 by omega),
      Nat.cast_zero, zero_div, mul_zero, zero_sub]
    have hd0 : ((d.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have ha0 : ((a.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.mpr (mul_ne_zero hd0 (div_ne_zero ha0 hd0))

theorem orderedVector_first_ne_zero (N : ℕ) (d : Fin N)
    (hd : Squarefree (d.val + 2)) :
    orderedVector N ⟨0, by omega⟩ ≠ 0 := by
  apply orderedVector_ne_zero_of_onset_witness N ⟨0, by omega⟩ (qResidue (d.val + 2))
  · refine ⟨active_qResidue_mem_stage N d hd, ?_⟩
    intro i hi
    change i < 0 at hi
    exact (Nat.not_lt_zero i hi).elim
  · rw [qSequence_qResidue]
    simp only [ArithmeticCumulative.residueFraction,
      Nat.mod_eq_of_lt (show 1 < d.val + 2 by omega), Nat.cast_one]
    exact div_ne_zero one_ne_zero (by positivity)

theorem orderedVector_zero_stage (i : Fin 1) : orderedVector 0 i = 0 := by
  simpa [stage, walkSpan] using orderedVector_mem_stage 0 i

/-- All pivots at or beyond a conductor cutoff vanish once every active
conductor is at most that cutoff. This includes the final active pivot. -/
theorem orderedVector_eq_zero_of_active_cutoff (N D : ℕ) (hD : 2 ≤ D)
    (hcut : ∀ a : Fin N, Squarefree (a.val + 2) → a.val + 2 ≤ D)
    (i : Fin (N + 1)) (hi : D ≤ i.val + 1) : orderedVector N i = 0 := by
  apply stage_eq_zero_of_head_zero (D - 1) (by omega)
  · exact stage_le_of_active_cutoff N D hD hcut (orderedVector_mem_stage N i)
  · intro n hn
    exact orderedVector_physical_zero N i n (by omega)

/-- With a largest active conductor D, the nonzero pivots are exactly the
squarefree physical sites strictly below D (including site 1). -/
theorem orderedVector_ne_zero_iff (N : ℕ) (d : Fin N)
    (hd : Squarefree (d.val + 2))
    (hmax : ∀ a : Fin N, Squarefree (a.val + 2) → a.val ≤ d.val)
    (i : Fin (N + 1)) :
    orderedVector N i ≠ 0 ↔
      Squarefree (i.val + 1) ∧ i.val + 1 < d.val + 2 := by
  constructor
  · intro hi
    constructor
    · by_cases hi0 : i.val = 0
      · simp [hi0]
      · by_contra hsf
        exact hi (orderedVector_eq_zero_of_nonsquarefree N i (by omega) hsf)
    · by_contra hlt
      apply hi
      apply orderedVector_eq_zero_of_active_cutoff N (d.val + 2) (by omega)
      · intro a ha
        have := hmax a ha
        omega
      · omega
  · rintro ⟨hsf, hlt⟩
    by_cases hi0 : i.val = 0
    · have he : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [he]
      exact orderedVector_first_ne_zero N d hd
    · let a : Fin N := ⟨i.val - 1, by omega⟩
      have ha : a.val + 2 = i.val + 1 := by dsimp [a]; omega
      have hsf' : Squarefree (a.val + 2) := by simpa only [ha] using hsf
      have had : a.val < d.val := by dsimp [a]; omega
      have h := orderedVector_ne_zero_of_active_lt N a d hsf' hd had
      have he : (⟨a.val + 1, by omega⟩ : Fin (N + 1)) = i := by
        apply Fin.ext
        dsimp [a]
        omega
      rwa [he] at h

theorem exists_largest_active (N : ℕ) (hN : 0 < N) :
    ∃ d : Fin N, Squarefree (d.val + 2) ∧
      ∀ a : Fin N, Squarefree (a.val + 2) → a.val ≤ d.val := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hs : Squarefree (N + 2)
      · refine ⟨⟨N, by omega⟩, hs, ?_⟩
        intro a ha
        exact Nat.le_of_lt_succ a.isLt
      · have hNp : 0 < N := by
          by_contra h
          have hN0 : N = 0 := by omega
          subst N
          exact hs Nat.prime_two.squarefree
        obtain ⟨d, hd, hm⟩ := ih hNp
        refine ⟨⟨d.val, by omega⟩, hd, ?_⟩
        intro a ha
        have haN : a.val < N := by
          have hne : a.val ≠ N := by
            intro he
            apply hs
            simpa only [he] using ha
          omega
        exact hm ⟨a.val, haN⟩ ha

end RiemannResearch.RH.QSquarefreeResponseBasis
