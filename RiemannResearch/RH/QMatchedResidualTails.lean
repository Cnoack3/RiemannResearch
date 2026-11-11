import RiemannResearch.RH.QUniformTail
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Uniform physical tails of the actual matched Pareto residuals

Source: user-provided short-head localization, 10 November 2026.
QHilbert and ThresholdHilbert share the raw l2 carrier. The coordinate
truncation below is applied to the Pareto encoding, so its norm is P, not Q.
The existing uniform-tail theorem proves the finite-exception argument.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMatchedResidualTails
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoClosedProjectionComparison
open QFiniteSupportDualCriterion QAnnihilatorTailEscape QFullDivisorProjection
open RiemannResearch.Analysis.ResidualizedProjectionKernel

theorem tail_apply (A : ℕ) (f : QHilbert) (i : ℕ) :
    tail A f i = if A ≤ i then f i else 0 := by
  by_cases h : A ≤ i
  · change f i - finiteHead A f i = _
    rw [finiteHead_apply_eq_zero A f i h, if_pos h, sub_zero]
  · change f i - finiteHead A f i = _
    rw [finiteHead_apply_of_lt A f i (Nat.lt_of_not_ge h), if_neg h, sub_self]

theorem tail_comp {A B : ℕ} (hAB : A ≤ B) (f : QHilbert) :
    tail B (tail A f) = tail B f := by
  apply lp.ext
  funext i
  by_cases hi : B ≤ i
  · simp only [tail_apply, if_pos hi, if_pos (hAB.trans hi)]
  · simp only [tail_apply, if_neg hi]

theorem tail_norm_antitone (f : QHilbert) :
    Antitone (fun A => ‖tail A f‖) := by
  intro A B hAB
  simpa only [tail_comp hAB] using tail_norm_le B (tail A f)

/-- Equality to the physical P tail beyond the positive site A. -/
theorem pareto_tail_norm_eq_shift (A : ℕ) (f : ThresholdHilbert) :
    ‖tail A f‖ = ‖hilbertTailShift f A‖ := by
  have hh := hilbertTailShift_inner f (tail A f) A (by
    intro i hi
    simp only [tail_apply, if_neg (Nat.not_le_of_gt hi)])
  have ht : hilbertTailShift (tail A f) A = hilbertTailShift f A := by
    apply lp.ext
    funext i
    change tail A f (i + A) = f (i + A)
    rw [tail_apply, if_pos (Nat.le_add_left A i)]
  rw [ht, real_inner_self_eq_norm_sq] at hh
  have horth := inner_finiteHead_tail A f f
  have he : inner ℝ f (tail A f) = ‖tail A f‖ ^ 2 := by
    have hsplit : f = finiteHead A f + tail A f := by
      simp only [tail, add_sub_cancel]
    nth_rw 1 [hsplit]
    rw [inner_add_left, show inner ℝ (finiteHead A f) (tail A f) = 0
      from horth, zero_add, real_inner_self_eq_norm_sq]
  rw [he] at hh
  nlinarith [norm_nonneg (tail A f), norm_nonneg (hilbertTailShift f A)]

def tailEnvelope (r : ℕ → ThresholdHilbert) (A : ℕ) : ℝ :=
  ⨆ j, ‖tail A (r j)‖

theorem tail_bdd (r : ℕ → ThresholdHilbert) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B) (A : ℕ) :
    BddAbove (Set.range (fun j => ‖tail A (r j)‖)) := by
  refine ⟨B, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact (tail_norm_le A (r j)).trans (hr j)

theorem tail_le_envelope (r : ℕ → ThresholdHilbert) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B) (A j : ℕ) :
    ‖tail A (r j)‖ ≤ tailEnvelope r A :=
  le_ciSup (tail_bdd r hr A) j

theorem envelope_nonneg (r : ℕ → ThresholdHilbert) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B) (A : ℕ) :
    0 ≤ tailEnvelope r A :=
  (norm_nonneg _).trans (tail_le_envelope r hr A 0)

theorem envelope_le (r : ℕ → ThresholdHilbert) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B) (A : ℕ) :
    tailEnvelope r A ≤ B :=
  ciSup_le (fun j => (tail_norm_le A (r j)).trans (hr j))

theorem envelope_antitone (r : ℕ → ThresholdHilbert) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B) : Antitone (tailEnvelope r) := by
  intro A C hAC
  apply ciSup_le
  intro j
  exact (tail_norm_antitone (r j) hAC).trans (tail_le_envelope r hr A j)

theorem envelope_tendsto_zero (r : ℕ → ThresholdHilbert) (rLimit : ThresholdHilbert)
    (hconv : Tendsto r atTop (𝓝 rLimit)) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B) :
    Tendsto (tailEnvelope r) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun A => ha.trans_le (envelope_nonneg r hr A))
  · intro ε hε
    obtain ⟨A₀, hA₀⟩ := uniform_tail_tightness_of_tendsto r rLimit hconv
      (ε / 2) (by linarith)
    filter_upwards [eventually_ge_atTop A₀] with A hA
    have hb : tailEnvelope r A ≤ ε / 2 :=
      ciSup_le (fun j => (hA₀ A hA j).le)
    linarith

def matchedResidual (L : ℕ+) : ThresholdHilbert :=
  toPareto (qOne - pOptimizer L)

def limitResidual : ThresholdHilbert :=
  toPareto (qOne - pFit QFullDisplacement.paretoClosure qOne)

theorem matchedResidual_tendsto (L : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (L i : ℕ) ∣ (L j : ℕ))
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    Tendsto (fun j => matchedResidual (L j)) atTop (𝓝 limitResidual) := by
  exact toParetoCLM.continuous.continuousAt.tendsto.comp
    (tendsto_const_nhds.sub (pOptimizer_tendsto L hnest hcofinal))

theorem matchedResidual_norm_le_one (L : ℕ+) : ‖matchedResidual L‖ ≤ 1 := by
  have he : matchedResidual L =
      hilbertOne - (paretoStage L).starProjection hilbertOne := by
    simp only [matchedResidual, pOptimizer, toPareto_sub,
      toPareto_pFit, toPareto_qOne]
  rw [he]
  have h := residual_norm_sq (paretoStage L) hilbertOne
  rw [hilbertOne_norm_sq] at h
  nlinarith [sq_nonneg ‖(paretoStage L).starProjection hilbertOne‖,
    norm_nonneg (hilbertOne - (paretoStage L).starProjection hilbertOne)]

/-- Unconditional: the limit residual need not vanish. -/
theorem matched_tailEnvelope_tendsto (L : ℕ → ℕ+)
    (hnest : ∀ i j, i ≤ j → (L i : ℕ) ∣ (L j : ℕ))
    (hcofinal : ∀ m : ℕ, 1 < m → ∃ j, m ∣ (L j : ℕ)) :
    Tendsto (tailEnvelope (fun j => matchedResidual (L j))) atTop (𝓝 0) :=
  envelope_tendsto_zero _ limitResidual (matchedResidual_tendsto L hnest hcofinal)
    (fun j => matchedResidual_norm_le_one (L j))

end RiemannResearch.RH.QMatchedResidualTails
