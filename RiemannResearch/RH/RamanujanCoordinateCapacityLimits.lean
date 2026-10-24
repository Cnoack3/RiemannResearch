import RiemannResearch.RH.RamanujanCoefficientConstraints
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Fixed-coordinate capacities and moving affine optimizer limits

Source: user-requested third Ramanujan transfer program, 23 October 2026.
The finite arithmetic capacity is the squared norm of the actual projected
Möbius Riesz vector. Its limit is positive and finite, independently of RH.
Prescribed values may vary along any cofinal filter; the constrained legal
optimizers converge to the explicit affine correction of the full projection.
The limiting error retains the full unresolved canonical residual energy.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanCoefficientConstraints
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

def coordinateRiesz (m : ℕ) : ThresholdHilbert := -mobiusRieszHilbert m

def coordinateRepresenter (n m : ℕ) : ThresholdHilbert :=
  (finiteSpace n).starProjection (coordinateRiesz m)

def coordinateLimitRepresenter (m : ℕ) : ThresholdHilbert :=
  closedSpace.starProjection (coordinateRiesz m)

def coordinateLimitCapacity (m : ℕ) : ℝ := ‖coordinateLimitRepresenter m‖ ^ 2

theorem coordinateRiesz_inner (m : ℕ) (x : ThresholdHilbert) :
    inner ℝ (coordinateRiesz m) x = coefficientCLM m x := by
  simp only [coordinateRiesz, inner_neg_left, mobiusRieszHilbert_inner,
    coefficientCLM, ContinuousLinearMap.neg_apply]

theorem coordinateSource_eq_cross (n m : ℕ) (hm : 1 < m) :
    coordinateSource n m =
      cross (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (coordinateRiesz m) := by
  funext i
  symm
  change inner ℝ (ramanujanPacketHilbert (i.val + 2)) (-mobiusRieszHilbert m) = _
  rw [inner_neg_right, real_inner_comm, mobiusRieszHilbert_inner,
    mobiusDifferenceCLM_ramanujanPacketHilbert m (i.val + 2) hm (by omega)]
  unfold coordinateSource
  split_ifs <;> ring

/-- The arithmetic inverse source is exactly the projected continuous coordinate vector. -/
theorem minimumVector_eq_coordinateRepresenter (n m : ℕ) (hm : 1 < m) :
    minimumVector (finitePacket_independent n) (coordinateSource n m) =
      coordinateRepresenter n m := by
  have hs : synthesisSpan (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) =
      finiteSpace n := by
    exact finitePacket_span_eq n
  have h : Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (inverseCoeff (finitePacket_independent n) (coordinateRiesz m)) =
        (finiteSpace n).starProjection (coordinateRiesz m) := by
    simpa only [hs] using
      synthesis_inverseCoeff_eq_projection (finitePacket_independent n) (coordinateRiesz m)
  change Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
    (inverseSource (finitePacket_independent n)
      (cross (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (coordinateRiesz m))) =
      coordinateRepresenter n m at h
  rw [← coordinateSource_eq_cross n m hm] at h
  exact h

theorem coordinateCapacity_eq_norm_sq (n m : ℕ) (hm : 1 < m) :
    coordinateCapacity n m = ‖coordinateRepresenter n m‖ ^ 2 := by
  rw [coordinateCapacity, capacity_eq_norm_sq, minimumVector_eq_coordinateRepresenter n m hm]

theorem coordinateRepresenter_tendsto (m : ℕ) :
    Tendsto (fun n => coordinateRepresenter n m) atTop (𝓝 (coordinateLimitRepresenter m)) :=
  walkProjection_tendsto residueAtom id Function.surjective_id (coordinateRiesz m)

theorem coordinateCapacity_tendsto (m : ℕ) (hm : 1 < m) :
    Tendsto (fun n => coordinateCapacity n m) atTop (𝓝 (coordinateLimitCapacity m)) := by
  simpa only [coordinateCapacity_eq_norm_sq _ m hm, coordinateLimitCapacity] using
    (coordinateRepresenter_tendsto m).norm.pow 2

private theorem coordinateCapacity_energy_identity (n m : ℕ) (hm : 1 < m) :
    ‖coordinateRiesz m‖ ^ 2 =
      walkError residueAtom id (coordinateRiesz m) n + coordinateCapacity n m := by
  have h := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
    (finiteSpace n) bot_le (coordinateRiesz m)
  have hn : ‖coordinateRiesz m‖ ^ 2 =
      ‖coordinateRiesz m - coordinateRepresenter n m‖ ^ 2 +
        ‖coordinateRepresenter n m‖ ^ 2 := by
    simpa [coordinateRepresenter] using h
  rw [← coordinateCapacity_eq_norm_sq n m hm] at hn
  exact hn

private theorem coordinateLimitCapacity_energy_identity (m : ℕ) :
    ‖coordinateRiesz m‖ ^ 2 =
      limitingError residueAtom (coordinateRiesz m) + coordinateLimitCapacity m := by
  have h := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
    closedSpace bot_le (coordinateRiesz m)
  simpa [coordinateLimitRepresenter, coordinateLimitCapacity, limitingError] using h

theorem coordinateCapacity_monotone (m : ℕ) (hm : 1 < m) :
    Monotone (fun n => coordinateCapacity n m) := by
  intro j k hjk
  have he := walkError_antitone residueAtom id (coordinateRiesz m) hjk
  linarith [coordinateCapacity_energy_identity j m hm,
    coordinateCapacity_energy_identity k m hm]

/-- The missing capacity is exactly the squared representer approximation error. -/
theorem coordinateCapacity_limit_exact (n m : ℕ) (hm : 1 < m) :
    coordinateLimitCapacity m = coordinateCapacity n m +
      ‖coordinateLimitRepresenter m - coordinateRepresenter n m‖ ^ 2 := by
  have h := walkError_eq_limitingError_add residueAtom id (coordinateRiesz m) n
  change walkError residueAtom id (coordinateRiesz m) n =
    limitingError residueAtom (coordinateRiesz m) +
      ‖coordinateLimitRepresenter m - coordinateRepresenter n m‖ ^ 2 at h
  linarith [coordinateCapacity_energy_identity n m hm,
    coordinateLimitCapacity_energy_identity m]

theorem coordinateCapacity_le_limit (n m : ℕ) (hm : 1 < m) :
    coordinateCapacity n m ≤ coordinateLimitCapacity m := by
  rw [coordinateCapacity_limit_exact n m hm]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The fixed-coordinate capacity never diverges: its exact continuous dual norm bounds it. -/
theorem coordinateLimitCapacity_bounds (m : ℕ) (hm : 1 < m) :
    0 < coordinateLimitCapacity m ∧
      coordinateLimitCapacity m ≤
        ∑ j ∈ Finset.Icc 1 m,
          (j : ℝ) * ((j : ℝ) + 1) * (dualCoeff m j : ℝ) ^ 2 := by
  constructor
  · exact lt_of_lt_of_le (coordinateCapacity_pos m m hm (Nat.le_succ m))
      (coordinateCapacity_le_limit m m hm)
  · have h := coordinateLimitCapacity_energy_identity m
    have hn : 0 ≤ limitingError residueAtom (coordinateRiesz m) := sq_nonneg _
    have hb : coordinateLimitCapacity m ≤ ‖coordinateRiesz m‖ ^ 2 := by linarith
    simpa only [coordinateRiesz, norm_neg, mobiusRieszHilbert_norm,
      mobiusDifferenceCLM_norm_sq m (by omega)] using hb

/-- The finite optimizer is the canonical fit plus its exact coordinate correction. -/
theorem candidate_eq_projection_correction (n m : ℕ) (hm : 1 < m) (t : ℝ) :
    candidate n m t = packetCandidate n +
      ((t - packetMultipleCoefficient n m) / coordinateCapacity n m) •
        coordinateRepresenter n m := by
  unfold candidate
  rw [coefficients_exact, map_add, map_smul]
  change packetCandidate n +
    ((t - packetMultipleCoefficient n m) / coordinateCapacity n m) •
      minimumVector (finitePacket_independent n) (coordinateSource n m) = _
  rw [minimumVector_eq_coordinateRepresenter n m hm]

def limitCandidate (m : ℕ) (t : ℝ) : ThresholdHilbert :=
  limitProjection + ((t - limitCoefficient m) / coordinateLimitCapacity m) •
    coordinateLimitRepresenter m

/-- Prescribed coordinate values may vary along every cofinal filter. -/
theorem candidate_tendsto_limit {α : Type*} {l : Filter α}
    (m : ℕ) (hm : 1 < m) (N : α → ℕ) (hN : Tendsto N l atTop)
    (t : α → ℝ) (t₀ : ℝ) (ht : Tendsto t l (𝓝 t₀)) :
    Tendsto (fun i => candidate (N i) m (t i)) l (𝓝 (limitCandidate m t₀)) := by
  have hp : Tendsto (fun i => packetCandidate (N i)) l (𝓝 limitProjection) := by
    simpa only [packetCandidate_eq_projection, Function.comp_def] using
      projection_tendsto.comp hN
  have hc := (packetMultipleCoefficient_tendsto m hm).comp hN
  have hk := (coordinateCapacity_tendsto m hm).comp hN
  have hr := (coordinateRepresenter_tendsto m).comp hN
  have hs := (ht.sub hc).div hk (ne_of_gt (coordinateLimitCapacity_bounds m hm).1)
  simpa only [candidate_eq_projection_correction _ m hm, limitCandidate,
    Function.comp_def, Pi.div_apply] using hp.add (hs.smul hr)

theorem limitCandidate_mem_closedSpace (m : ℕ) (t : ℝ) :
    limitCandidate m t ∈ closedSpace := by
  exact closedSpace.add_mem (closedSpace.starProjection_apply_mem hilbertOne)
    (closedSpace.smul_mem _ (closedSpace.starProjection_apply_mem (coordinateRiesz m)))

/-- The limiting affine optimizer pays the full canonical error and the exact finite capacity cost. -/
theorem limitCandidate_error (m : ℕ) (hm : 1 < m) (t : ℝ) :
    ‖hilbertOne - limitCandidate m t‖ ^ 2 =
      limitEnergy + (t - limitCoefficient m) ^ 2 / coordinateLimitCapacity m := by
  have hc := candidate_tendsto_limit m hm id tendsto_id (fun _ => t) t tendsto_const_nhds
  have hOne : Tendsto (fun _ : ℕ => hilbertOne) atTop (𝓝 hilbertOne) := tendsto_const_nhds
  have hT : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  have he := (hOne.sub hc).norm.pow 2
  have hp : Tendsto (fun n => 1 - packetMass n) atTop (𝓝 limitEnergy) := by
    have hf : (fun n => 1 - packetMass n) = energy := by
      funext n
      exact (packet_energy_eq_original n).symm
    rw [hf]
    exact energy_tendsto
  have ht := hp.add (((hT.sub
    (packetMultipleCoefficient_tendsto m hm)).pow 2).div
      (coordinateCapacity_tendsto m hm) (ne_of_gt (coordinateLimitCapacity_bounds m hm).1))
  have hform : (fun n => ‖hilbertOne - candidate n m t‖ ^ 2) =ᶠ[atTop]
      (fun n => 1 - packetMass n +
        (t - packetMultipleCoefficient n m) ^ 2 / coordinateCapacity n m) := by
    exact eventually_atTop.2 ⟨m, fun n hn =>
      candidate_error_exact n m hm (by omega) t⟩
  exact tendsto_nhds_unique he (ht.congr' hform.symm)

/-- The limiting vector satisfies the prescribed continuous legal coordinate exactly. -/
theorem limitCandidate_coordinate (m : ℕ) (hm : 1 < m) (t : ℝ) :
    coefficientCLM m (limitCandidate m t) = t := by
  have hc := candidate_tendsto_limit m hm id tendsto_id (fun _ => t) t tendsto_const_nhds
  have he := ((coefficientCLM m).continuous.tendsto (limitCandidate m t)).comp hc
  have hform : (fun n => coefficientCLM m (candidate n m t)) =ᶠ[atTop] (fun _ => t) := by
    exact eventually_atTop.2 ⟨m, fun n hn => candidate_coordinate n m hm (by omega) t⟩
  exact tendsto_nhds_unique he (tendsto_const_nhds.congr' hform.symm)

theorem coordinateLimitRepresenter_inner (m : ℕ) (y : ThresholdHilbert)
    (hy : y ∈ closedSpace) :
    inner ℝ (coordinateLimitRepresenter m) y = coefficientCLM m y := by
  have ho : inner ℝ (coordinateRiesz m - coordinateLimitRepresenter m) y = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (coordinateRiesz m)) _ hy
  rw [inner_sub_left, coordinateRiesz_inner] at ho
  exact (sub_eq_zero.mp ho).symm

private theorem limitCandidate_residual_orthogonal
    (m : ℕ) (hm : 1 < m) (t : ℝ) (y : ThresholdHilbert)
    (hy : y ∈ closedSpace) (hyt : coefficientCLM m y = t) :
    inner ℝ (hilbertOne - limitCandidate m t) (y - limitCandidate m t) = 0 := by
  have hyc := closedSpace.sub_mem hy (limitCandidate_mem_closedSpace m t)
  have h₁ : inner ℝ (hilbertOne - limitProjection) (y - limitCandidate m t) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hyc
  have h₂ : inner ℝ (coordinateLimitRepresenter m) (y - limitCandidate m t) = 0 := by
    rw [coordinateLimitRepresenter_inner m _ hyc, map_sub, hyt,
      limitCandidate_coordinate m hm t, sub_self]
  have he : hilbertOne - limitCandidate m t = (hilbertOne - limitProjection) -
      ((t - limitCoefficient m) / coordinateLimitCapacity m) • coordinateLimitRepresenter m := by
    unfold limitCandidate
    abel
  rw [he, inner_sub_left, real_inner_smul_left, h₁, h₂, mul_zero, sub_zero]

/-- Exact minimization over the entire closed affine legal space, with every remainder retained. -/
theorem limitCandidate_completion (m : ℕ) (hm : 1 < m) (t : ℝ)
    (y : ThresholdHilbert) (hy : y ∈ closedSpace) (hyt : coefficientCLM m y = t) :
    ‖hilbertOne - y‖ ^ 2 =
      limitEnergy + (t - limitCoefficient m) ^ 2 / coordinateLimitCapacity m +
        ‖y - limitCandidate m t‖ ^ 2 := by
  have he : hilbertOne - y =
      (hilbertOne - limitCandidate m t) - (y - limitCandidate m t) := by abel
  rw [he, norm_sub_sq_real, limitCandidate_residual_orthogonal m hm t y hy hyt,
    limitCandidate_error m hm t]
  ring

theorem limitCandidate_optimal_iff (m : ℕ) (hm : 1 < m) (t : ℝ)
    (y : ThresholdHilbert) (hy : y ∈ closedSpace) (hyt : coefficientCLM m y = t) :
    ‖hilbertOne - y‖ ^ 2 =
      limitEnergy + (t - limitCoefficient m) ^ 2 / coordinateLimitCapacity m ↔
      y = limitCandidate m t := by
  constructor
  · intro he
    have hc := limitCandidate_completion m hm t y hy hyt
    have hz : ‖y - limitCandidate m t‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    exact limitCandidate_error m hm t

end RiemannResearch.RH.RamanujanCoefficientConstraints
