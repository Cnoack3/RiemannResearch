import RiemannResearch.Analysis.CorrelationNormalizedCorrection
import RiemannResearch.RH.TwoThreeHilbertBudget
import RiemannResearch.RH.ThresholdHilbertProjection
import Mathlib.Data.Nat.Factorial.Basic
import RiemannResearch.Analysis.LogarithmicResidualBarrier

/-!
# Transported corrections of the actual Pareto residual

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`.
The spaces are the established `budgetHilbert`, not independent abstract
providers. Floor indices and the zero-anchored Hilbert convention are exact.
The logarithmic lower bound for the source gain remains open.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.CorrelationCorrection
open RiemannResearch.LinearAlgebra

def fit (M : ℕ) : ThresholdHilbert := (budgetHilbert M).starProjection hilbertOne
def error (M : ℕ) : ThresholdHilbert := hilbertOne - fit M
def distance (M : ℕ) : ℝ := ‖error M‖^2
def gain (M : ℕ) : ℝ := distance M - distance (2*M)

theorem distance_sub (A B : ℕ) (hAB : A ≤ B) :
    distance A - distance B = ‖fit B - fit A‖^2 :=
  nested_gain (budgetHilbert A) (budgetHilbert B)
    (budgetHilbert_mono hAB) hilbertOne

theorem distance_antitone : Antitone distance := by
  intro A B hAB
  have h := distance_sub A B hAB
  nlinarith [sq_nonneg ‖fit B-fit A‖]

theorem residual_target (M : ℕ) : inner ℝ (error M) hilbertOne = distance M := by
  have h := residual_inner (budgetHilbert M) hilbertOne hilbertOne
  simpa only [RiemannResearch.Analysis.ProjectionSourceImprovement.residual, ← real_inner_self_eq_norm_sq, error, fit, distance] using h.symm

theorem dilation_generator (a p m : ℕ) (ha : 0 < a) (hp : 0 < p) (hm : 0 < m) :
    hilbertDilation a ha (generator p m hp hm) =
      generator p (a*m) hp (Nat.mul_pos ha hm) := by
  unfold generator
  exact hilbertDilation_comp a m ha hm _

theorem dilation_budget_mem (a N : ℕ) (ha : 0 < a)
    (f : ThresholdHilbert) (hf : f ∈ budgetHilbert N) :
    hilbertDilation a ha f ∈ budgetHilbert (a*N) := by
  rw [← canonicalHilbertFamily_span] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨hm, hmN, h3 | ⟨h2, hn⟩⟩ := (mem_canonicalIndices N i.val).mp i.property
    · unfold canonicalHilbertFamily
      rw [dilation_generator]
      exact generator_mem_budgetHilbert _ _ _ _ _ (Or.inr h3)
        (Nat.mul_le_mul_left a hmN)
    · unfold canonicalHilbertFamily
      rw [dilation_generator]
      exact generator_mem_budgetHilbert _ _ _ _ _ (Or.inl h2)
        (Nat.mul_le_mul_left a hmN)
  | zero =>
    change hilbertDilationLinear a ha 0 ∈ _
    rw [map_zero]
    exact (budgetHilbert (a*N)).zero_mem
  | add x y hx hy ihx ihy =>
    change hilbertDilationLinear a ha (x+y) ∈ _
    rw [map_add]
    exact (budgetHilbert (a*N)).add_mem ihx ihy
  | smul c x hx ih =>
    rw [hilbertDilation_smul]
    exact (budgetHilbert (a*N)).smul_mem c ih

def innovation (M p : ℕ) : ThresholdHilbert := fit (2*M/p) - fit (M/p)
def priorGain (M p : ℕ) : ℝ := distance (M/p) - distance (2*M/p)
def transported (M p : ℕ) (hp : 0 < p) : ThresholdHilbert :=
  hilbertDilation p hp (innovation M p)
def source (M p : ℕ) (hp : 0 < p) : ℝ :=
  inner ℝ (error M) (transported M p hp)

theorem innovation_norm_sq (M p : ℕ) :
    ‖innovation M p‖^2 = priorGain M p := by
  exact (distance_sub _ _ (Nat.div_le_div_right (by omega : M ≤ 2*M))).symm

theorem priorGain_nonneg (M p : ℕ) : 0 ≤ priorGain M p := by
  rw [← innovation_norm_sq]
  positivity

theorem transported_norm_sq (M p : ℕ) (hp : 0 < p) :
    ‖transported M p hp‖^2 = (p : ℝ) * priorGain M p := by
  rw [transported, hilbertDilation_norm_sq, innovation_norm_sq]

theorem dilation_fit_mem (K p : ℕ) (hp : 0 < p) :
    hilbertDilation p hp (fit (K/p)) ∈ budgetHilbert K := by
  exact budgetHilbert_mono (Nat.mul_div_le K p)
    (dilation_budget_mem p (K/p) hp _ ((budgetHilbert (K/p)).starProjection_apply_mem _))

theorem transported_mem (M p : ℕ) (hp : 0 < p) :
    transported M p hp ∈ budgetHilbert (2*M) := by
  unfold transported innovation
  change hilbertDilationLinear p hp (fit (2*M/p)-fit (M/p)) ∈ _
  rw [map_sub]
  exact (budgetHilbert (2*M)).sub_mem (dilation_fit_mem (2*M) p hp)
    (budgetHilbert_mono (by omega : M ≤ 2*M) (dilation_fit_mem M p hp))

theorem source_eq_dilated_fit (M p : ℕ) (hp : 0 < p) :
    source M p hp =
      inner ℝ (error M) (hilbertDilation p hp (fit (2*M/p))) := by
  have ho := Submodule.starProjection_inner_eq_zero hilbertOne
    (hilbertDilation p hp (fit (M/p))) (dilation_fit_mem M p hp)
  change inner ℝ (error M) (hilbertDilation p hp (fit (M/p))) = 0 at ho
  unfold source transported innovation
  change inner ℝ (error M)
    (hilbertDilationLinear p hp (fit (2*M/p)-fit (M/p))) = _
  rw [map_sub, inner_sub_right]
  change inner ℝ (error M) (hilbertDilation p hp (fit (2*M/p))) -
    inner ℝ (error M) (hilbertDilation p hp (fit (M/p))) = _
  rw [ho, sub_zero]

theorem source_residual_identity (M p : ℕ) (hp : 0 < p) :
    source M p hp =
      inner ℝ (error M) (hilbertDilation p hp hilbertOne) -
      inner ℝ (error M) (hilbertDilation p hp (error (2*M/p))) := by
  rw [source_eq_dilated_fit]
  have he : fit (2*M/p) = hilbertOne - error (2*M/p) := by unfold error; abel
  rw [he]
  change inner ℝ (error M) (hilbertDilationLinear p hp (_-_)) = _
  rw [map_sub, inner_sub_right]
  rfl

private theorem binary_target :
    hilbertDilation 2 (by omega) hilbertOne =
      (2:ℝ) • hilbertOne - (2:ℝ) • hilbertAtom 1 (by omega) := by
  apply hilbertSequence_injective
  funext n
  simp only [hilbertDilation_sequence, hilbertSequence_sub, hilbertSequence_smul,
    hilbertOne_sequence, hilbertAtom_sequence, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : n = 0
  · subst n; norm_num [dilation, zeroAnchor]
  by_cases h1 : n = 1
  · subst n; norm_num [dilation, zeroAnchor]
  have hd : n/2 ≠ 0 := by omega
  simp [dilation, zeroAnchor, h0, h1, hd]

private theorem ternary_target :
    hilbertDilation 3 (by omega) hilbertOne =
      (3:ℝ) • hilbertOne - (3:ℝ) • hilbertAtom 1 (by omega) -
        (3:ℝ) • hilbertAtom 2 (by omega) := by
  apply hilbertSequence_injective
  funext n
  simp only [hilbertDilation_sequence, hilbertSequence_sub, hilbertSequence_smul,
    hilbertOne_sequence, hilbertAtom_sequence, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : n = 0
  · subst n; norm_num [dilation, zeroAnchor]
  by_cases h1 : n = 1
  · subst n; norm_num [dilation, zeroAnchor]
  by_cases h2 : n = 2
  · subst n; norm_num [dilation, zeroAnchor]
  have hd : n/3 ≠ 0 := by omega
  simp [dilation, zeroAnchor, h0, h1, h2, hd]

/-- The head term comes from zero extension, not periodic extension. -/
theorem binary_source (M : ℕ) :
    source M 2 (by omega) =
      2*distance M - hilbertSequence (error M) 1 -
        inner ℝ (error M) (hilbertDilation 2 (by omega) (error M)) := by
  rw [source_residual_identity, binary_target, inner_sub_right,
    real_inner_smul_right, real_inner_smul_right, residual_target,
    real_inner_comm (hilbertAtom 1 (by omega)) (error M), hilbertAtom_inner]
  norm_num [positiveWeight, Nat.mul_div_cancel_left] <;> ring

theorem ternary_source (M : ℕ) :
    source M 3 (by omega) =
      3*distance M - (3/2:ℝ)*hilbertSequence (error M) 1 -
        (1/2:ℝ)*hilbertSequence (error M) 2 -
        inner ℝ (error M) (hilbertDilation 3 (by omega) (error (2*M/3))) := by
  rw [source_residual_identity, ternary_target, inner_sub_right, inner_sub_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    residual_target, real_inner_comm (hilbertAtom 1 (by omega)) (error M),
    hilbertAtom_inner, real_inner_comm (hilbertAtom 2 (by omega)) (error M),
    hilbertAtom_inner]
  norm_num [positiveWeight] <;> ring

/-- Finite budgets vanish at a genuine positive common period. This uses
the existing canonical spanning family, including the empty budget. -/
theorem budget_common_period_zero (M : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ budgetHilbert M) :
    hilbertSequence f (Nat.factorial (3*M+1)) = 0 := by
  rw [← canonicalHilbertFamily_span] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨hm, hmM, hs⟩ := (mem_canonicalIndices M i.val).mp i.property
    have hp : 0 < i.val.1 := by rcases hs with h | ⟨h, _⟩ <;> omega
    have hb : i.val.1 * i.val.2 ≤ 3*M+1 := by
      rcases hs with h | ⟨h, _⟩ <;> rw [h] <;> omega
    have hd := Nat.dvd_factorial (Nat.mul_pos hp hm) hb
    have hm' := Nat.dvd_factorial hm (by omega : i.val.2 ≤ 3*M+1)
    unfold canonicalHilbertFamily
    rw [generator_sequence_apply]
    simp [residue, Nat.mod_eq_zero_of_dvd hd, Nat.mod_eq_zero_of_dvd hm']
  | zero =>
    exact congrFun hilbertSequenceLinear.map_zero _
  | add x y hx hy ihx ihy => simp only [hilbertSequence_add, Pi.add_apply, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, ih, mul_zero]

theorem distance_pos (M : ℕ) : 0 < distance M := by
  apply sq_pos_of_ne_zero
  apply norm_ne_zero_iff.mpr
  intro hz
  have he : hilbertOne = fit M := sub_eq_zero.mp hz
  have hfit := budget_common_period_zero M (fit M)
    ((budgetHilbert M).starProjection_apply_mem hilbertOne)
  rw [← he, hilbertOne_sequence] at hfit
  simp [zeroAnchor, Nat.factorial_ne_zero] at hfit

/-- Cauchy--Schwarz against the actual next innovation, not the whole
old residual. This is the interscale inequality with exact floor indices. -/
theorem interscale_source_sq (M p : ℕ) (hp : 0 < p) :
    (source M p hp)^2 ≤
      ((p : ℝ) * priorGain M p) * gain M := by
  have h := nested_correlation_sq_le (budgetHilbert M) (budgetHilbert (2*M))
    (budgetHilbert_mono (by omega : M ≤ 2*M)) hilbertOne
    (transported M p hp) (transported_mem M p hp)
  change (source M p hp)^2 ≤ gain M * ‖transported M p hp‖^2 at h
  rw [transported_norm_sq, mul_comm] at h
  exact h

/-- The full signed raw Gram quadratic, including its mixed term. -/
theorem raw_gram_energy (M : ℕ) (a b : ℝ) :
    ‖a • transported M 2 (by omega) + b • transported M 3 (by omega)‖^2 =
      2*a^2*priorGain M 2 +
      2*a*b*inner ℝ (transported M 2 (by omega)) (transported M 3 (by omega)) +
      3*b^2*priorGain M 3 := by
  rw [pair_energy, transported_norm_sq, transported_norm_sq]
  norm_num
  ring

/-- Every entry of the screened Gram is the signed raw entry minus the
projected entry. Applies also to diagonal and singular cases. -/
theorem screened_gram (M p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    inner ℝ (residual (budgetHilbert M) (transported M p hp))
      (residual (budgetHilbert M) (transported M q hq)) =
    inner ℝ (transported M p hp) (transported M q hq) -
      inner ℝ ((budgetHilbert M).starProjection (transported M p hp))
        ((budgetHilbert M).starProjection (transported M q hq)) :=
  inner_residualized_eq_schur _ _ _

def trace (M : ℕ) : ℝ := 2*priorGain M 2 + 3*priorGain M 3
def sourceSquare (M : ℕ) : ℝ :=
  (source M 2 (by omega))^2 + (source M 3 (by omega))^2

theorem trace_gain (M : ℕ) (ht : 0 < trace M) :
    sourceSquare M / trace M ≤ gain M := by
  have h2 := interscale_source_sq M 2 (by omega)
  have h3 := interscale_source_sq M 3 (by omega)
  norm_num at h2 h3
  apply (div_le_iff₀ ht).mpr
  unfold sourceSquare trace
  nlinarith

/-- The manuscript's explicit correlation-normalized trace witness.
This is unconditional when the actual source vector is nonzero. -/
theorem trace_correction (M : ℕ) (hh : 0 < sourceSquare M) :
    let z := source M 2 (by omega) • transported M 2 (by omega) +
      source M 3 (by omega) • transported M 3 (by omega)
    let w := (distance M / sourceSquare M) • residual (budgetHilbert M) z
    inner ℝ (error M) w = distance M ∧
      ‖w‖^2 ≤ (distance M)^2 * trace M / sourceSquare M := by
  have h := pair_trace_witness (budgetHilbert M) hilbertOne
    (transported M 2 (by omega)) (transported M 3 (by omega)) (distance M) hh
  dsimp at h ⊢
  simpa only [transported_norm_sq, Nat.cast_ofNat, source, sourceSquare, trace,
    error, fit, RiemannResearch.Analysis.ProjectionSourceImprovement.residual] using h

/-- A genuine legal correction: membership and orthogonality accompany
the energy bound, not merely a formal coefficient calculation. -/
theorem exists_trace_correction (M : ℕ) (hh : 0 < sourceSquare M) :
    ∃ w : ThresholdHilbert,
      w ∈ budgetHilbert (2*M) ∧ w ∈ (budgetHilbert M)ᗮ ∧
      inner ℝ (error M) w = distance M ∧
      ‖w‖^2 ≤ (distance M)^2 * trace M / sourceSquare M := by
  let z := source M 2 (by omega) • transported M 2 (by omega) +
    source M 3 (by omega) • transported M 3 (by omega)
  let w := (distance M / sourceSquare M) • residual (budgetHilbert M) z
  have hz : z ∈ budgetHilbert (2*M) :=
    (budgetHilbert (2*M)).add_mem
      ((budgetHilbert (2*M)).smul_mem _ (transported_mem M 2 (by omega)))
      ((budgetHilbert (2*M)).smul_mem _ (transported_mem M 3 (by omega)))
  have hq : residual (budgetHilbert M) z ∈ budgetHilbert (2*M) :=
    (budgetHilbert (2*M)).sub_mem hz (budgetHilbert_mono (by omega : M ≤ 2*M)
      ((budgetHilbert M).starProjection_apply_mem z))
  have ho : residual (budgetHilbert M) z ∈ (budgetHilbert M)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal z
  exact ⟨w, (budgetHilbert (2*M)).smul_mem _ hq,
    ((budgetHilbert M)ᗮ).smul_mem _ ho, trace_correction M hh⟩

theorem reconstruction_optimum (M : ℕ) (hg : 0 < gain M) :
    ∃ w : ThresholdHilbert,
      w ∈ budgetHilbert (2*M) ∧ w ∈ (budgetHilbert M)ᗮ ∧
      inner ℝ (error M) w = distance M ∧ ‖w‖^2 = (distance M)^2 / gain M := by
  have h := optimal_normalized_increment (budgetHilbert M) (budgetHilbert (2*M))
    (budgetHilbert_mono (by omega : M ≤ 2*M)) hilbertOne (distance M) hg
  exact ⟨(distance M / gain M) • (fit (2*M)-fit M), h⟩

theorem reconstruction_lower (M : ℕ) (hg : 0 < gain M)
    (w : ThresholdHilbert) (hw : w ∈ budgetHilbert (2*M))
    (hc : inner ℝ (error M) w = distance M) :
    (distance M)^2 / gain M ≤ ‖w‖^2 :=
  feasible_cost_lower (budgetHilbert M) (budgetHilbert (2*M))
    (budgetHilbert_mono (by omega : M ≤ 2*M)) hilbertOne w hw (distance M) hc hg

theorem zero_gain_no_correction (M : ℕ) (hg : gain M = 0) :
    ¬ ∃ w ∈ budgetHilbert (2*M), inner ℝ (error M) w = distance M :=
  zero_gain_infeasible (budgetHilbert M) (budgetHilbert (2*M))
    (budgetHilbert_mono (by omega : M ≤ 2*M)) hilbertOne hg (distance M)
    (ne_of_gt (distance_pos M))

/-- Zero trace means both raw columns vanish. It says nothing about the
gain of the other fresh directions in the doubled budget. -/
theorem zero_trace (M : ℕ) (ht : trace M = 0) :
    transported M 2 (by omega) = 0 ∧ transported M 3 (by omega) = 0 ∧
      source M 2 (by omega) = 0 ∧ source M 3 (by omega) = 0 := by
  have h2 := transported_norm_sq M 2 (by omega)
  have h3 := transported_norm_sq M 3 (by omega)
  have hd2 := priorGain_nonneg M 2
  have hd3 := priorGain_nonneg M 3
  unfold trace at ht
  have hn2 : ‖transported M 2 (by omega)‖ = 0 := by
    norm_num at h2
    nlinarith [norm_nonneg (transported M 2 (by omega))]
  have hn3 : ‖transported M 3 (by omega)‖ = 0 := by
    norm_num at h3
    nlinarith [norm_nonneg (transported M 3 (by omega))]
  have hz2 := norm_eq_zero.mp hn2
  have hz3 := norm_eq_zero.mp hn3
  refine ⟨hz2, hz3, ?_, ?_⟩ <;> simp [source, hz2, hz3]

/-- A conditional research reduction. The hypothesis is the actual
distance lower envelope that still needs the analytic Burnol bridge. -/
theorem conditional_dyadic_log_budget (J N : ℕ) (c : ℝ) (hc : 0 < c)
    (hlower : c / ((N : ℝ)+1) ≤ distance (2^(J+N))) :
    (∑ j ∈ Finset.range N,
      -Real.log (1-RiemannResearch.Analysis.LogarithmicResidualBarrier.relativeGain
        (fun k => distance (2^(J+k))) j)) ≤
      Real.log (distance (2^J)/c) + Real.log ((N : ℝ)+1) := by
  simpa only [Nat.add_zero] using
    RiemannResearch.Analysis.LogarithmicResidualBarrier.log_gain_budget_of_distance_lower
      (fun k => distance (2^(J+k))) (fun k => distance_pos _) N c hc hlower

end RiemannResearch.RH.Pareto.CoupledResidual
