/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.SquarefreeCumulantLimit
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ZetaTwoCoordinateDual
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Physical Q realization of formal squarefree coefficient families
Source: the user's all-order cumulant/infinite-CRT request, 17 October 2026.
Synthesis uses literal residues and the full atomic-Q norm. It never
substitutes floor operators for square-zero variables.
The finite cumulant range is exactly the ordinary finite synthesis range.
Boundedness and strong realizability have separate exact complete-Gram tests.
Strong and weak physical limits stay in the old closed squarefree span.
A compatible singleton moment/cumulant family has unbounded physical norm.
Continuous finite-site Mobius functionals recover coefficients and separate
Q vectors. The final RH reduction retains its complete signed arithmetic
budget and exact growing heads as explicit Open hypotheses.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeFormalSynthesis
open RiemannResearch.NumberTheory.SquarefreeCumulantTower
open RiemannResearch.NumberTheory.SquarefreeCumulantLimit
open RiemannResearch.Analysis.FiniteHilbertGram
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets ArithmeticCumulative

def period (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => period p n*p n
def conductor (p : ℕ → ℕ) : (n : ℕ) → Index n → ℕ
  | 0, _ => 1
  | n+1, (b,s) => (if b then p n else 1)*conductor p n s
@[simp] theorem conductor_empty (p : ℕ → ℕ) : ∀ n,
    conductor p n (emptyIndex n) = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [conductor, emptyIndex] using ih
theorem conductor_dvd_period (p : ℕ → ℕ) : ∀ (n : ℕ) (s : Index n),
    conductor p n s ∣ period p n := by
  intro n
  induction n with
  | zero => intro s; exact dvd_rfl
  | succ n ih =>
    rintro ⟨b,s⟩
    cases b
    · simpa [conductor, period] using dvd_mul_of_dvd_left (ih s) (p n)
    · simpa [conductor, period, Nat.mul_comm] using Nat.mul_dvd_mul_left (p n) (ih s)
theorem period_pos (p : ℕ → ℕ) (hp : ∀ j, 0 < p j) : ∀ n, 0 < period p n := by
  intro n
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos ih (hp n)

/-- Linear synthesis by the literal residues, including every CRT carry. -/
def synthesisAt (p : ℕ → ℕ) (n m : ℕ) (a : Algebra n) : QHilbert :=
  ∑ s : Index n, coefficient n a s • qResidue (m*conductor p n s)
def synthesis (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) : QHilbert :=
  synthesisAt p n 1 a
def cumulantSynthesis (p : ℕ → ℕ) (n : ℕ) (k : Coordinates n) : QHilbert :=
  synthesis p n (moment n (expStar n k))

theorem synthesisAt_succ (p : ℕ → ℕ) (n m : ℕ) (a : Algebra (n + 1)) :
    synthesisAt p (n + 1) m a =
      synthesisAt p n m a.fst+synthesisAt p n (m*p n) a.snd := by
  simp only [synthesisAt]
  change (∑ s : Bool × Index n, _) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [coefficient, conductor, Bool.false_eq_true, ite_false, ite_true,
    Nat.one_mul, Nat.mul_assoc]
  exact add_comm _ _
@[simp] theorem synthesisAt_scalar (p : ℕ → ℕ) (n m : ℕ) (r : ℝ) :
    synthesisAt p n m (scalar n r) = r • qResidue m := by
  classical
  simp [synthesisAt, coefficient_scalar]

theorem synthesis_mem_stage (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) :
    synthesis p n a ∈ divisorStage (period p n) := by
  apply (divisorStage (period p n)).sum_mem
  intro s hs
  apply (divisorStage (period p n)).smul_mem
  exact Submodule.subset_span
    ⟨conductor p n s, conductor_dvd_period p n s, by simp⟩

theorem synthesis_legal (p : ℕ → ℕ) (n : ℕ) (a : Algebra n)
    (hpos : 0 < period p n) (hsf : Squarefree (period p n)) :
    synthesis p n a ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan _ hpos hsf (synthesis_mem_stage p n a)

/-- Normalize only the coefficient of the zero atom g_1. -/
def normalizedArray (n : ℕ) (a : Algebra n) : Algebra n :=
  assemble n (fun s => if s = emptyIndex n then 1 else coefficient n a s)
theorem normalizedArray_augmentation (n : ℕ) (a : Algebra n) :
    augmentation n (normalizedArray n a) = 1 := by
  rw [← coefficient_empty]
  simp [normalizedArray]
theorem synthesis_normalizedArray (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) :
    synthesis p n (normalizedArray n a) = synthesis p n a := by
  apply Finset.sum_congr rfl
  intro s hs
  simp only [normalizedArray, coefficient_assemble]
  by_cases h : s = emptyIndex n
  · subst s
    simp [qResidue_one]
  · simp [h]
/-- All cumulants together parameterize exactly the same finite legal functions. -/
theorem exists_cumulant_synthesis (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) :
    ∃ k : Coordinates n, cumulantSynthesis p n k = synthesis p n a := by
  refine ⟨logStar n (coordinatesOf n (normalizedArray n a)), ?_⟩
  unfold cumulantSynthesis
  rw [expStar_logStar, moment_coordinatesOf n _ (normalizedArray_augmentation n a),
    synthesis_normalizedArray]
theorem cumulant_synthesis_range (p : ℕ → ℕ) (n : ℕ) :
    Set.range (cumulantSynthesis p n) = Set.range (synthesis p n) := by
  ext f
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨moment n (expStar n k), rfl⟩
  · rintro ⟨a,rfl⟩
    exact exists_cumulant_synthesis p n a

def atom (p : ℕ → ℕ) (n : ℕ) (s : Index n) : QHilbert :=
  qResidue (conductor p n s)
def gramEnergy (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) : ℝ :=
  ∑ s : Index n, coefficient n a s *
    ∑ t : Index n, inner ℝ (atom p n s) (atom p n t)*coefficient n a t

theorem synthesis_norm_sq (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) :
    ‖synthesis p n a‖^2 = gramEnergy p n a := by
  simpa [synthesis, synthesisAt, atom, gramEnergy, gram_apply,
    Fintype.linearCombination_apply] using gram_quadratic (atom p n) (coefficient n a)

/-- Complete error, with all signed source correlations and all Gram entries. -/
theorem synthesis_error_exact (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) (t : QHilbert) :
    ‖t-synthesis p n a‖^2 = ‖t‖^2 -
      2*(∑ s : Index n, coefficient n a s*inner ℝ t (atom p n s)) +
        gramEnergy p n a := by
  rw [norm_sub_sq_real, synthesis_norm_sq]
  have hi : inner ℝ t (synthesis p n a) =
      ∑ s : Index n, coefficient n a s*inner ℝ t (atom p n s) := by
    simp [synthesis, synthesisAt, atom, inner_sum, real_inner_smul_right]
  rw [hi]

def crossEnergy (p : ℕ → ℕ) (m n : ℕ) (a : Algebra m) (b : Algebra n) : ℝ :=
  gramEnergy p m a+gramEnergy p n b-
    2*(∑ s : Index m, ∑ t : Index n,
      coefficient m a s*coefficient n b t*inner ℝ (atom p m s) (atom p n t))
theorem synthesis_difference_exact (p : ℕ → ℕ) (m n : ℕ)
    (a : Algebra m) (b : Algebra n) :
    ‖synthesis p m a-synthesis p n b‖^2 = crossEnergy p m n a b := by
  have hi : inner ℝ (synthesis p m a) (synthesis p n b) =
      ∑ s : Index m, ∑ t : Index n,
        coefficient m a s*coefficient n b t*inner ℝ (atom p m s) (atom p n t) := by
    simp only [synthesis, synthesisAt, Nat.one_mul]
    change inner ℝ (∑ s, coefficient m a s • atom p m s)
        (∑ t, coefficient n b t • atom p n t) = _
    rw [sum_inner]
    simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [norm_sub_sq_real, synthesis_norm_sq, synthesis_norm_sq, hi]
  unfold crossEnergy
  ring

/-- Exact criterion for uniform physical boundedness of a formal family. -/
theorem bounded_realization_iff (p : ℕ → ℕ) (a : Completion) :
    (∃ B : ℝ, ∀ n, ‖synthesis p n (a.val n)‖^2 ≤ B) ↔
      ∃ B : ℝ, ∀ n, gramEnergy p n (a.val n) ≤ B := by
  simp only [synthesis_norm_sq]

/-- Strong realizability is precisely the complete Gram Cauchy condition. -/
theorem strong_realization_iff (p : ℕ → ℕ) (a : Completion) :
    (∃ f : QHilbert, Tendsto (fun n => synthesis p n (a.val n)) atTop (𝓝 f)) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
        Real.sqrt (crossEnergy p m n (a.val m) (a.val n)) < ε := by
  have he (m n : ℕ) :
      Real.sqrt (crossEnergy p m n (a.val m) (a.val n)) =
        ‖synthesis p m (a.val m)-synthesis p n (a.val n)‖ := by
    rw [← synthesis_difference_exact, Real.sqrt_sq (norm_nonneg _)]
  simp only [he, ← dist_eq_norm]
  exact ⟨fun ⟨f,hf⟩ => Metric.cauchySeq_iff.mp hf.cauchySeq,
    fun h => cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr h)⟩

theorem strong_limit_mem_closed_span (F : ℕ → QHilbert) (f : QHilbert)
    (hF : ∀ n, F n ∈ qSquarefreeCRTSpan) (h : Tendsto F atTop (𝓝 f)) :
    f ∈ qSquarefreeCRTSpan.topologicalClosure :=
  qSquarefreeCRTSpan.isClosed_topologicalClosure.mem_of_tendsto h
    (Eventually.of_forall fun n => qSquarefreeCRTSpan.le_topologicalClosure (hF n))

/-- Even weak physical limits add no vector beyond the old closed legal span. -/
theorem weak_limit_mem_closed_span (F : ℕ → QHilbert) (f : QHilbert)
    (hF : ∀ n, F n ∈ qSquarefreeCRTSpan)
    (h : ∀ v : QHilbert, Tendsto (fun n => inner ℝ v (F n)) atTop (𝓝 (inner ℝ v f))) :
    f ∈ qSquarefreeCRTSpan.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ f).mpr
  intro v hv
  have hz (n : ℕ) : inner ℝ v (F n) = 0 :=
    (Submodule.mem_orthogonal' _ v).mp hv (F n) (hF n)
  have ht : Tendsto (fun n => inner ℝ v (F n)) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique (h v) ht

theorem singleton_synthesis (p : ℕ → ℕ) : ∀ n,
    synthesis p n (singletonArray (fun j => (p j : ℝ)) n) =
      ∑ j ∈ Finset.range n, (p j : ℝ) • qResidue (p j) := by
  intro n
  induction n with
  | zero => simp [synthesis, synthesisAt, coefficient, conductor, singletonArray, qResidue_one]
  | succ n ih =>
    unfold synthesis at ih ⊢
    rw [synthesisAt_succ]
    change synthesisAt p n 1 (singletonArray (fun j => (p j : ℝ)) n)+
      synthesisAt p n (1*p n) (scalar n (p n : ℝ)) = _
    rw [synthesisAt_scalar, Finset.sum_range_succ, ih]
    simp

theorem singleton_synthesis_at_one (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j) (n : ℕ) :
    qSequence (synthesis p n (singletonArray (fun j => (p j : ℝ)) n)) 1 = n := by
  rw [singleton_synthesis]
  change qSequenceLinear _ 1 = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    show ∀ d, qSequenceLinear (qResidue d) = residueFraction d from
      fun d => qSequence_qResidue d]
  change (∑ j ∈ Finset.range n, (p j : ℝ)*residueFraction (p j) 1) = _
  have he (j : ℕ) : (p j : ℝ)*residueFraction (p j) 1 = 1 := by
    have hpR : (p j : ℝ) ≠ 0 := by exact_mod_cast (show p j ≠ 0 by have := hp j; omega)
    simp [residueFraction, Nat.mod_eq_of_lt (show 1 < p j by have := hp j; omega), hpR]
  simp [he]

theorem singleton_norm_lower (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j) (n : ℕ) :
    (n : ℝ)^2 ≤ zetaTwo*‖synthesis p n (singletonArray (fun j => (p j : ℝ)) n)‖^2 := by
  have h := real_inner_mul_inner_self_le (qSiteRiesz 1)
    (synthesis p n (singletonArray (fun j => (p j : ℝ)) n))
  rw [qSiteRiesz_inner 1 (by omega), singleton_synthesis_at_one p hp,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    qSiteRiesz_norm_sq 1 (by omega)] at h
  simpa [pow_two] using h

/-- A compatible formal moment/cumulant family can have unbounded Q syntheses. -/
theorem singleton_not_bounded (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j) (B : ℝ) :
    ∃ n, B < ‖synthesis p n ((singletonCompletion (fun j => (p j : ℝ))).val n)‖^2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (zetaTwo*B) 1)
  refine ⟨n, ?_⟩
  by_contra hb
  have he := singleton_norm_lower p hp n
  have hh : (n : ℝ)^2 ≤ zetaTwo*B :=
    he.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hb) zetaTwo_pos.le)
  have hn1 : (1 : ℝ) < n := (le_max_right _ _).trans_lt hn
  have hnn : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  exact (not_lt_of_ge (hnn.trans hh)) ((le_max_left _ _).trans_lt hn)

/-- Continuous recovery of a legal residue coefficient from finitely many
physical sites. This is not the divisor-wavelet isometry. -/
def coefficientCLM (m : ℕ) : QHilbert →L[ℝ] ℝ :=
  -(Pareto.mobiusDifferenceCLM m).comp ZetaTwoParetoTransfer.toParetoCLM

theorem coefficientCLM_apply (m : ℕ) (f : QHilbert) :
    coefficientCLM m f =
      -∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d) : ℝ)*
        (qSequence f d-qSequence f (d-1)) := by
  simp [coefficientCLM, Pareto.mobiusDifferenceCLM_apply,
    Pareto.mobiusDifference, ZetaTwoParetoTransfer.toPareto_sequence]

theorem coefficientCLM_residue (m d : ℕ) (hm : 1 < m) (hd : 0 < d) :
    coefficientCLM m (qResidue d) = if m = d then 1 else 0 := by
  rw [coefficientCLM_apply]
  simp only [qSequence_qResidue]
  change -Pareto.mobiusDifference m (residueFraction d) = _
  have he : Pareto.mobiusDifference m (residueFraction d) =
      Pareto.mobiusDifference m (Pareto.residue d)/(d : ℝ) := by
    simp only [Pareto.mobiusDifference, residueFraction, Pareto.residue,
      div_sub_div_same, mul_div_assoc, Finset.sum_div]
  rw [he, Pareto.mobiusDifference_residue m d hm]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  split_ifs <;> simp_all

theorem coefficientCLM_one (m : ℕ) (hm : 0 < m) :
    coefficientCLM m qOne = -(ArithmeticFunction.moebius m : ℝ) := by
  change -Pareto.mobiusDifferenceCLM m
      (ZetaTwoParetoTransfer.toParetoCLM qOne) = _
  rw [ZetaTwoParetoTransfer.toParetoCLM_apply, ZetaTwoParetoTransfer.toPareto_qOne,
    Pareto.mobius_coordinate_one m hm]

theorem coefficient_tendsto_of_strong (F : ℕ → QHilbert) (f : QHilbert)
    (h : Tendsto F atTop (𝓝 f)) (m : ℕ) :
    Tendsto (fun n => coefficientCLM m (F n)) atTop (𝓝 (coefficientCLM m f)) :=
  (coefficientCLM m).continuous.tendsto f |>.comp h

/-- Conditional research reduction. The complete signed Gram budget and exact
growing physical heads are hypotheses; no provider for this bound is assumed. -/
theorem riemannHypothesis_of_bounded_cumulant_heads
    (p : ℕ → ℕ) (k : (n : ℕ) → Coordinates n)
    (hpos : ∀ n, 0 < period p n) (hsf : ∀ n, Squarefree (period p n))
    (hhead : ∀ n j, 0 < j → j ≤ n → qSequence (cumulantSynthesis p n (k n)) j = 1)
    (B : ℝ)
    (hbudget : ∀ n, ‖qOne‖ ^ 2 -
      2 * (∑ s : Index n, coefficient n (moment n (expStar n (k n))) s *
        inner ℝ qOne (atom p n s)) +
          gramEnergy p n (moment n (expStar n (k n))) ≤ B) : RiemannHypothesis := by
  have hb (n : ℕ) : ‖qOne-cumulantSynthesis p n (k n)‖^2 ≤ B := by
    change ‖qOne-synthesis p n (moment n (expStar n (k n)))‖^2 ≤ B
    rw [synthesis_error_exact]
    exact hbudget n
  exact (QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    (fun n => cumulantSynthesis p n (k n))
    (fun n => synthesis_legal p n _ (hpos n) (hsf n))
    hb hhead).2.2


/-- Literal atomic-Q values; modular carries remain in every residueFraction. -/
theorem synthesis_sequence (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) (k : ℕ) :
    qSequence (synthesis p n a) k =
      ∑ s : Index n, coefficient n a s*residueFraction (conductor p n s) k := by
  change qSequenceLinear (∑ s : Index n,
    coefficient n a s • qResidue (1*conductor p n s)) k = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Nat.one_mul, show ∀ d, qSequenceLinear (qResidue d) = residueFraction d from
      fun d => qSequence_qResidue d]

theorem synthesis_atomic_norm (p : ℕ → ℕ) (n : ℕ) (a : Algebra n) :
    ‖synthesis p n a‖^2 = ∑' k, positiveQWeight k*
      (∑ s : Index n, coefficient n a s*residueFraction (conductor p n s) k)^2 := by
  rw [qNorm_weighted_sq]
  simp only [synthesis_sequence]

def singletonCumulants (p : ℕ → ℕ) : CompletedCoordinates :=
  logStarLimit (singletonCoordinates (fun j => (p j : ℝ)))
theorem singleton_cumulant_synthesis (p : ℕ → ℕ) (n : ℕ) :
    cumulantSynthesis p n ((singletonCumulants p).val n) =
      synthesis p n (singletonArray (fun j => (p j : ℝ)) n) := by
  change synthesis p n (moment n (expStar n (logStar n
    (coordinatesOf n (singletonArray (fun j => (p j : ℝ)) n))))) = _
  rw [expStar_logStar, moment_coordinatesOf n _ (singletonArray_augmentation _ n)]

theorem compatible_cumulants_not_bounded (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j) (B : ℝ) :
    ∃ n, B < ‖cumulantSynthesis p n ((singletonCumulants p).val n)‖^2 := by
  simpa only [singleton_cumulant_synthesis, singletonCompletion] using
    singleton_not_bounded p hp B


/-- All legal-coefficient functionals together separate the entire Q Hilbert
space; no RH or density assumption is used. -/
theorem eq_zero_of_coefficients_zero (f : QHilbert)
    (h : ∀ m, 1 < m → coefficientCLM m f = 0) : f = 0 := by
  have hz : ZetaTwoParetoTransfer.toPareto f = 0 := by
    apply Pareto.eq_zero_of_mobius_coordinates_zero
    intro m hm
    have hh := h m hm
    change -Pareto.mobiusDifferenceCLM m (ZetaTwoParetoTransfer.toPareto f) = 0 at hh
    exact neg_eq_zero.mp hh
  have h0 : ZetaTwoParetoTransfer.toPareto (0 : QHilbert) = 0 :=
    map_zero ZetaTwoParetoTransfer.toParetoLinear
  apply qSequence_injective
  simpa only [ZetaTwoParetoTransfer.toPareto_sequence] using
    congrArg Pareto.hilbertSequence (hz.trans h0.symm)

theorem coefficients_injective (f g : QHilbert)
    (h : ∀ m, 1 < m → coefficientCLM m f = coefficientCLM m g) : f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_coefficients_zero
  intro m hm
  rw [map_sub, h m hm, sub_self]

/-- The formal target moments are known unconditionally, but a legal physical
realization of them is precisely the outstanding closure question. -/
theorem coefficients_eq_mobius_iff (f : QHilbert) :
    (∀ m, 1 < m → coefficientCLM m f = -(ArithmeticFunction.moebius m : ℝ)) ↔
      f = qOne := by
  constructor
  · intro h
    apply coefficients_injective
    intro m hm
    rw [h m hm, coefficientCLM_one m (by omega)]
  · rintro rfl m hm
    exact coefficientCLM_one m (by omega)


/-- Once a physical strong limit exists, identifying every fixed residue
coefficient limit as minus Moebius is equivalent to identifying that limit
as the constant target. This does not supply the arithmetic identification. -/
theorem strong_limit_eq_one_iff_coefficients_tendsto
    (F : ℕ → QHilbert) (f : QHilbert)
    (hF : Tendsto F atTop (𝓝 f)) :
    f = qOne ↔ ∀ m, 1 < m →
      Tendsto (fun n => coefficientCLM m (F n)) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ))) := by
  constructor
  · rintro rfl m hm
    simpa only [coefficientCLM_one m (by omega)] using
      coefficient_tendsto_of_strong F qOne hF m
  · intro h
    apply (coefficients_eq_mobius_iff f).mp
    intro m hm
    exact tendsto_nhds_unique
      (coefficient_tendsto_of_strong F f hF m) (h m hm)

end RiemannResearch.RH.QSquarefreeFormalSynthesis
