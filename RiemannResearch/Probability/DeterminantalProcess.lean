import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Determinantal laws and a genuine random single-hole process

Source: the user-provided `RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction`
handoff, Sections 1 and 5. The finite-correlation definition is standard DPP
terminology; see Hough--Krishnapur--Peres--Virag, *Determinantal Processes and
Independence*, arXiv:math/0503110. The proof below constructs the rank-one
process directly from a probability mass function and checks every finite
correlation determinant. It does not assume a general DPP existence theorem.

This real-kernel construction applies to every finite or countable ground set
(and, formally, to any type equipped with measurable singletons). A complex
rank-one kernel with phases has the same principal minors as the nonnegative
amplitude kernel used here.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical ENNReal

namespace RiemannResearch.Probability.DPP

variable {α Ω : Type*} [MeasurableSpace Ω]

/-- A random subset is determinantal when every finite inclusion probability is
the corresponding principal determinant. Injections prevent repeated sites. -/
structure IsDPP (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Set α) (K : α → α → ℝ) : Prop where
  measurable_occupancy : ∀ i, MeasurableSet {ω | i ∈ X ω}
  correlation : ∀ (n : ℕ) (e : Fin n ↪ α),
    μ.real {ω | ∀ i, e i ∈ X ω} =
      Matrix.det (Matrix.of (fun (i j : Fin n) => K (e i) (e j)))

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Set α} {K : α → α → ℝ}

/-- One-point inclusion probabilities are exactly the kernel diagonal. -/
theorem IsDPP.occupation (h : IsDPP μ X K) (i : α) :
    μ.real {ω | i ∈ X ω} = K i i := by
  let e : Fin 1 ↪ α := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  have he (j : Fin 1) : e j = i := rfl
  simpa only [Matrix.det_fin_one, Matrix.of_apply, he, forall_const] using h.correlation 1 e

/-- The probability of a hole is one minus the occupation diagonal. -/
theorem IsDPP.vacancy (h : IsDPP μ X K) (i : α) :
    μ.real {ω | i ∉ X ω} = 1 - K i i := by
  change μ.real ({ω | i ∈ X ω}ᶜ) = _
  rw [probReal_compl_eq_one_sub (h.measurable_occupancy i), h.occupation i]

/-- The stochastic interpretation supplies the elementary diagonal bounds. -/
theorem IsDPP.diagonal_bounds (h : IsDPP μ X K) (i : α) :
    0 ≤ K i i ∧ K i i ≤ 1 := by
  constructor
  · rw [← h.occupation i]
    exact ENNReal.toReal_nonneg
  · have hv : 0 ≤ μ.real {ω | i ∉ X ω} := ENNReal.toReal_nonneg
    rw [h.vacancy i] at hv
    linarith

/-- Diagonal saturation is equivalent to almost-sure occupation at that site. -/
theorem IsDPP.mem_ae_iff (h : IsDPP μ X K) (i : α) :
    (∀ᵐ ω ∂μ, i ∈ X ω) ↔ K i i = 1 := by
  rw [ae_iff, ← measureReal_eq_zero_iff, h.vacancy i]
  constructor <;> intro hi <;> linarith

/-- On a countable ground set, saturation of every diagonal means the whole
ground set is occupied almost surely; no independence is needed. -/
theorem IsDPP.full_occupation_ae_iff [Countable α] (h : IsDPP μ X K) :
    (∀ᵐ ω ∂μ, X ω = Set.univ) ↔ ∀ i, K i i = 1 := by
  have he : (fun ω => X ω = Set.univ) = (fun ω => ∀ i, i ∈ X ω) := by
    funext ω
    exact propext Set.eq_univ_iff_forall
  rw [he, ae_all_iff]
  exact forall_congr' fun i => h.mem_ae_iff i

section RankOne


/-- The canonical nonnegative amplitude of a probability mass function. -/
def amplitude (p : PMF α) (i : α) : ℝ := Real.sqrt (p i).toReal

theorem amplitude_sq (p : PMF α) (i : α) :
    amplitude p i * amplitude p i = (p i).toReal :=
  Real.mul_self_sqrt ENNReal.toReal_nonneg

/-- The rank-one kernel whose diagonal is the given probability mass function. -/
def rankOneKernel (p : PMF α) (i j : α) : ℝ := amplitude p i * amplitude p j

/-- The identity minus the rank-one kernel. -/
def singleHoleKernel (p : PMF α) (i j : α) : ℝ :=
  (if i = j then 1 else 0) - rankOneKernel p i j

theorem rankOneKernel_diagonal (p : PMF α) (i : α) :
    rankOneKernel p i i = (p i).toReal := amplitude_sq p i

theorem pmf_real_mass_one (p : PMF α) : ∑' i, (p i).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe]
  simp

theorem amplitude_square_summable (p : PMF α) :
    Summable (fun i => amplitude p i * amplitude p i) := by
  simpa only [amplitude_sq] using ENNReal.summable_toReal p.tsum_coe_ne_top

theorem rankOneKernel_symmetric (p : PMF α) (i j : α) :
    rankOneKernel p i j = rankOneKernel p j i := mul_comm _ _

/-- The countable kernel is idempotent, so this is a projection DPP. -/
theorem rankOneKernel_idempotent (p : PMF α) (i j : α) :
    (∑' k, rankOneKernel p i k * rankOneKernel p k j) = rankOneKernel p i j := by
  calc
    _ = ∑' k, (amplitude p i * amplitude p j) * (p k).toReal := by
      apply tsum_congr
      intro k
      rw [← amplitude_sq p k]
      dsimp [rankOneKernel]
      ring
    _ = (amplitude p i * amplitude p j) * ∑' k, (p k).toReal := tsum_mul_left
    _ = rankOneKernel p i j := by rw [pmf_real_mass_one, mul_one]; rfl

theorem rankOneKernel_trace (p : PMF α) : ∑' i, rankOneKernel p i i = 1 := by
  simpa only [rankOneKernel_diagonal] using pmf_real_mass_one p

/-- Actual probability law of the singleton random set. -/
def singletonLaw (p : PMF α) : PMF (Set α) := p.map fun i => {i}

/-- Actual probability law of the complement of that singleton. -/
def singleHoleLaw (p : PMF α) : PMF (Set α) := p.map fun i => ({i} : Set α)ᶜ

theorem singleHoleLaw_eq_complement_map (p : PMF α) :
    singleHoleLaw p = (singletonLaw p).map Set.compl := by
  change p.map (fun i => ({i} : Set α)ᶜ) =
    (p.map (fun i => ({i} : Set α))).map Set.compl
  rw [PMF.map_comp]
  rfl

/-- Determinant of every finite restriction of the single-hole kernel. -/
theorem singleHoleKernel_det (p : PMF α) (n : ℕ) (e : Fin n ↪ α) :
    Matrix.det (Matrix.of (fun (i j : Fin n) => singleHoleKernel p (e i) (e j))) =
      1 - ∑ i, (p (e i)).toReal := by
  classical
  let u : Fin n → ℝ := fun i => amplitude p (e i)
  let A : Matrix (Fin n) (Fin 1) ℝ := Matrix.of (fun i _ => u i)
  let B : Matrix (Fin 1) (Fin n) ℝ := Matrix.of (fun _ j => u j)
  have hAB : A * B = Matrix.vecMulVec u u := by
    ext i j
    rw [Matrix.mul_apply]
    simp [A, B, Matrix.of_apply, Matrix.vecMulVec]
  have hK : Matrix.of (fun (i j : Fin n) => singleHoleKernel p (e i) (e j)) =
      1 - A * B := by
    rw [hAB]
    ext i j
    simp [Matrix.of_apply, Matrix.sub_apply, singleHoleKernel, rankOneKernel, u,
      Matrix.one_apply, Matrix.vecMulVec, e.injective.eq_iff]
  rw [hK, Matrix.det_one_sub_mul_comm, Matrix.det_fin_one]
  rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp only [A, B, Matrix.of_apply, u, amplitude_sq]

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Sampling one site with law `p` is a DPP, with every finite correlation
checked, not merely its one-point marginals. -/
theorem singleton_isDPP (p : PMF α) :
    IsDPP p.toMeasure (fun i => ({i} : Set α)) (rankOneKernel p) := by
  classical
  constructor
  · intro i
    have he : {j : α | i ∈ ({j} : Set α)} = {i} := by ext j; simp [eq_comm]
    rw [he]
    exact measurableSet_singleton i
  · intro n e
    rcases n with _ | n
    · simp [Matrix.det_fin_zero]
    rcases n with _ | n
    · have he : {j : α | ∀ i : Fin 1, e i ∈ ({j} : Set α)} = {e 0} := by
        ext j
        simp [eq_comm]
      rw [he, Matrix.det_fin_one, Matrix.of_apply, rankOneKernel_diagonal]
      exact congrArg ENNReal.toReal
        (p.toMeasure_apply_singleton (e 0) (measurableSet_singleton _))
    · have he : {j : α | ∀ i : Fin (n + 1 + 1), e i ∈ ({j} : Set α)} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hij : e (0 : Fin (n + 1 + 1)) = e (1 : Fin (n + 1 + 1)) :=
          (hj 0).trans (hj 1).symm
        have h01 := e.injective hij
        have hvals := congrArg Fin.val h01
        norm_num at hvals
      rw [he]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      change (0 : ℝ) = (Matrix.vecMulVec
        (fun i => amplitude p (e i)) (fun i => amplitude p (e i))).det
      exact (Matrix.det_vecMulVec _ _).symm

/-- A finite list of distinct sites has total mass equal to the sum of the
individual site probabilities. -/
theorem pmf_mass_range (p : PMF α) (n : ℕ) (e : Fin n ↪ α) :
    p.toMeasure.real (Set.range e) = ∑ i, (p (e i)).toReal := by
  classical
  rw [← Set.iUnion_singleton_eq_range]
  rw [measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro i hi
    exact congrArg ENNReal.toReal
      (p.toMeasure_apply_singleton (e i) (measurableSet_singleton _))
  · intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    exact hij (e.injective ((Set.mem_singleton_iff.mp hxi).symm.trans
      (Set.mem_singleton_iff.mp hxj)))
  · intro i
    exact measurableSet_singleton _

/-- The complement of the one-particle DPP is an actual DPP with kernel
`I - rankOneKernel p`. In particular persistent holes obey DPP laws. -/
theorem singleHole_isDPP (p : PMF α) :
    IsDPP p.toMeasure (fun i => ({i} : Set α)ᶜ) (singleHoleKernel p) := by
  classical
  constructor
  · intro i
    have he : {j : α | i ∈ ({j} : Set α)ᶜ} = ({i} : Set α)ᶜ := by
      ext j
      simp [eq_comm]
    rw [he]
    exact (measurableSet_singleton i).compl
  · intro n e
    have he : {j : α | ∀ i : Fin n, e i ∈ ({j} : Set α)ᶜ} =
        (Set.range e)ᶜ := by
      ext j
      simp [Set.mem_range, eq_comm]
    rw [he, probReal_compl_eq_one_sub (Set.finite_range e).measurableSet,
      pmf_mass_range p n e, singleHoleKernel_det p n e]

/-- For the single-hole process the vacancy at site `i` is exactly `p i`. -/
theorem singleHole_vacancy (p : PMF α) (i : α) :
    p.toMeasure.real {j | i ∉ ({j} : Set α)ᶜ} = (p i).toReal := by
  rw [(singleHole_isDPP p).vacancy]
  simp [singleHoleKernel, rankOneKernel_diagonal]

/-- A summable nonnegative weight function gives the exact normalized hole law.
For the Mellin mode take `a n = ENNReal.ofReal (norm m_n ^ 2 / w_n)`; the
analytic module must supply the two explicitly stated normalization bounds. -/
theorem normalized_singleHole_vacancy (a : α → ℝ≥0∞)
    (ha0 : (∑' i, a i) ≠ 0) (ha_top : (∑' i, a i) ≠ ∞) (i : α) :
    (PMF.normalize a ha0 ha_top).toMeasure.real
      {j | i ∉ ({j} : Set α)ᶜ} = (a i).toReal / (∑' j, a j).toReal := by
  rw [singleHole_vacancy (PMF.normalize a ha0 ha_top) i,
    PMF.normalize_apply, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv]

end RankOne

end RiemannResearch.Probability.DPP
