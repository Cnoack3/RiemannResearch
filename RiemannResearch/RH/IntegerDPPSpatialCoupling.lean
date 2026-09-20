import RiemannResearch.Probability.CompactProbabilityConstraints
import RiemannResearch.RH.IntegerDPPCoupling

/-!
# Arithmetic spatial coupling reduced to finite transport

Source: user-requested specialization to nested arithmetic projections.
Lyons, https://arxiv.org/abs/math/0204325, Theorems 6.2 and 7.1, support
the intended domination route, not a claim that it is proved here.
Compactness assembles finite space-time witnesses without any compatibility
assumption; running unions make the resulting paths pointwise increasing.
The reverse restriction theorem makes the finite obligation exact.

OPEN: a provider of SpatialWindowFeasible. No unconditional full spatial
coupling, weighted-vacancy estimate, zero vacancy, or RH is proved here.
See SpatialCouplingStatus.md for the precise remaining finite transport task.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP
abbrev SpatialPath := ℕ → ℕ → Bool
abbrev SpatialConstraint := (ℕ × (Σ m : ℕ, Fin m ↪ ℕ)) ⊕ (ℕ × ℕ)
def spatialEvent : SpatialConstraint → Set SpatialPath
  | .inl (n, ⟨_, e⟩) => {ω | ∀ i, ω n (e i) = true}
  | .inr (n, k) => {ω | ω n k = true ∧ ω (n+1) k = false}
def spatialTarget : SpatialConstraint → ℝ
  | .inl (n, ⟨_, e⟩) => Matrix.det (Matrix.of (fun i j => integerKernel n (e i) (e j)))
  | .inr _ => 0
theorem spatialEvent_clopen (c : SpatialConstraint) : IsClopen (spatialEvent c) := by
  have h (n k : ℕ) (b : Bool) : IsClopen {ω : SpatialPath | ω n k = b} :=
    (isClopen_discrete ({b} : Set Bool)).preimage
      ((continuous_apply k).comp (continuous_apply n))
  rcases c with ⟨n, m, e⟩ | ⟨n, k⟩
  · convert isClopen_iInter_of_finite (fun i : Fin m => h n (e i) true) using 1
    ext ω
    simp [spatialEvent]
  · exact (h n k true).inter (h (n+1) k false)
end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP
/-- Exact finite feasibility obligation; not supplied by kernel PSD order alone. -/
def SpatialFiniteFeasible : Prop :=
  ∀ F : Finset SpatialConstraint, ∃ μ : ProbabilityMeasure SpatialPath,
    ∀ c ∈ F, (μ : Measure SpatialPath).real (spatialEvent c) = spatialTarget c

def spatialProcess (n : ℕ) (ω : SpatialPath) : Set ℕ :=
  pastUnion (fun j ω => {k | ω j k = true}) n ω

theorem spatialProcess_monotone (n : ℕ) (ω : SpatialPath) :
    spatialProcess n ω ⊆ spatialProcess (n+1) ω :=
  pastUnion_mono _ n ω

/-- Compactness supplies the countable coupling once all finite probability
constraints are feasible; it does not assume consistency of witnesses. -/
theorem exists_spatialCoupling_of_finite_constraints (h : SpatialFiniteFeasible) :
    ∃ μ : ProbabilityMeasure SpatialPath,
      ∀ n, IsDPP (μ : Measure SpatialPath) (spatialProcess n) (integerKernel n) := by
  obtain ⟨μ, hμ⟩ := RiemannResearch.Probability.exists_probabilityMeasure_clopen_constraints
    spatialEvent spatialTarget spatialEvent_clopen h
  have hdpp (n : ℕ) : IsDPP (μ : Measure SpatialPath)
      (fun ω => {k | ω n k = true}) (integerKernel n) := by
    constructor
    · intro k
      exact (measurableSet_singleton true).preimage
        ((measurable_pi_apply k).comp (measurable_pi_apply n))
    · intro m e
      exact hμ (.inl (n, ⟨m, e⟩))
  have hstep (n k : ℕ) :
      ∀ᵐ ω ∂(μ : Measure SpatialPath), ω n k = true → ω (n+1) k = true := by
    have hz : (μ : Measure SpatialPath) {ω | ω n k = true ∧ ω (n+1) k = false} = 0 :=
      by
        rw [← measureReal_eq_zero_iff]
        exact hμ (.inr (n,k))
    have hn : ∀ᵐ ω ∂(μ : Measure SpatialPath),
        ¬ (ω n k = true ∧ ω (n+1) k = false) := by
      rw [ae_iff]
      simpa only [not_not] using hz
    filter_upwards [hn] with ω hω hk
    cases hv : ω (n+1) k <;> simp_all
  have hm : ∀ᵐ ω ∂(μ : Measure SpatialPath),
      ∀ n, {k | ω n k = true} ⊆ {k | ω (n+1) k = true} := by
    apply ae_all_iff.mpr
    intro n
    exact ae_all_iff.mpr (hstep n)
  exact ⟨μ, isDPP_pastUnion _ integerKernel hdpp hm⟩
end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP
abbrev SpatialWindow (N : ℕ) := Fin N → Fin N → Bool

/-- A finite square transport problem. All row laws must retain their full
determinantal correlations, and no site may disappear between adjacent rows. -/
def SpatialWindowFeasible : Prop :=
  ∀ N : ℕ, ∃ μ : ProbabilityMeasure (SpatialWindow N),
    (∀ n : Fin N, IsDPP (μ : Measure (SpatialWindow N))
      (fun ω => {k | ω n k = true})
      (fun i j : Fin N => integerKernel n.val i.val j.val)) ∧
    (∀ (n k : Fin N) (hn : n.val + 1 < N),
      (μ : Measure (SpatialWindow N)).real
        {ω | ω n k = true ∧ ω ⟨n.val+1, hn⟩ k = false} = 0)

def extendSpatialWindow (N : ℕ) (ω : SpatialWindow N) : SpatialPath :=
  fun n k => if hn : n < N then
    if hk : k < N then ω ⟨n, hn⟩ ⟨k, hk⟩ else false else false

def spatialBound : SpatialConstraint → ℕ
  | .inl (n, ⟨_, e⟩) => max n (Finset.univ.sup e) + 1
  | .inr (n, k) => max (n+1) k + 1

/-- Finite rectangular witnesses suffice; no projective compatibility is assumed. -/
theorem spatialFiniteFeasible_of_windows (h : SpatialWindowFeasible) :
    SpatialFiniteFeasible := by
  classical
  intro F
  let N := F.sup spatialBound
  obtain ⟨μ, hdpp, hstep⟩ := h N
  have hm : Measurable (extendSpatialWindow N) := measurable_of_finite _
  let ν : ProbabilityMeasure SpatialPath :=
    ⟨Measure.map (extendSpatialWindow N) (μ : Measure (SpatialWindow N)),
      Measure.isProbabilityMeasure_map hm.aemeasurable⟩
  refine ⟨ν, ?_⟩
  intro c hc
  have hb : spatialBound c ≤ N := Finset.le_sup hc
  change ((Measure.map (extendSpatialWindow N)
    (μ : Measure (SpatialWindow N))) (spatialEvent c)).toReal = _
  rw [Measure.map_apply hm (spatialEvent_clopen c).1.measurableSet]
  rcases c with ⟨n, m, e⟩ | ⟨n, k⟩
  · have hn : n < N := by
      have : n ≤ max n (Finset.univ.sup e) := le_max_left _ _
      change max n (Finset.univ.sup e) + 1 ≤ N at hb
      omega
    have hi : ∀ i : Fin m, e i < N := by
      intro i
      have hle : e i ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ i)
      have : Finset.univ.sup e ≤ max n (Finset.univ.sup e) := le_max_right _ _
      change max n (Finset.univ.sup e) + 1 ≤ N at hb
      omega
    let eN : Fin m ↪ Fin N :=
      ⟨fun i => ⟨e i, hi i⟩, fun i j hij => e.injective (congrArg Fin.val hij)⟩
    have hcor := (hdpp ⟨n, hn⟩).correlation m eN
    change (μ : Measure (SpatialWindow N)).real
      {ω | ∀ i, ω ⟨n, hn⟩ ⟨e i, hi i⟩ = true} =
        Matrix.det (Matrix.of (fun i j => integerKernel n (e i) (e j))) at hcor
    simpa [Measure.real, spatialEvent, spatialTarget, extendSpatialWindow, hn, hi]
      using hcor
  · have hn : n < N := by
      have := le_max_left (n+1) k
      change max (n+1) k + 1 ≤ N at hb
      omega
    have hs : n+1 < N := by
      have := le_max_left (n+1) k
      change max (n+1) k + 1 ≤ N at hb
      omega
    have hk : k < N := by
      have := le_max_right (n+1) k
      change max (n+1) k + 1 ≤ N at hb
      omega
    simpa [Measure.real, spatialEvent, spatialTarget, extendSpatialWindow, hn, hs, hk]
      using hstep ⟨n, hn⟩ ⟨k, hk⟩ hs

theorem exists_spatialCoupling_of_windows (h : SpatialWindowFeasible) :
    ∃ μ : ProbabilityMeasure SpatialPath,
      ∀ n, IsDPP (μ : Measure SpatialPath) (spatialProcess n) (integerKernel n) :=
  exists_spatialCoupling_of_finite_constraints (spatialFiniteFeasible_of_windows h)
end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP
/-- Restricting an actual coupling supplies every finite square witness. -/
theorem spatialWindowFeasible_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Set ℕ) (hZ : ∀ n, IsDPP μ (Z n) (integerKernel n))
    (hmono : ∀ n ω, Z n ω ⊆ Z (n+1) ω) : SpatialWindowFeasible := by
  classical
  intro N
  let f : Ω → SpatialWindow N := fun ω n k => if k.val ∈ Z n.val ω then true else false
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro n
    apply measurable_pi_lambda
    intro k
    exact Measurable.ite ((hZ n.val).measurable_occupancy k.val)
      measurable_const measurable_const
  let ν : ProbabilityMeasure (SpatialWindow N) :=
    ⟨Measure.map f μ, Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  refine ⟨ν, ?_, ?_⟩
  · intro n
    constructor
    · intro k
      exact (Set.toFinite _).measurableSet
    · intro m e
      let eN : Fin m ↪ ℕ := e.trans ⟨Fin.val, Fin.val_injective⟩
      change ((Measure.map f μ) {ω | ∀ i, ω n (e i) = true}).toReal = _
      rw [Measure.map_apply hf (Set.toFinite _).measurableSet]
      simpa [f, Measure.real, eN] using (hZ n.val).correlation m eN
  · intro n k hn
    change ((Measure.map f μ) {ω | ω n k = true ∧ ω ⟨n.val+1, hn⟩ k = false}).toReal = 0
    rw [Measure.map_apply hf (Set.toFinite _).measurableSet]
    have he : f ⁻¹' {ω | ω n k = true ∧ ω ⟨n.val+1, hn⟩ k = false} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      simp only [f, ite_eq_left_iff, Bool.false_eq_true, imp_false,
        not_not, ite_eq_right_iff, Bool.true_eq_false]
      exact fun hh => hh.2 (hmono n.val ω hh.1)
    rw [he, measure_empty, ENNReal.toReal_zero]

/-- Exact remaining finite obligation for the canonical countable construction. -/
theorem spatialWindowFeasible_iff_exists_spatialCoupling :
    SpatialWindowFeasible ↔ ∃ μ : ProbabilityMeasure SpatialPath,
      ∀ n, IsDPP (μ : Measure SpatialPath) (spatialProcess n) (integerKernel n) := by
  constructor
  · exact exists_spatialCoupling_of_windows
  · rintro ⟨μ, hμ⟩
    exact spatialWindowFeasible_of_coupling (μ : Measure SpatialPath)
      spatialProcess hμ spatialProcess_monotone
end RiemannResearch.RH.Pareto.IntegerDPP
