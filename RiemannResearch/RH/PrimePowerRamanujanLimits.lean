import RiemannResearch.RH.PrimePowerRamanujanSchur
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Limits and centered covariance for prime-power Ramanujan equations

This module combines the finite mixed-conductor Schur elimination with the
increasing-projection limit and the Pareto closed-space RH implication.
The screened packets converge unconditionally. The final implication retains
explicit mean and complete-covariance convergence hypotheses; it is not an
unconditional proof of RH.

Provenance: the full-conductor projection research agenda and the cited local
Schur, Ramanujan, and projection modules. Proofs use Mathlib Hilbert-space
projection and infinite-limit results.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.ExhaustiveWalk
open CoefficientStabilization

theorem mixedSpace_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    mixedSpace s ≤ mixedSpace t := by
  classical
  apply Submodule.span_mono
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨q.val, ?_⟩, rfl⟩
  obtain ⟨hq, hp⟩ := Finset.mem_filter.mp q.property
  exact Finset.mem_filter.mpr ⟨hst hq, hp⟩

def mixedClosure : Submodule ℝ ThresholdHilbert :=
  (⨆ N : ℕ, mixedSpace (Finset.Icc 2 N)).topologicalClosure

instance mixedClosure_hasOrthogonalProjection : mixedClosure.HasOrthogonalProjection := by
  unfold mixedClosure
  infer_instance

def limitScreenedPacket (q : ℕ) : ThresholdHilbert :=
  ramanujanPacketHilbert q - mixedClosure.starProjection (ramanujanPacketHilbert q)

theorem screenedPacket_tendsto (q : ℕ) :
    Tendsto (fun N => screenedPacket (Finset.Icc 2 N) q) atTop
      (𝓝 (limitScreenedPacket q)) := by
  have hmono : Monotone (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  exact tendsto_const_nhds.sub
    (Submodule.starProjection_tendsto_closure_iSup
      (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) hmono (ramanujanPacketHilbert q))

theorem limitScreenedPacket_inner_one (q : ℕ) :
    inner ℝ (limitScreenedPacket q) hilbertOne = ArithmeticFunction.vonMangoldt q := by
  have h : Tendsto (fun N => inner ℝ (screenedPacket (Finset.Icc 2 N) q) hilbertOne)
      atTop (𝓝 (inner ℝ (limitScreenedPacket q) hilbertOne)) :=
    (screenedPacket_tendsto q).inner tendsto_const_nhds
  simp only [screenedPacket_inner_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem mixedSpace_window_le_closure (N : ℕ) :
    mixedSpace (Finset.Icc 2 N) ≤ mixedClosure :=
  (le_iSup (fun n => mixedSpace (Finset.Icc 2 n)) N).trans
    (Submodule.le_topologicalClosure _)

theorem screenedPacket_norm_sq_decomposition (N q : ℕ) :
    ‖screenedPacket (Finset.Icc 2 N) q‖ ^ 2 =
      ‖limitScreenedPacket q‖ ^ 2 +
        ‖mixedClosure.starProjection (ramanujanPacketHilbert q) -
          (mixedSpace (Finset.Icc 2 N)).starProjection (ramanujanPacketHilbert q)‖ ^ 2 :=
  nested_projection_energy _ _ (mixedSpace_window_le_closure N) _

theorem screenedPacket_gram_tendsto (q r : ℕ) :
    Tendsto (fun N => inner ℝ (screenedPacket (Finset.Icc 2 N) q)
      (screenedPacket (Finset.Icc 2 N) r)) atTop
      (𝓝 (inner ℝ (limitScreenedPacket q) (limitScreenedPacket r))) :=
  (screenedPacket_tendsto q).inner (screenedPacket_tendsto r)

theorem packet_mem_closedSpace (q : ℕ) (hq : 1 < q) :
    ramanujanPacketHilbert q ∈ closedSpace := by
  rw [ramanujanPacketHilbert_eq_divisor_sum q hq]
  apply closedSpace.sum_mem
  intro d hd
  apply closedSpace.smul_mem
  unfold rawResidueAtom
  apply closedSpace.smul_mem
  exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (Submodule.subset_span ⟨d - 2, rfl⟩)

theorem mixedSpace_le_closedSpace (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    mixedSpace s ≤ closedSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  exact packet_mem_closedSpace q.val (hs q.val (Finset.mem_filter.mp q.property).1)

theorem mixedClosure_le_closedSpace : mixedClosure ≤ closedSpace := by
  apply Submodule.topologicalClosure_minimal
  · apply iSup_le
    intro N
    apply mixedSpace_le_closedSpace
    intro q hq
    exact lt_of_lt_of_le (by norm_num : 1 < 2) (Finset.mem_Icc.mp hq).1
  · exact isClosed_closure

theorem screenedPacket_mem_closedSpace (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (q : ℕ) (hq : 1 < q) :
    screenedPacket s q ∈ closedSpace :=
  closedSpace.sub_mem (packet_mem_closedSpace q hq)
    (mixedSpace_le_closedSpace s hs ((mixedSpace s).starProjection_apply_mem _))

theorem limitScreenedPacket_mem_closedSpace (q : ℕ) (hq : 1 < q) :
    limitScreenedPacket q ∈ closedSpace :=
  closedSpace.sub_mem (packet_mem_closedSpace q hq)
    (mixedClosure_le_closedSpace (mixedClosure.starProjection_apply_mem _))

def screenedCombination (s : Finset ℕ) (a : primeConductors s → ℝ) : ThresholdHilbert :=
  finiteSchurCombination (fun q : primeConductors s => screenedPacket s q.val) a

def screenedSource (s : Finset ℕ) (a : primeConductors s → ℝ) : ℝ :=
  ∑ q, a q * ArithmeticFunction.vonMangoldt q.val

def screenedCovariance (s : Finset ℕ) (a : primeConductors s → ℝ) : ℝ :=
  ∑ q, ∑ r, a q * a r *
    (inner ℝ (screenedPacket s q.val) (screenedPacket s r.val) -
      ArithmeticFunction.vonMangoldt q.val * ArithmeticFunction.vonMangoldt r.val)

theorem screenedCombination_inner_one (s : Finset ℕ) (a : primeConductors s → ℝ) :
    inner ℝ (screenedCombination s a) hilbertOne = screenedSource s a := by
  simp only [screenedCombination, finiteSchurCombination, sum_inner,
    real_inner_smul_left, screenedPacket_inner_one, screenedSource]

theorem screenedCovariance_eq (s : Finset ℕ) (a : primeConductors s → ℝ) :
    screenedCovariance s a =
      ‖screenedCombination s a‖ ^ 2 - (screenedSource s a) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [screenedCovariance, screenedCombination, finiteSchurCombination,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, screenedSource,
    pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [real_inner_comm (screenedPacket s q.val) (screenedPacket s r.val)]
  ring

theorem screened_error_mean_covariance (s : Finset ℕ) (a : primeConductors s → ℝ) :
    ‖hilbertOne - screenedCombination s a‖ ^ 2 =
      (1 - screenedSource s a) ^ 2 + screenedCovariance s a := by
  rw [screenedCovariance_eq, norm_sub_sq_real, hilbertOne_norm_sq,
    real_inner_comm (screenedCombination s a) hilbertOne, screenedCombination_inner_one]
  ring

theorem screenedCovariance_nonneg (s : Finset ℕ) (a : primeConductors s → ℝ) :
    0 ≤ screenedCovariance s a := by
  have h := real_inner_mul_inner_self_le (screenedCombination s a) hilbertOne
  rw [screenedCombination_inner_one, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq, mul_one] at h
  rw [screenedCovariance_eq]
  nlinarith

theorem screenedCombination_mem_closedSpace (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (a : primeConductors s → ℝ) :
    screenedCombination s a ∈ closedSpace := by
  apply closedSpace.sum_mem
  intro q hq
  apply closedSpace.smul_mem
  exact screenedPacket_mem_closedSpace s hs q.val
    (hs q.val (Finset.mem_filter.mp q.property).1)

/-- The only substantive hypothesis is the displayed complete covariance decay;
the mean may approach one rather than be exactly one at every stage. -/
theorem riemannHypothesis_of_screened_covariance
    (s : ℕ → Finset ℕ) (a : ∀ N, primeConductors (s N) → ℝ)
    (hs : ∀ N q, q ∈ s N → 1 < q)
    (hmean : Tendsto (fun N => screenedSource (s N) (a N)) atTop (𝓝 1))
    (hcov : Tendsto (fun N => screenedCovariance (s N) (a N)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have he : Tendsto (fun N => ‖hilbertOne - screenedCombination (s N) (a N)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [screened_error_mean_covariance, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      zero_add] using (((tendsto_const_nhds (x := (1 : ℝ))).sub hmean).pow 2).add hcov
  have hn : Tendsto (fun N => ‖hilbertOne - screenedCombination (s N) (a N)‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp he
  have hv : Tendsto (fun N => screenedCombination (s N) (a N)) atTop (𝓝 hilbertOne) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hn
  have hmem : hilbertOne ∈ closedSpace :=
    (show IsClosed (closedSpace : Set ThresholdHilbert) from isClosed_closure).mem_of_tendsto hv
      (Eventually.of_forall (fun N => screenedCombination_mem_closedSpace (s N) (hs N) (a N)))
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr hmem)

end RiemannResearch.RH.Pareto.PrimePowerSchur
