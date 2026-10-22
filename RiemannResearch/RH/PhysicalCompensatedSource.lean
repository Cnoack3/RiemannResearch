import RiemannResearch.RH.PhysicalScreenedSource
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.Analysis.FiniteGramSourceTranslation
import RiemannResearch.Analysis.FiniteGramBasisInvariance

/-!
# Concrete complete-tail target and observed physical source radius

Source: `crt_complete_tail_certificate.txt`, Section 4, equations (4.6),
(4.10)--(4.11), and RH_Actual_Arithmetic_Advances_2026-10-07.pdf.
All packets, cutoffs, projections, full Gram capacities and source vectors
are literal existing physical objects. Tail-old projection is constructed
from a finite-dimensional span; no supplied tail inverse or norm bound is
needed. Its complete target error is bounded by the exact 1/(N+1) allowance.
The old legality and odd-prime hypotheses from PhysicalSourceProjection
identify projectionCoefficients with the actual old Gram projection; the
radius inequality itself is valid without assuming an odd prime.

The source radius uses the norm of the observation of this target error,
with the complete unobserved residual square subtracted exactly. These
declarations compare capacities of the literal actual screened source and
its translated source. The following sections identify the full capacity
with E_old-E_new and the translated source with observations of the literal
head plus the complete old-tail fit. Cumulative certificate divergence
remains an Open arithmetic provider.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PhysicalCompensatedSource

open PhysicalPacketCore PhysicalSourceProjection PhysicalScreenedSource
open PhysicalSchurReindex
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open CoefficientStabilization

/-- The actual complete Pareto Hilbert family at an arbitrary finite packet set. -/
def packetFamily (s : Finset ℕ) : s → ThresholdHilbert :=
  fun q => ramanujanPacketHilbert q.val

/-- The Hilbert Gram action is the already constructed literal physical Gram. -/
theorem packetFamily_gram (s : Finset ℕ) (c : s → ℝ) :
    gram (packetFamily s) c = ramanujanGramAction s c := by
  funext i
  rw [RiemannResearch.Analysis.FiniteHilbertGram.gram_apply]
  change (∑ j : s, inner ℝ (ramanujanPacketHilbert i.val)
    (ramanujanPacketHilbert j.val) * c j) =
      ∑ j : s, paretoInner (ramanujanPacket i.val) (ramanujanPacket j.val) * c j
  simp_rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert]

/-- Existing actual packet Gram injectivity supplies finite Hilbert independence. -/
theorem packetFamily_independent (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    LinearIndependent ℝ (packetFamily s) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hsyn : Fintype.linearCombination ℝ (packetFamily s) c = 0 := by
    simpa only [Fintype.linearCombination_apply] using hc
  have hzero : gram (packetFamily s) c = 0 := by
    funext i
    change inner ℝ (packetFamily s i)
      (Fintype.linearCombination ℝ (packetFamily s) c) = 0
    rw [hsyn, inner_zero_right]
  rw [packetFamily_gram] at hzero
  have hz := ramanujanGramAction_eq_zero s hs c hzero
  exact fun i => congrFun hz i

/-- The entire old/fresh family is the actual enlarged family under its exact
index splitting. Thus screening the fresh block needs no independence premise. -/
theorem packetFamily_old_fresh_independent (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) :
    LinearIndependent ℝ (Sum.elim (packetFamily s) (packetFamily (t \ s))) := by
  classical
  have he : Sum.elim (packetFamily s) (packetFamily (t \ s)) =
      packetFamily t ∘ (splitEquiv s t hst).symm := by
    funext q
    cases q <;> rfl
  rw [he]
  exact (packetFamily_independent t ht).comp
    (splitEquiv s t hst).symm (splitEquiv s t hst).symm.injective

/-- The literal new innovations, screened against the complete old Gram. -/
def innovationFamily (s t : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    ↥(t \ s) → ThresholdHilbert :=
  screened (packetFamily_independent s hs) (packetFamily (t \ s))

theorem innovationFamily_independent (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) :
    LinearIndependent ℝ (innovationFamily s t hs) := by
  exact screened_linearIndependent (packetFamily_independent s hs)
    (packetFamily (t \ s)) (packetFamily_old_fresh_independent s t hst ht)

/-- The old packet span after the literal physical tail cutoff. Finite
dimensionality supplies its actual orthogonal projection unconditionally. -/
abbrev tailOldSpace (s : Finset ℕ) (N : ℕ) : Submodule ℝ ThresholdHilbert :=
  synthesisSpan (fun q : s => packetFamily s q - compactHead N (packetFamily s q))

/-- Complete omitted target error after projecting the tail target onto the
tail-old span. This is the paper's (I-P_t)1_tail. -/
def tailTargetError (s : Finset ℕ) (N : ℕ) : ThresholdHilbert :=
  (hilbertOne - compactHead N hilbertOne) -
    (tailOldSpace s N).starProjection (hilbertOne - compactHead N hilbertOne)

/-- The actual target is one on the head and the tail-old fit on the tail. -/
def compensatedTarget (s : Finset ℕ) (N : ℕ) : ThresholdHilbert :=
  hilbertOne - tailTargetError s N

theorem compensatedTarget_eq_head_add_tail_fit (s : Finset ℕ) (N : ℕ) :
    compensatedTarget s N = compactHead N hilbertOne +
      (tailOldSpace s N).starProjection (hilbertOne - compactHead N hilbertOne) := by
  unfold compensatedTarget tailTargetError
  abel

theorem compensatedTarget_error_exact (s : Finset ℕ) (N : ℕ) :
    hilbertOne - compensatedTarget s N = tailTargetError s N := by
  unfold compensatedTarget
  abel

/-- Full tail target Pythagoras; the old tail-fit square is retained exactly. -/
theorem tailTargetError_pythagoras (s : Finset ℕ) (N : ℕ) :
    ‖hilbertOne - compactHead N hilbertOne‖ ^ 2 =
      ‖(tailOldSpace s N).starProjection
        (hilbertOne - compactHead N hilbertOne)‖ ^ 2 +
        ‖tailTargetError s N‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (hilbertOne - compactHead N hilbertOne) (tailOldSpace s N)
  rw [Submodule.starProjection_orthogonal_val] at h
  exact h

/-- The entire physical target error obeys the exact cutoff allowance,
without an inverse-operator estimate or a supplied tail approximation. -/
theorem tailTargetError_norm_sq_le_headAllowance (s : Finset ℕ) (N : ℕ) :
    ‖tailTargetError s N‖ ^ 2 ≤ 1 / ((N : ℝ) + 1) := by
  have hp := tailTargetError_pythagoras s N
  have ht : ‖hilbertOne - compactHead N hilbertOne‖ ^ 2 ≤
      1 / ((N : ℝ) + 1) := by
    have h := compactHead_complete_tail_norm_sq_le_of_sequence_bound N hilbertOne 1
      (by intro j; by_cases hj : j = 0 <;> simp [hilbertOne_sequence, zeroAnchor, hj])
    simpa only [one_pow] using h
  nlinarith only [hp, ht,
    sq_nonneg ‖(tailOldSpace s N).starProjection
      (hilbertOne - compactHead N hilbertOne)‖]

/-- Complete actual matrix source. Every signed old/fresh Gram entry remains. -/
def actualSource (s t : Finset ℕ) (hst : s ⊆ t) : ↥(t \ s) → ℝ :=
  ramanujanVonMangoldtVector (t \ s) -
    projectionAdjunctionCross s t hst *ᵥ projectionCoefficients s

/-- Source evaluated after subtracting the entire omitted target error.
The later target-observation and head-plus-tail-fit identities identify its
complete physical compensation. An explicit tail-Gram inverse coordinate
expansion is not needed for the certificate divergence equivalence. -/
def compensatedSource (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (N : ℕ) : ↥(t \ s) → ℝ :=
  actualSource s t hst - cross (innovationFamily s t hs) (tailTargetError s N)

/-- The complete inverse innovation Gram sees only the observed target error.
The unobserved error square is subtracted exactly rather than omitted. -/
theorem observedTailError_exact (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) (N : ℕ) :
    capacity (innovationFamily_independent s t hst hs ht)
      (cross (innovationFamily s t hs) (tailTargetError s N)) =
      ‖tailTargetError s N‖ ^ 2 -
        ‖tailTargetError s N - minimumVector
          (innovationFamily_independent s t hst hs ht)
          (cross (innovationFamily s t hs) (tailTargetError s N))‖ ^ 2 := by
  exact capacity_observed_exact (innovationFamily_independent s t hst hs ht)
    (tailTargetError s N)

/-- This literal observed error satisfies the horizon allowance internally. -/
theorem observedTailError_le_headAllowance (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) (N : ℕ) :
    capacity (innovationFamily_independent s t hst hs ht)
      (cross (innovationFamily s t hs) (tailTargetError s N)) ≤
        1 / ((N : ℝ) + 1) := by
  exact (capacity_observed_le_norm_sq
    (innovationFamily_independent s t hst hs ht) (tailTargetError s N)).trans
      (tailTargetError_norm_sq_le_headAllowance s N)

/-- Complete actual/translated source capacities satisfy the observed-radius
comparison with no supplied source-error inequality. -/
theorem actual_compensatedSource_sqrt_radius (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) (N : ℕ) :
    |Real.sqrt (capacity (innovationFamily_independent s t hst hs ht)
        (actualSource s t hst)) -
      Real.sqrt (capacity (innovationFamily_independent s t hst hs ht)
        (compensatedSource s t hst hs N))| ≤
      Real.sqrt (capacity (innovationFamily_independent s t hst hs ht)
        (cross (innovationFamily s t hs) (tailTargetError s N))) := by
  exact capacity_sub_observed_sqrt_budget_observed
    (innovationFamily_independent s t hst hs ht)
    (actualSource s t hst) (tailTargetError s N)

end RiemannResearch.RH.Pareto.PhysicalCompensatedSource

/-!
# Actual physical innovation capacity equals the whole-block projection gain

The focused dependency FiniteGramBasisInvariance supplies the exact
observation-change theorem is used for old/fresh reindexing.

Source: `crt_complete_tail_certificate.txt`, complete physical old/new Schur
gain, equations (1.2) and (4.3). The gain is derived from the actual
finite Hilbert Gram, actual physical normal equation, exact index splitting,
and capacity_screened_add. No Gram inverse, source radius, gain nonnegativity,
gain divergence or RH conclusion is supplied as an input.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PhysicalCompensatedSource

open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection
open PhysicalScreenedSource PhysicalSchurReindex
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

/-- The literal Hilbert observations of one are the actual von Mangoldt source. -/
theorem packetFamily_source (s : Finset ℕ) :
    cross (packetFamily s) hilbertOne = ramanujanVonMangoldtVector s := by
  funext q
  change inner ℝ (ramanujanPacketHilbert q.val) hilbertOne =
    ramanujanVonMangoldtVector s q
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert]
  exact (ramanujanVonMangoldtVector_eq_mean s q).symm

/-- Uniqueness in the complete Gram identifies the Hilbert inverse source
with the already proved actual physical projection coefficients. -/
theorem packetFamily_inverseSource (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    inverseSource (packetFamily_independent s hs)
      (ramanujanVonMangoldtVector s) = projectionCoefficients s := by
  apply ramanujanGramAction_injective s hs
  have hi := funext (inverseSource_normal (packetFamily_independent s hs)
    (ramanujanVonMangoldtVector s))
  rw [packetFamily_gram] at hi
  have hp := projection_normalEquation s hs ho
  rw [ramanujanGramMatrix_mulVec] at hp
  exact hi.trans hp.symm

/-- The arbitrary finite actual packet capacity is precisely the physical
projection charge; all full-tail and signed mixed entries are retained. -/
theorem packetFamily_capacity_eq_charge (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    capacity (packetFamily_independent s hs) (ramanujanVonMangoldtVector s) =
      sourceProjectionCharge s := by
  unfold capacity
  rw [packetFamily_inverseSource s hs ho]
  change projectionCoefficients s ⬝ᵥ ramanujanVonMangoldtVector s = _
  rw [dotProduct_comm]
  exact projection_pairing s

/-- The actual old/fresh family and the enlarged packet family impose
identical observations, with their source split reindexed at the same time. -/
theorem packetFamily_old_fresh_capacity_eq_charge (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hot : ∃ p ∈ t, p.Prime ∧ 2 < p) :
    capacity (packetFamily_old_fresh_independent s t hst ht)
      (Sum.elim (ramanujanVonMangoldtVector s)
        (ramanujanVonMangoldtVector (t \ s))) = sourceProjectionCharge t := by
  classical
  let e := splitEquiv s t hst
  have he : Sum.elim (packetFamily s) (packetFamily (t \ s)) =
      packetFamily t ∘ e.symm := by
    funext q
    cases q <;> rfl
  have hSourceReindex : Sum.elim (ramanujanVonMangoldtVector s)
      (ramanujanVonMangoldtVector (t \ s)) = ramanujanVonMangoldtVector t ∘ e.symm := by
    funext q
    cases q <;> rfl
  have hcap : capacity (packetFamily_old_fresh_independent s t hst ht)
      (Sum.elim (ramanujanVonMangoldtVector s)
        (ramanujanVonMangoldtVector (t \ s))) =
      capacity (packetFamily_independent t ht) (ramanujanVonMangoldtVector t) := by
    apply capacity_eq_of_same_observations
    intro z
    constructor
    · intro hz q
      simpa only [he, hSourceReindex, Function.comp_apply, Equiv.symm_apply_apply] using hz (e q)
    · intro hz q
      simpa only [he, hSourceReindex, Function.comp_apply] using hz (e.symm q)
  exact hcap.trans (packetFamily_capacity_eq_charge t ht hot)

/-- The Hilbert screened source is exactly the physical full Gram cross
source, using the genuine old projection coefficients rather than a provider
hypothesis for an inverse or source identification. -/
theorem actualSource_eq_hilbert_screenedSource (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    actualSource s t hst =
      screenedSource (packetFamily_independent s hs) (packetFamily (t \ s))
        (ramanujanVonMangoldtVector s) (ramanujanVonMangoldtVector (t \ s)) := by
  have hcross (i : s) (j : ↥(t \ s)) :
      cross (packetFamily s) (packetFamily (t \ s) j) i =
        projectionAdjunctionCross s t hst j i := by
    unfold cross packetFamily
    rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert,
      hilbertSequence_ramanujanPacketHilbert]
    change paretoInner (ramanujanPacket i.val) (ramanujanPacket j.val) =
      paretoInner (ramanujanPacket j.val) (ramanujanPacket i.val)
    exact paretoInner_comm _ _
  funext j
  rw [screenedSource_eq, packetFamily_inverseSource s hs ho]
  change ramanujanVonMangoldtVector (t \ s) j -
      (∑ i : s, projectionAdjunctionCross s t hst j i * projectionCoefficients s i) =
    ramanujanVonMangoldtVector (t \ s) j -
      ∑ i : s, projectionCoefficients s i * cross (packetFamily s) (packetFamily (t \ s) j) i
  simp_rw [hcross]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete inverse innovation Gram capacity is the literal actual
whole-block error decrease. All independence, normal equations, source
identification and old/fresh reindexing are discharged above. -/
theorem actualSource_capacity_eq_projection_gain (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    capacity (innovationFamily_independent s t hst hs ht) (actualSource s t hst) =
      paretoError (synthesis s (projectionCoefficients s)) -
        paretoError (synthesis t (projectionCoefficients t)) := by
  have hot : ∃ p ∈ t, p.Prime ∧ 2 < p := by
    obtain ⟨p, hps, hp, hp2⟩ := ho
    exact ⟨p, hst hps, hp, hp2⟩
  have h := capacity_screened_add (packetFamily_independent s hs)
    (packetFamily (t \ s)) (innovationFamily_independent s t hst hs ht)
    (packetFamily_old_fresh_independent s t hst ht)
    (ramanujanVonMangoldtVector s) (ramanujanVonMangoldtVector (t \ s))
  rw [packetFamily_old_fresh_capacity_eq_charge s t hst ht hot,
    packetFamily_capacity_eq_charge s hs ho,
    ← actualSource_eq_hilbert_screenedSource s t hst hs ho] at h
  change sourceProjectionCharge t = sourceProjectionCharge s +
    capacity (innovationFamily_independent s t hst hs ht) (actualSource s t hst) at h
  rw [projection_error s hs ho, projection_error t ht hot]
  linarith only [h]

end RiemannResearch.RH.Pareto.PhysicalCompensatedSource

/-!
# Literal physical observed certificates at explicit nested-chain horizons

Source: `crt_complete_tail_certificate.txt`, Sections 4 and 6. The signed source
is identified with observations of the literal compensated target, retaining
the complete old-tail fit. The observed error, source capacity and certificate
are constructed from actual packet innovations and the same complete measure.

The final equivalence has no free A or tau, no supplied source-radius premise,
no supplied gain nonnegativity and no supplied summability provider. The actual
finite error floor and explicit horizon discharge normalization. It does not
assert either cumulative divergence statement or RH.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalCompensatedSource

open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.CompensatedSourceCertificate

/-- The literal full matrix source is the actual innovation's observation of
one. The old inverse is the constructed Hilbert Gram inverse; no source
identity is inserted as a hypothesis. -/
theorem actualSource_eq_innovation_observations (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    actualSource s t hst = cross (innovationFamily s t hs) hilbertOne := by
  let hu := packetFamily_independent s hs
  have hc : inverseCoeff hu hilbertOne =
      inverseSource hu (ramanujanVonMangoldtVector s) := by
    unfold inverseCoeff inverseSource
    rw [packetFamily_source]
  rw [actualSource_eq_hilbert_screenedSource s t hst hs ho]
  funext j
  let w := packetFamily (t \ s) j
  let pOne := Fintype.linearCombination ℝ (packetFamily s) (inverseCoeff hu hilbertOne)
  let pW := Fintype.linearCombination ℝ (packetFamily s) (inverseCoeff hu w)
  have hOne := residual_orthogonal hu hilbertOne (inverseCoeff hu w)
  have hW := residual_orthogonal hu w (inverseCoeff hu hilbertOne)
  rw [inner_sub_left] at hOne hW
  have hpair : inner ℝ pW hilbertOne = inner ℝ w pOne := by
    calc
      _ = inner ℝ hilbertOne pW := real_inner_comm _ _
      _ = inner ℝ pOne pW := sub_eq_zero.mp hOne
      _ = inner ℝ pW pOne := real_inner_comm _ _
      _ = _ := (sub_eq_zero.mp hW).symm
  have hmin : minimumVector hu (ramanujanVonMangoldtVector s) = pOne := by
    change Fintype.linearCombination ℝ (packetFamily s)
      (inverseSource hu (ramanujanVonMangoldtVector s)) = _
    rw [← hc]
  have hnew : ramanujanVonMangoldtVector (t \ s) j = inner ℝ w hilbertOne :=
    congrFun (packetFamily_source (t \ s)).symm j
  change ramanujanVonMangoldtVector (t \ s) j -
      inner ℝ w (minimumVector hu (ramanujanVonMangoldtVector s)) =
    inner ℝ (w - pW) hilbertOne
  rw [hnew, hmin, inner_sub_left, hpair]

/-- The translated source is exactly the innovation's observation of the
concrete compensated target, not an arbitrary finite source certificate. -/
theorem compensatedSource_eq_target_observations (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (N : ℕ) :
    compensatedSource s t hst hs N =
      cross (innovationFamily s t hs) (compensatedTarget s N) := by
  rw [compensatedSource, actualSource_eq_innovation_observations s t hst hs ho]
  funext j
  change inner ℝ (innovationFamily s t hs j) hilbertOne -
      inner ℝ (innovationFamily s t hs j) (tailTargetError s N) =
    inner ℝ (innovationFamily s t hs j) (hilbertOne - tailTargetError s N)
  rw [inner_sub_right]

/-- Coefficient-free finite-head source plus the entire old-tail fit source.
The signed compensation is part of the equality and remains before taking a
capacity or absolute value. -/
theorem compensatedSource_eq_head_add_tail_fit_observations
    (s t : Finset ℕ) (hst : s ⊆ t) (hs : ∀ q ∈ s, 1 < q)
    (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (N : ℕ) :
    compensatedSource s t hst hs N =
      cross (innovationFamily s t hs) (compactHead N hilbertOne) +
        cross (innovationFamily s t hs)
          ((tailOldSpace s N).starProjection (hilbertOne - compactHead N hilbertOne)) := by
  rw [compensatedSource_eq_target_observations s t hst hs ho N,
    compensatedTarget_eq_head_add_tail_fit]
  funext j
  exact inner_add_right _ _ _

/-- The actual complete innovation Gram source capacity at a physical horizon. -/
def compensatedCapacity (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) (N : ℕ) : ℝ :=
  capacity (innovationFamily_independent s t hst hs ht) (compensatedSource s t hst hs N)

/-- The exact observed tail error, using the same complete innovation Gram. -/
def observedTailError (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) (N : ℕ) : ℝ :=
  capacity (innovationFamily_independent s t hst hs ht)
    (cross (innovationFamily s t hs) (tailTargetError s N))

/-- A literal physical compensated certificate; neither capacity nor radius
is left as an application input. -/
def observedCertificate (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) (N : ℕ) : ℝ :=
  gainCertificate (compensatedCapacity s t hst hs ht N)
    (observedTailError s t hst hs ht N)

/-- On any nested legal packet chain, the explicit horizons give equivalent
cumulative divergence of actual normalized projection gains and the literal
physical observed certificates. Every geometric source/radius and normalized
error provider is supplied internally; divergence itself remains unproved. -/
theorem observedCertificate_divergence_iff_explicit_horizon
    (s : ℕ → Finset ℕ) (L F : ℕ → ℕ)
    (hnested : ∀ n, s n ⊆ s (n + 1))
    (hs : ∀ n, ∀ q ∈ s n, 1 < q)
    (ho : ∀ n, ∃ p ∈ s n, p.Prime ∧ 2 < p)
    (hL : ∀ n, 0 < L n) (hperiod : ∀ n, ∀ q ∈ s n, q ∣ L n) :
    let N : ℕ → ℕ := fun n => normalizedTailHorizonWithFloor (L n) (F n) n
    let E : ℕ → ℝ := fun n =>
      paretoError (synthesis (s n) (projectionCoefficients (s n)))
    Tendsto (fun J => ∑ n ∈ Finset.range J, (E n - E (n + 1)) / (E n) ^ 2)
      atTop atTop ↔
    Tendsto (fun J => ∑ n ∈ Finset.range J,
      observedCertificate (s n) (s (n + 1)) (hnested n)
        (hs n) (hs (n + 1)) (N n) / (E n) ^ 2) atTop atTop := by
  dsimp only
  let N : ℕ → ℕ := fun n => normalizedTailHorizonWithFloor (L n) (F n) n
  let E : ℕ → ℝ := fun n =>
    paretoError (synthesis (s n) (projectionCoefficients (s n)))
  let A : ℕ → ℝ := fun n => compensatedCapacity (s n) (s (n + 1))
    (hnested n) (hs n) (hs (n + 1)) (N n)
  let τ : ℕ → ℝ := fun n => observedTailError (s n) (s (n + 1))
    (hnested n) (hs n) (hs (n + 1)) (N n)
  have hτ0 (n : ℕ) : 0 ≤ τ n := capacity_nonneg
    (innovationFamily_independent (s n) (s (n + 1)) (hnested n)
      (hs n) (hs (n + 1))) _
  have hτ (n : ℕ) : τ n ≤ 1 / ((N n : ℝ) + 1) :=
    observedTailError_le_headAllowance (s n) (s (n + 1)) (hnested n)
      (hs n) (hs (n + 1)) (N n)
  have hgain (n : ℕ) : 0 ≤ E n - E (n + 1) := by
    rw [← actualSource_capacity_eq_projection_gain (s n) (s (n + 1))
      (hnested n) (hs n) (hs (n + 1)) (ho n)]
    exact capacity_nonneg _ _
  have hsource (n : ℕ) :
      |Real.sqrt (E n - E (n + 1)) - Real.sqrt (A n)| ≤ Real.sqrt (τ n) := by
    rw [← actualSource_capacity_eq_projection_gain (s n) (s (n + 1))
      (hnested n) (hs n) (hs (n + 1)) (ho n)]
    exact actual_compensatedSource_sqrt_radius (s n) (s (n + 1))
      (hnested n) (hs n) (hs (n + 1)) (N n)
  have h := projection_normalizedCertificate_divergence_iff_explicit_horizon
    s L F A τ hs ho hL hperiod hτ0 hτ hgain hsource
  simpa only [N, E, A, τ, observedCertificate] using h

end RiemannResearch.RH.Pareto.PhysicalCompensatedSource
