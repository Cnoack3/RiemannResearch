import RiemannResearch.Analysis.HilbertAnnihilatorCertificate
import RiemannResearch.RH.RamanujanHilbertTransfer
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.MobiusCoefficientStabilization
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Lean.Elab.Tactic.Omega

/-!
# Complete Ramanujan annihilators, sharp certificates, and dual adjoints

Source: user-requested duality program, 23 October 2026.
Arbitrary packet sets and Hilbert targets have exact closure/annihilator
criteria and sharp normalized certificates. Inverse adjoints transport dual
vectors between P and Q and preserve target pairings.
Full-conductor rigidity is equivalent to natural approximation; its reverse
RH implication retains the explicit Baez-Duarte analytic provider.
-/

noncomputable section

namespace RiemannResearch.RH.RamanujanTransfer

open ZetaTwoHilbert QRamanujanPackets Pareto
open RiemannResearch.Analysis.HilbertAnnihilatorCertificate

abbrev qPacketClosedSpan (S : Set ℕ) : Submodule ℝ QHilbert :=
  closedSpan (qRamanujanPacket '' S)

abbrev pPacketClosedSpan (S : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  closedSpan (ramanujanPacketHilbert '' S)

theorem q_annihilator_iff (S : Set ℕ) (h : QHilbert) :
    h ∈ (qPacketClosedSpan S)ᗮ ↔
      ∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0 := by
  rw [closedSpan_annihilator_iff]
  constructor
  · intro hh q hq
    exact hh _ ⟨q, hq, rfl⟩
  · intro hh
    rintro _ ⟨q, hq, rfl⟩
    exact hh q hq

theorem p_annihilator_iff (S : Set ℕ) (h : ThresholdHilbert) :
    h ∈ (pPacketClosedSpan S)ᗮ ↔
      ∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0 := by
  rw [closedSpan_annihilator_iff]
  constructor
  · intro hh q hq
    exact hh _ ⟨q, hq, rfl⟩
  · intro hh
    rintro _ ⟨q, hq, rfl⟩
    exact hh q hq

theorem q_closure_iff_annihilator (S : Set ℕ) (x : QHilbert) :
    x ∈ qPacketClosedSpan S ↔
      ∀ h : QHilbert,
        (∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0) → inner ℝ h x = 0 := by
  rw [closure_iff_annihilator]
  constructor
  · intro hx h hh
    apply hx h
    rintro _ ⟨q, hq, rfl⟩
    exact hh q hq
  · intro hx h hh
    exact hx h (fun q hq => hh _ ⟨q, hq, rfl⟩)

theorem p_closure_iff_annihilator (S : Set ℕ) (x : ThresholdHilbert) :
    x ∈ pPacketClosedSpan S ↔
      ∀ h : ThresholdHilbert,
        (∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0) → inner ℝ h x = 0 := by
  rw [closure_iff_annihilator]
  constructor
  · intro hx h hh
    apply hx h
    rintro _ ⟨q, hq, rfl⟩
    exact hh q hq
  · intro hx h hh
    exact hx h (fun q hq => hh _ ⟨q, hq, rfl⟩)

theorem q_normalized_separator_of_not_closure (S : Set ℕ) (x : QHilbert)
    (hx : x ∉ qPacketClosedSpan S) :
    ∃ h : QHilbert,
      (∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0) ∧ inner ℝ h x = 1 ∧
      ‖h‖ ^ 2 * ‖x - (qPacketClosedSpan S).starProjection x‖ ^ 2 = 1 := by
  obtain ⟨h, ha, hm, hs⟩ :=
    normalized_separator_of_not_closure (qRamanujanPacket '' S) x hx
  exact ⟨h, (fun q hq => ha _ ⟨q, hq, rfl⟩), hm, hs⟩

theorem p_normalized_separator_of_not_closure (S : Set ℕ) (x : ThresholdHilbert)
    (hx : x ∉ pPacketClosedSpan S) :
    ∃ h : ThresholdHilbert,
      (∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0) ∧ inner ℝ h x = 1 ∧
      ‖h‖ ^ 2 * ‖x - (pPacketClosedSpan S).starProjection x‖ ^ 2 = 1 := by
  obtain ⟨h, ha, hm, hs⟩ :=
    normalized_separator_of_not_closure (ramanujanPacketHilbert '' S) x hx
  exact ⟨h, (fun q hq => ha _ ⟨q, hq, rfl⟩), hm, hs⟩

theorem q_cauchy_certificate_bound (S : Set ℕ) (x h v : QHilbert)
    (ha : ∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0)
    (hv : v ∈ qPacketClosedSpan S) :
    (inner ℝ h x) ^ 2 ≤ ‖h‖ ^ 2 * ‖x - v‖ ^ 2 := by
  apply cauchy_certificate_bound (qRamanujanPacket '' S) x h v _ hv
  rintro _ ⟨q, hq, rfl⟩
  exact ha q hq

theorem p_cauchy_certificate_bound (S : Set ℕ) (x h v : ThresholdHilbert)
    (ha : ∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0)
    (hv : v ∈ pPacketClosedSpan S) :
    (inner ℝ h x) ^ 2 ≤ ‖h‖ ^ 2 * ‖x - v‖ ^ 2 := by
  apply cauchy_certificate_bound (ramanujanPacketHilbert '' S) x h v _ hv
  rintro _ ⟨q, hq, rfl⟩
  exact ha q hq

theorem q_normalized_separator_error_lower (S : Set ℕ) (x h v : QHilbert)
    (ha : ∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0)
    (hm : inner ℝ h x = 1) (hv : v ∈ qPacketClosedSpan S) :
    1 ≤ ‖h‖ ^ 2 * ‖x - v‖ ^ 2 := by
  have hc := q_cauchy_certificate_bound S x h v ha hv
  simpa only [hm, one_pow] using hc

theorem p_normalized_separator_error_lower (S : Set ℕ) (x h v : ThresholdHilbert)
    (ha : ∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0)
    (hm : inner ℝ h x = 1) (hv : v ∈ pPacketClosedSpan S) :
    1 ≤ ‖h‖ ^ 2 * ‖x - v‖ ^ 2 := by
  have hc := p_cauchy_certificate_bound S x h v ha hv
  simpa only [hm, one_pow] using hc

theorem q_residual_inner_target (S : Set ℕ) (x : QHilbert) :
    inner ℝ (x - (qPacketClosedSpan S).starProjection x) x =
      ‖x - (qPacketClosedSpan S).starProjection x‖ ^ 2 :=
  residual_inner_target (qRamanujanPacket '' S) x

theorem p_residual_inner_target (S : Set ℕ) (x : ThresholdHilbert) :
    inner ℝ (x - (pPacketClosedSpan S).starProjection x) x =
      ‖x - (pPacketClosedSpan S).starProjection x‖ ^ 2 :=
  residual_inner_target (ramanujanPacketHilbert '' S) x

theorem q_residual_attains_certificate (S : Set ℕ) (x : QHilbert) :
    (inner ℝ (x - (qPacketClosedSpan S).starProjection x) x) ^ 2 =
      ‖x - (qPacketClosedSpan S).starProjection x‖ ^ 2 *
        ‖x - (qPacketClosedSpan S).starProjection x‖ ^ 2 :=
  residual_attains_bound (qRamanujanPacket '' S) x

theorem p_residual_attains_certificate (S : Set ℕ) (x : ThresholdHilbert) :
    (inner ℝ (x - (pPacketClosedSpan S).starProjection x) x) ^ 2 =
      ‖x - (pPacketClosedSpan S).starProjection x‖ ^ 2 *
        ‖x - (pPacketClosedSpan S).starProjection x‖ ^ 2 :=
  residual_attains_bound (ramanujanPacketHilbert '' S) x

open ZetaTwoParetoTransfer QParetoEquivalence RamanujanPrimeCoordinates

/-- The two complete annihilator criteria transfer for the same physical target.
The annihilator vectors themselves are allowed to vary with the metric. -/
theorem q_p_annihilator_conditions_iff (S : Set ℕ) (f : QHilbert) :
    (∀ h : QHilbert,
      (∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0) → inner ℝ h f = 0) ↔
    (∀ h : ThresholdHilbert,
      (∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0) →
        inner ℝ h (toPareto f) = 0) :=
  (q_closure_iff_annihilator S f).symm.trans
    ((packet_closure_transfer S f).trans
      (p_closure_iff_annihilator S (toPareto f)))

/-- The adjoint, rather than the sequence-preserving map, transports dual vectors. -/
def qDualFromPareto (h : ThresholdHilbert) : QHilbert :=
  toParetoCLM.adjoint h

def pDualFromQ (h : QHilbert) : ThresholdHilbert :=
  toQCLM.adjoint h

theorem qDualFromPareto_pairing (h : ThresholdHilbert) (f : QHilbert) :
    inner ℝ (qDualFromPareto h) f = inner ℝ h (toPareto f) := by
  change inner ℝ (toParetoCLM.adjoint h) f = _
  calc
    _ = inner ℝ f (toParetoCLM.adjoint h) := real_inner_comm _ _
    _ = inner ℝ (toParetoCLM f) h := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℝ h (toPareto f) := real_inner_comm _ _

theorem pDualFromQ_pairing (h : QHilbert) (f : ThresholdHilbert) :
    inner ℝ (pDualFromQ h) f = inner ℝ h (toQ f) := by
  change inner ℝ (toQCLM.adjoint h) f = _
  calc
    _ = inner ℝ f (toQCLM.adjoint h) := real_inner_comm _ _
    _ = inner ℝ (toQCLM f) h := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℝ h (toQ f) := real_inner_comm _ _

@[simp] theorem pDualFromQ_qDualFromPareto (h : ThresholdHilbert) :
    pDualFromQ (qDualFromPareto h) = h := by
  apply ext_inner_left ℝ
  intro f
  change inner ℝ f (toQCLM.adjoint (toParetoCLM.adjoint h)) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (toPareto (toQ f)) h = _
  rw [toPareto_toQ]

@[simp] theorem qDualFromPareto_pDualFromQ (h : QHilbert) :
    qDualFromPareto (pDualFromQ h) = h := by
  apply ext_inner_left ℝ
  intro f
  change inner ℝ f (toParetoCLM.adjoint (toQCLM.adjoint h)) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (toQ (toPareto f)) h = _
  rw [toQ_toPareto]

/-- Exact bijective transfer of each Pareto annihilator to its Q dual vector. -/
theorem qDualFromPareto_annihilator_iff (S : Set ℕ) (h : ThresholdHilbert) :
    qDualFromPareto h ∈ (qPacketClosedSpan S)ᗮ ↔
      h ∈ (pPacketClosedSpan S)ᗮ := by
  rw [q_annihilator_iff, p_annihilator_iff]
  simp only [qDualFromPareto_pairing, toPareto_packet]

theorem pDualFromQ_annihilator_iff (S : Set ℕ) (h : QHilbert) :
    pDualFromQ h ∈ (pPacketClosedSpan S)ᗮ ↔
      h ∈ (qPacketClosedSpan S)ᗮ := by
  have hh := qDualFromPareto_annihilator_iff S (pDualFromQ h)
  rw [qDualFromPareto_pDualFromQ] at hh
  exact hh.symm

end RiemannResearch.RH.RamanujanTransfer

namespace RiemannResearch.RH.RamanujanTransfer

open Pareto ZetaTwoHilbert QRamanujanPackets
open ZetaTwoParetoTransfer QParetoEquivalence

/-- Full legal packets have exactly the original full residue closure. -/
theorem p_fullPacketClosedSpan_eq_closedSpace :
    pPacketClosedSpan {q : ℕ | 1 < q} = CoefficientStabilization.closedSpace := by
  have hspan := p_span_eq {q : ℕ | 1 < q}
    (by intro d hd; exact Nat.zero_lt_of_lt hd)
    (by intro d hd q hqd hq; exact hq)
  have hset : BaezDuarte.residueVector '' {q : ℕ | 1 < q} =
      Set.range CoefficientStabilization.residueAtom := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      change 1 < d at hd
      refine ⟨d - 2, ?_⟩
      have hd0 : 0 < d := by omega
      have he : d - 2 + 2 = d := by omega
      simp only [CoefficientStabilization.residueAtom, he,
        BaezDuarte.residueVector, dif_pos hd0]
    · rintro ⟨i, rfl⟩
      refine ⟨i + 2, by change 1 < i + 2; omega, ?_⟩
      simp only [BaezDuarte.residueVector,
        dif_pos (show 0 < i + 2 by omega), CoefficientStabilization.residueAtom]
  change (Submodule.span ℝ
    (ramanujanPacketHilbert '' {q : ℕ | 1 < q})).topologicalClosure =
      (Submodule.span ℝ (Set.range CoefficientStabilization.residueAtom)).topologicalClosure
  rw [hspan, hset]

/-- Density and annihilator rigidity transfer between the two metrics.
Individual annihilators are transported by the inverse adjoint maps. -/
theorem q_p_annihilator_rigidity_iff (S : Set ℕ) :
    (∀ h : QHilbert,
      (∀ q ∈ S, inner ℝ h (qRamanujanPacket q) = 0) → h = 0) ↔
    (∀ h : ThresholdHilbert,
      (∀ q ∈ S, inner ℝ h (ramanujanPacketHilbert q) = 0) → h = 0) := by
  constructor
  · intro hrig h ha
    have ho : qDualFromPareto h ∈ (qPacketClosedSpan S)ᗮ :=
      (qDualFromPareto_annihilator_iff S h).mpr ((p_annihilator_iff S h).mpr ha)
    have hz : qDualFromPareto h = 0 :=
      hrig _ ((q_annihilator_iff S _).mp ho)
    have hh := congrArg pDualFromQ hz
    rw [pDualFromQ_qDualFromPareto] at hh
    change h = toQCLM.adjoint 0 at hh
    simpa only [map_zero] using hh
  · intro hrig h ha
    have ho : pDualFromQ h ∈ (pPacketClosedSpan S)ᗮ :=
      (pDualFromQ_annihilator_iff S h).mpr ((q_annihilator_iff S h).mpr ha)
    have hz : pDualFromQ h = 0 :=
      hrig _ ((p_annihilator_iff S _).mp ho)
    have hh := congrArg qDualFromPareto hz
    rw [qDualFromPareto_pDualFromQ] at hh
    change h = toParetoCLM.adjoint 0 at hh
    simpa only [map_zero] using hh

/-- This equivalence is unconditional: the approximation property is not asserted. -/
theorem p_full_annihilator_rigidity_iff_naturalApproximation :
    (∀ h : ThresholdHilbert,
      (∀ q : ℕ, 1 < q → inner ℝ h (ramanujanPacketHilbert q) = 0) → h = 0) ↔
      BaezDuarte.NaturalApproximation := by
  constructor
  · intro hrig
    apply BaezDuarte.naturalApproximation_iff_one_mem.mpr
    have hm : hilbertOne ∈ pPacketClosedSpan {q : ℕ | 1 < q} := by
      apply (p_closure_iff_annihilator _ _).mpr
      intro h ha
      rw [hrig h ha]
      simp
    simpa only [p_fullPacketClosedSpan_eq_closedSpace] using hm
  · intro hn h ha
    have ht : CoefficientStabilization.closedSpace = ⊤ :=
      CoefficientStabilization.closedSpace_eq_top_iff_one_mem.mpr
        (BaezDuarte.naturalApproximation_iff_one_mem.mp hn)
    have ho : h ∈ (pPacketClosedSpan {q : ℕ | 1 < q})ᗮ :=
      (p_annihilator_iff _ _).mpr ha
    have hm : h ∈ pPacketClosedSpan {q : ℕ | 1 < q} := by
      rw [p_fullPacketClosedSpan_eq_closedSpace, ht]
      trivial
    exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal' _ h).mp ho h hm)

theorem q_full_annihilator_rigidity_iff_naturalApproximation :
    (∀ h : QHilbert,
      (∀ q : ℕ, 1 < q → inner ℝ h (qRamanujanPacket q) = 0) → h = 0) ↔
      BaezDuarte.NaturalApproximation :=
  (q_p_annihilator_rigidity_iff {q : ℕ | 1 < q}).trans
    p_full_annihilator_rigidity_iff_naturalApproximation

theorem riemannHypothesis_of_p_full_annihilator_rigidity
    (hrig : ∀ h : ThresholdHilbert,
      (∀ q : ℕ, 1 < q → inner ℝ h (ramanujanPacketHilbert q) = 0) → h = 0) :
    RiemannHypothesis :=
  CoefficientStabilization.riemannHypothesis_of_limitCoefficients
    (CoefficientStabilization.limitCoefficients_eq_mobius_iff_mem.mpr
      (BaezDuarte.naturalApproximation_iff_one_mem.mp
        (p_full_annihilator_rigidity_iff_naturalApproximation.mp hrig)))

theorem riemannHypothesis_of_q_full_annihilator_rigidity
    (hrig : ∀ h : QHilbert,
      (∀ q : ℕ, 1 < q → inner ℝ h (qRamanujanPacket q) = 0) → h = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_p_full_annihilator_rigidity
    ((q_p_annihilator_rigidity_iff {q : ℕ | 1 < q}).mp hrig)

/-- The external analytic converse remains explicit; no provider is invented. -/
theorem p_full_annihilator_rigidity_iff_riemannHypothesis_of_baez_duarte
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    (∀ h : ThresholdHilbert,
      (∀ q : ℕ, 1 < q → inner ℝ h (ramanujanPacketHilbert q) = 0) → h = 0) ↔
      RiemannHypothesis := by
  apply p_full_annihilator_rigidity_iff_naturalApproximation.trans
  constructor
  · intro hn
    exact CoefficientStabilization.riemannHypothesis_of_limitCoefficients
      (CoefficientStabilization.limitCoefficients_eq_mobius_iff_mem.mpr
        (BaezDuarte.naturalApproximation_iff_one_mem.mp hn))
  · exact hBaezDuarte

theorem q_full_annihilator_rigidity_iff_riemannHypothesis_of_baez_duarte
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    (∀ h : QHilbert,
      (∀ q : ℕ, 1 < q → inner ℝ h (qRamanujanPacket q) = 0) → h = 0) ↔
      RiemannHypothesis :=
  (q_p_annihilator_rigidity_iff {q : ℕ | 1 < q}).trans
    (p_full_annihilator_rigidity_iff_riemannHypothesis_of_baez_duarte hBaezDuarte)

end RiemannResearch.RH.RamanujanTransfer
