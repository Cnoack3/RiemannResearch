import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.ParetoLegalStructure
import RiemannResearch.Analysis.ResidualGainProduct

/-!
# Actual legal Pareto packet walks and RH

Source: user-requested Nyman--Pareto--CRT random-walk investigation, 2026-09-17.
The dictionary consists of all positive integer dilations of the given seeds.
The signed complete Pareto norm is unchanged. The Mellin separation/RH bridge
comes from ThresholdRiemannHypothesis, without a supplied RH implication.
Exhaustion proves existence and order-independence of the limiting residual;
its vanishing, or nonsummability of the actual relative gains, remains open.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ResidualGain

def LegalPacketIndex (A : Set ℕ) := {i : ℕ × ℕ // i.1 ∈ A ∧ 0 < i.2}

def legalPacket (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (i : LegalPacketIndex A) : ThresholdHilbert :=
  hilbertDilation i.val.2 i.property.2
    (digitHilbert i.val.1 1 (hA _ i.property.1) (by norm_num))

theorem legalPacket_sequence (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (i : LegalPacketIndex A) :
    hilbertSequence (legalPacket A hA i) = dilation i.val.2 (residue i.val.1) :=
  hilbertDilation_digit_one_sequence _ _ (hA _ i.property.1) i.property.2

theorem legalPacket_mem (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (i : LegalPacketIndex A) : legalPacket A hA i ∈ hilbertLegalSubspace A := by
  change hilbertSequence (legalPacket A hA i) ∈ legalSeedSpan A
  rw [legalPacket_sequence]
  exact Submodule.subset_span ⟨i.val.1, i.property.1, i.val.2, i.property.2, rfl⟩

theorem span_legalPacket (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    Submodule.span ℝ (Set.range (legalPacket A hA)) = hilbertLegalSubspace A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact legalPacket_mem A hA i
  · have hs : legalSeedSpan A ≤
        (Submodule.span ℝ (Set.range (legalPacket A hA))).map hilbertSequenceLinear := by
      apply Submodule.span_le.mpr
      rintro g ⟨a, ha, m, hm, rfl⟩
      let i : LegalPacketIndex A := ⟨(a, m), ha, hm⟩
      exact ⟨legalPacket A hA i, Submodule.subset_span ⟨i, rfl⟩,
        legalPacket_sequence A hA i⟩
    intro f hf
    obtain ⟨g, hg, he⟩ := hs hf
    have heq : g = f := hilbertSequence_injective he
    exact heq ▸ hg

theorem dictionaryClosure_legalPacket (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    dictionaryClosure (legalPacket A hA) = hilbertLegalClosure A := by
  unfold dictionaryClosure hilbertLegalClosure
  rw [span_legalPacket]

theorem legalWalk_projection_mem (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A) (n : ℕ) (x : ThresholdHilbert) :
    (walkSpan (legalPacket A hA) draw n).starProjection x ∈ hilbertLegalSubspace A := by
  rw [← span_legalPacket A hA]
  exact walkSpan_le _ _ n ((walkSpan _ _ n).starProjection_apply_mem x)

theorem legalWalk_error_pos (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A) (n : ℕ) :
    0 < walkError (legalPacket A hA) draw hilbertOne n := by
  apply pow_pos
  apply norm_pos_iff.mpr
  intro hz
  have he := sub_eq_zero.mp hz
  have hp := legalWalk_projection_mem A hA draw n hilbertOne
  rw [← he] at hp
  obtain ⟨Q, hQ, hzero⟩ := legalSeedSpan_exists_positive_zero A hA hp
  change hilbertSequence hilbertOne Q = 0 at hzero
  rw [hilbertOne_sequence] at hzero
  simp [zeroAnchor, Nat.ne_of_gt hQ] at hzero

theorem legalWalk_error_tendsto_zero_iff (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A) (hexhaust : Function.Surjective draw) :
    Tendsto (walkError (legalPacket A hA) draw hilbertOne) atTop (𝓝 0) ↔
      hilbertOne ∈ hilbertLegalClosure A := by
  rw [walkError_tendsto_zero_iff _ _ hexhaust, dictionaryClosure_legalPacket]

/-- Small complete errors imply actual RH even for a nonexhaustive ordering. -/
theorem riemannHypothesis_of_legalWalk_tendsto (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A)
    (hlim : Tendsto (walkError (legalPacket A hA) draw hilbertOne) atTop (𝓝 0)) :
    RiemannHypothesis := by
  let F := fun n => (walkSpan (legalPacket A hA) draw n).starProjection hilbertOne
  have hn : Tendsto (fun n => ‖F n - hilbertOne‖) atTop (𝓝 0) := by
    simpa [F, walkError, Real.sqrt_sq_eq_abs, norm_sub_rev] using hlim.sqrt
  have ht : Tendsto F atTop (𝓝 hilbertOne) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hn
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
  exact (hilbertLegalSubspace A).isClosed_topologicalClosure.mem_of_tendsto ht
    (Eventually.of_forall (fun n => (hilbertLegalSubspace A).le_topologicalClosure
      (legalWalk_projection_mem A hA draw n hilbertOne)))

def legalWalk_relativeGain (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (draw : ℕ → LegalPacketIndex A) (n : ℕ) : ℝ :=
  (walkError (legalPacket A hA) draw hilbertOne n -
    walkError (legalPacket A hA) draw hilbertOne (n+1)) /
    walkError (legalPacket A hA) draw hilbertOne n

theorem legalWalk_tendsto_zero_iff_not_summable_gain
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (draw : ℕ → LegalPacketIndex A) :
    Tendsto (walkError (legalPacket A hA) draw hilbertOne) atTop (𝓝 0) ↔
      ¬ Summable (legalWalk_relativeGain A hA draw) := by
  have hp := legalWalk_error_pos A hA draw
  have hd := walkError_antitone (legalPacket A hA) draw hilbertOne
  apply residual_tendsto_zero_iff_not_summable (hp 0)
  · intro n
    exact div_nonneg (sub_nonneg.mpr (hd (Nat.le_succ n))) (hp n).le
  · intro n
    unfold legalWalk_relativeGain
    apply (div_lt_iff₀ (hp n)).mpr
    linarith [hp (n+1)]
  · intro n
    unfold legalWalk_relativeGain
    field_simp [ne_of_gt (hp n)]
    ring

theorem riemannHypothesis_of_legalWalk_nonsummable_gain
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (draw : ℕ → LegalPacketIndex A)
    (hgain : ¬ Summable (legalWalk_relativeGain A hA draw)) : RiemannHypothesis :=
  riemannHypothesis_of_legalWalk_tendsto A hA draw
    ((legalWalk_tendsto_zero_iff_not_summable_gain A hA draw).mpr hgain)

/-- A hypothetical zero obstructs every random choice and every step uniformly. -/
theorem legalWalk_error_lower_bound_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (draw : ℕ → LegalPacketIndex A)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (n : ℕ) :
    (2*s.re-1)/‖s‖^2 ≤ walkError (legalPacket A hA) draw hilbertOne n :=
  legalClosure_distance_sq_lower_bound_of_zeta A hA s hs hs1 hz
    ((hilbertLegalSubspace A).le_topologicalClosure
      (legalWalk_projection_mem A hA draw n hilbertOne))

/-- The deterministic limiting error is positive if a right-half-plane zero exists. -/
theorem legalWalk_limitingError_lower_bound_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2*s.re-1)/‖s‖^2 ≤ limitingError (legalPacket A hA) hilbertOne := by
  apply legalClosure_distance_sq_lower_bound_of_zeta A hA s hs hs1 hz
  rw [← dictionaryClosure_legalPacket A hA]
  exact (dictionaryClosure (legalPacket A hA)).starProjection_apply_mem hilbertOne

end RiemannResearch.RH.Pareto
