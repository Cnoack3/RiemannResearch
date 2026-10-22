/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteConstrainedProjection
import RiemannResearch.Analysis.FiniteGramRange
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Feasible complete-Gram constraints and exact head repair

Source: user-provided continuation agenda, 22 October 2026, Section 5.
This extends the existing full-rank constrained projection to dependent
observation rows. Compatibility and bounded solvability are proved from
the directional inequality; no pseudoinverse or row independence is assumed.
All energies are ambient Hilbert norms, with signed terms retained.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteFeasibleGramRepair

open FiniteHilbertGram FiniteConstrainedProjection

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [Fintype κ] in
/-- Arbitrary compatible source in a possibly singular actual Gram system.
This generalizes `exists_gram_eq_one_of_synthesis_null_sum_zero`. -/
theorem exists_normal_of_compatible (v : ι → H) (b : ι → ℝ)
    (hnull : ∀ c : ι → ℝ,
      Fintype.linearCombination ℝ v c = 0 → ∑ i, c i * b i = 0) :
    ∃ d : ι → ℝ, ∀ i,
      inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i := by
  let eb : EuclideanSpace ℝ ι := WithLp.toLp 2 b
  have hsym : ∀ x y, inner ℝ (gramEuclidean v x) y =
      inner ℝ x (gramEuclidean v y) := by
    intro x y
    calc
      _ = inner ℝ y (gramEuclidean v x) := real_inner_comm _ _
      _ = inner ℝ (Fintype.linearCombination ℝ v y.ofLp)
          (Fintype.linearCombination ℝ v x.ofLp) := gramEuclidean_pairing v y x
      _ = inner ℝ (Fintype.linearCombination ℝ v x.ofLp)
          (Fintype.linearCombination ℝ v y.ofLp) := real_inner_comm _ _
      _ = _ := (gramEuclidean_pairing v x y).symm
  have hb : ∀ x, gramEuclidean v x = 0 → inner ℝ x eb = 0 := by
    intro x hx
    have he := gramEuclidean_pairing v x x
    rw [hx, inner_zero_right, real_inner_self_eq_norm_sq] at he
    have hz : Fintype.linearCombination ℝ v x.ofLp = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (Fintype.linearCombination ℝ v x.ofLp)]
    have hs := hnull x.ofLp hz
    rw [PiLp.inner_apply]
    simpa [RCLike.inner_apply', eb, mul_comm] using hs
  obtain ⟨d, hd⟩ := exists_preimage_of_kernel_orthogonal (gramEuclidean v) hsym eb hb
  have hn : gram v d.ofLp = b := congrArg WithLp.ofLp hd
  exact ⟨d.ofLp, fun i => congrFun hn i⟩

omit [Fintype κ] in
/-- Feasibility alone supplies a normal solution; row rank is unnecessary. -/
theorem exists_normal_of_feasible (v : ι → H) (b : ι → ℝ)
    (y : H) (hy : ∀ i, inner ℝ (v i) y = b i) :
    ∃ d : ι → ℝ, ∀ i,
      inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i := by
  apply exists_normal_of_compatible v b
  intro c hc
  have hp : inner ℝ (Fintype.linearCombination ℝ v c) y =
      ∑ i, c i * b i := by
    rw [inner_synthesis_left]
    simp only [hy]
  rw [hc, inner_zero_left] at hp
  exact hp.symm

omit [Fintype κ] in
/-- Pairing with a represented solution of the actual Gram normal equations. -/
theorem normal_pairing (v : ι → H) (b d c : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i) :
    inner ℝ (Fintype.linearCombination ℝ v c)
      (Fintype.linearCombination ℝ v d) = ∑ i, c i * b i := by
  rw [inner_synthesis_left]
  simp only [hn]

omit [Fintype κ] in
/-- Normal-equation energy, with every signed mixed contribution retained. -/
theorem normal_energy (v : ι → H) (b d : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i) :
    ‖Fintype.linearCombination ℝ v d‖ ^ 2 = ∑ i, d i * b i := by
  simpa only [real_inner_self_eq_norm_sq] using normal_pairing v b d d hn

omit [Fintype κ] in
/-- Rank-free HEAD completion for every feasible ambient vector. -/
theorem feasible_completion (v : ι → H) (b d : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i)
    (y : H) (hy : ∀ i, inner ℝ (v i) y = b i) :
    ‖y‖ ^ 2 = ‖Fintype.linearCombination ℝ v d‖ ^ 2 +
      ‖y - Fintype.linearCombination ℝ v d‖ ^ 2 := by
  have hp : inner ℝ (Fintype.linearCombination ℝ v d) y =
      inner ℝ (Fintype.linearCombination ℝ v d)
        (Fintype.linearCombination ℝ v d) := by
    rw [inner_synthesis_left, inner_synthesis_left]
    simp only [hy, hn]
  have hp' : inner ℝ y (Fintype.linearCombination ℝ v d) =
      ‖Fintype.linearCombination ℝ v d‖ ^ 2 := by
    calc
      _ = inner ℝ (Fintype.linearCombination ℝ v d) y := real_inner_comm _ _
      _ = _ := hp.trans (real_inner_self_eq_norm_sq _)
  rw [norm_sub_sq_real, hp']
  ring

omit [Fintype κ] in
theorem feasible_minimizes (v : ι → H) (b d : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i)
    (y : H) (hy : ∀ i, inner ℝ (v i) y = b i) :
    ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [feasible_completion v b d hn y hy]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [Fintype κ] in
theorem normal_direction_bound (v : ι → H) (b d c : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i) :
    (∑ i, c i * b i) ^ 2 ≤ ‖Fintype.linearCombination ℝ v d‖ ^ 2 *
      ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
  rw [← normal_pairing v b d c hn]
  have h := real_inner_mul_inner_self_le
    (Fintype.linearCombination ℝ v c) (Fintype.linearCombination ℝ v d)
  simpa only [real_inner_self_eq_norm_sq, ← pow_two, mul_comm] using h

omit [Fintype κ] in
/-- Exact directional dual, requiring no inverse and no row independence. -/
theorem normal_energy_le_iff (v : ι → H) (b d : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i)
    (B : ℝ) (hB : 0 ≤ B) :
    ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ B ↔
      ∀ c : ι → ℝ, (∑ i, c i * b i) ^ 2 ≤
        B * ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
  constructor
  · intro hb c
    exact (normal_direction_bound v b d c hn).trans
      (mul_le_mul_of_nonneg_right hb (sq_nonneg _))
  · intro hd
    have ht := hd d
    rw [← normal_energy v b d hn] at ht
    by_contra h
    have he : B < ‖Fintype.linearCombination ℝ v d‖ ^ 2 := lt_of_not_ge h
    have hp : 0 < ‖Fintype.linearCombination ℝ v d‖ ^ 2 := lt_of_le_of_lt hB he
    have hm := mul_lt_mul_of_pos_right he hp
    nlinarith

omit [Fintype κ] in
/-- The directional condition itself guarantees feasibility and a bounded
minimum-energy representer, including when the actual Gram is singular. -/
theorem bounded_normal_iff_directional (v : ι → H) (b : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B) :
    (∃ d : ι → ℝ,
      (∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i) ∧
        ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ B) ↔
      ∀ c : ι → ℝ, (∑ i, c i * b i) ^ 2 ≤
        B * ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
  constructor
  · rintro ⟨d, hn, hb⟩
    exact (normal_energy_le_iff v b d hn B hB).mp hb
  · intro hb
    have hnull : ∀ c : ι → ℝ,
        Fintype.linearCombination ℝ v c = 0 → ∑ i, c i * b i = 0 := by
      intro c hc
      have ht := hb c
      rw [hc, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at ht
      nlinarith [sq_nonneg (∑ i, c i * b i)]
    obtain ⟨d, hn⟩ := exists_normal_of_compatible v b hnull
    exact ⟨d, hn, (normal_energy_le_iff v b d hn B hB).mpr hb⟩

/-- A representer multiplier replaces the unavailable inverse of a singular
physical-head Gram. The baseline is the actual orthogonal projection. -/
theorem repaired_error_identity {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i) :
    ‖x - (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
      Fintype.linearCombination ℝ (projectedRow hv h) d)‖ ^ 2 =
      ‖projectionResidual hv x‖ ^ 2 + ∑ i, d i * headMismatch hv h x i := by
  have he : x - (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
      Fintype.linearCombination ℝ (projectedRow hv h) d) =
      projectionResidual hv x - Fintype.linearCombination ℝ (projectedRow hv h) d := by
    unfold projectionResidual
    abel
  rw [he, norm_sub_sq_real, residual_inner_rowSynthesis hv h x d,
    normal_energy (projectedRow hv h) (headMismatch hv h x) d hn]
  ring

theorem repaired_observation {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (i : κ) :
    inner ℝ (h i) (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
      Fintype.linearCombination ℝ (projectedRow hv h) d) = inner ℝ (h i) x := by
  rw [inner_add_right, projectedRow_pairing_rowSynthesis hv h d i, hn i]
  simp only [headMismatch, projectionResidual, inner_sub_right]
  ring

/-- Rank-free REPAIR completion against every legal exact-head competitor. -/
theorem repaired_error_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v c) = inner ℝ (h i) x) :
    ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖projectionResidual hv x‖ ^ 2 + ∑ i, d i * headMismatch hv h x i +
        ‖Fintype.linearCombination ℝ v c -
          (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
            Fintype.linearCombination ℝ (projectedRow hv h) d)‖ ^ 2 := by
  let q := c - inverseCoeff hv x
  have hq : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ v q) = headMismatch hv h x i := by
    intro i
    rw [← projectedRow_pairing hv h q i]
    change inner ℝ (h i)
      (Fintype.linearCombination ℝ v (c - inverseCoeff hv x)) = _
    rw [map_sub, inner_sub_right, hc i]
    simp only [headMismatch, projectionResidual, inner_sub_right]
  have hdiff : Fintype.linearCombination ℝ v c -
      (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
        Fintype.linearCombination ℝ (projectedRow hv h) d) =
      Fintype.linearCombination ℝ v q -
        Fintype.linearCombination ℝ (projectedRow hv h) d := by
    dsimp [q]
    rw [map_sub]
    abel
  rw [residual_completion hv x c, hdiff]
  change ‖projectionResidual hv x‖ ^ 2 + ‖Fintype.linearCombination ℝ v q‖ ^ 2 = _
  rw [feasible_completion (projectedRow hv h) (headMismatch hv h x) d hn
    (Fintype.linearCombination ℝ v q) hq,
    normal_energy (projectedRow hv h) (headMismatch hv h x) d hn]
  ring

/-- A frame estimate on the actual synthesized normal vector gives an energy
bound without requiring invertibility of the row Gram matrix. -/
theorem normal_energy_le_of_frame_at_solution
    (v : ι → H) (b d : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i)
    (c K : ℝ) (hc : 0 < c)
    (hframe : c * ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤
      ∑ i, (inner ℝ (v i) (Fintype.linearCombination ℝ v d)) ^ 2)
    (hsource : ∑ i, (b i) ^ 2 ≤ K) :
    c * ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ K ∧
      ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ K / c := by
  have he : c * ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ K := by
    simp only [hn] at hframe
    exact hframe.trans hsource
  constructor
  · exact he
  · apply (le_div_iff₀ hc).2
    simpa only [mul_comm] using he

/-- A uniform lower frame estimate is needed only on the row span; permanent
linear relations between the physical head rows are allowed. -/
theorem normal_energy_le_of_frame
    (v : ι → H) (b d : ι → ℝ)
    (hn : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i)
    (c K : ℝ) (hc : 0 < c)
    (hframe : ∀ a : ι → ℝ, c * ‖Fintype.linearCombination ℝ v a‖ ^ 2 ≤
      ∑ i, (inner ℝ (v i) (Fintype.linearCombination ℝ v a)) ^ 2)
    (hsource : ∑ i, (b i) ^ 2 ≤ K) :
    ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ K / c :=
  (normal_energy_le_of_frame_at_solution v b d hn c K hc (hframe d) hsource).2

/-- Feasibility plus a lower frame bound gives a bounded normal solution.
No source compatibility or rank condition is suppressed. -/
theorem exists_bounded_normal_of_feasible_frame
    (v : ι → H) (b : ι → ℝ)
    (y : H) (hy : ∀ i, inner ℝ (v i) y = b i)
    (c K : ℝ) (hc : 0 < c)
    (hframe : ∀ a : ι → ℝ, c * ‖Fintype.linearCombination ℝ v a‖ ^ 2 ≤
      ∑ i, (inner ℝ (v i) (Fintype.linearCombination ℝ v a)) ^ 2)
    (hsource : ∑ i, (b i) ^ 2 ≤ K) :
    ∃ d : ι → ℝ,
      (∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v d) = b i) ∧
      ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤ K / c := by
  obtain ⟨d, hn⟩ := exists_normal_of_feasible v b y hy
  exact ⟨d, hn, normal_energy_le_of_frame v b d hn c K hc hframe hsource⟩

/-- Pythagoras for an arbitrary signed observation direction and its actual
finite legal projection. No independence of the observation rows is assumed. -/
theorem headProbe_projection_completion {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (c : κ → ℝ) :
    ‖Fintype.linearCombination ℝ h c‖ ^ 2 =
      ‖Fintype.linearCombination ℝ (projectedRow hv h) c‖ ^ 2 +
      ‖Fintype.linearCombination ℝ h c -
        Fintype.linearCombination ℝ (projectedRow hv h) c‖ ^ 2 := by
  have hp : inner ℝ (Fintype.linearCombination ℝ h c)
      (Fintype.linearCombination ℝ (projectedRow hv h) c) =
      inner ℝ (Fintype.linearCombination ℝ (projectedRow hv h) c)
        (Fintype.linearCombination ℝ (projectedRow hv h) c) := by
    rw [inner_synthesis_left, inner_synthesis_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [projectedRow_pairing_rowSynthesis hv h c i]
  have hpNorm : inner ℝ (Fintype.linearCombination ℝ h c)
      (Fintype.linearCombination ℝ (projectedRow hv h) c) =
      ‖Fintype.linearCombination ℝ (projectedRow hv h) c‖ ^ 2 := by
    rw [hp, real_inner_self_eq_norm_sq]
  simp only [norm_sub_sq_real, hpNorm]
  ring

/-- The signed head defect pairs with the complementary observation probe.
The component in the legal span contributes exactly zero. -/
theorem headMismatch_eq_complement_pairing {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (x : H) (c : κ → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ h c -
      Fintype.linearCombination ℝ (projectedRow hv h) c)
        (projectionResidual hv x) =
      ∑ i, c i * headMismatch hv h x i := by
  have hz : inner ℝ (Fintype.linearCombination ℝ (projectedRow hv h) c)
      (projectionResidual hv x) = 0 := by
    rw [real_inner_comm]
    exact residual_inner_rowSynthesis hv h x c
  rw [inner_sub_left, hz, sub_zero, inner_synthesis_left]
  rfl

/-- Exact complementary covariance majorant. For physical Q Riesz rows,
the right-hand norm difference is y^T (D-W) y with D_nn=ζ(2)n².
It retains every mixed term and makes no inverse or rank assumption. -/
theorem headMismatch_sq_le_complement_energy {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (x : H) (c : κ → ℝ) :
    (∑ i, c i * headMismatch hv h x i) ^ 2 ≤
      ‖projectionResidual hv x‖ ^ 2 *
        (‖Fintype.linearCombination ℝ h c‖ ^ 2 -
          ‖Fintype.linearCombination ℝ (projectedRow hv h) c‖ ^ 2) := by
  have he := headProbe_projection_completion hv h c
  have hrem : ‖Fintype.linearCombination ℝ h c -
      Fintype.linearCombination ℝ (projectedRow hv h) c‖ ^ 2 =
      ‖Fintype.linearCombination ℝ h c‖ ^ 2 -
        ‖Fintype.linearCombination ℝ (projectedRow hv h) c‖ ^ 2 := by
    linarith
  have hc := real_inner_mul_inner_self_le
    (Fintype.linearCombination ℝ h c -
      Fintype.linearCombination ℝ (projectedRow hv h) c)
    (projectionResidual hv x)
  simpa only [headMismatch_eq_complement_pairing hv h x c,
    real_inner_self_eq_norm_sq, ← pow_two, hrem, mul_comm] using hc

/-- Source: the user-directed reduced-head investigation, 22 October 2026.
Only the actual normal-solution probe needs a comparison estimate. This can
be strictly sharper than a smallest-eigenvalue bound over every direction. -/
theorem normal_repair_le_of_probe_comparison {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (K : ℝ) (hK : 1 ≤ K)
    (hprobe : ‖Fintype.linearCombination ℝ h d‖ ^ 2 ≤
      K * ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2) :
    ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2 ≤
      ‖projectionResidual hv x‖ ^ 2 * (K - 1) := by
  have he := normal_energy (projectedRow hv h) (headMismatch hv h x) d hn
  have hb := headMismatch_sq_le_complement_energy hv h x d
  rw [← he] at hb
  have hδ := sq_nonneg ‖projectionResidual hv x‖
  have hE := sq_nonneg ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖
  by_cases hz : ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2 = 0
  · rw [hz]
    exact mul_nonneg hδ (by linarith)
  · have hp : 0 < ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2 :=
      lt_of_le_of_ne hE (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    have hc := mul_le_mul_of_nonneg_left hprobe hδ
    nlinarith


/-- An unconditional estimate in the actual nonzero repair direction.
Uniform control of this Rayleigh quotient is not asserted. -/
theorem normal_repair_target_rayleigh {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (hE : 0 < ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2) :
    ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2 ≤
      ‖projectionResidual hv x‖ ^ 2 *
        (‖Fintype.linearCombination ℝ h d‖ ^ 2 /
          ‖Fintype.linearCombination ℝ (projectedRow hv h) d‖ ^ 2 - 1) := by
  apply normal_repair_le_of_probe_comparison hv h x d hn
  · apply (le_div_iff₀ hE).mpr
    have he := headProbe_projection_completion hv h d
    nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ h d -
      Fintype.linearCombination ℝ (projectedRow hv h) d‖]
  · rw [div_mul_cancel₀ _ (ne_of_gt hE)]


end RiemannResearch.Analysis.FiniteFeasibleGramRepair
