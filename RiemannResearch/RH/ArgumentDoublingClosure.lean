import RiemannResearch.RH.MobiusResidualFirstCoordinate

/-!
# Argument-doubling closure as an explicit sufficient condition for RH

Source: user-provided CRT/orbit research direction and the ensuing argument-
doubling construction, 2026-09-20. The modular identity and dominated-convergence
argument are formalized here; no claim of mathematical novelty is made.

The closed span S contains the normalized residues g_d(n) = (n mod d) / d.
If S is invariant under f(n) ↦ f(2*n), its iterates contain
g_(2^k+1)(2^k*n). These vectors take values in [0,1] and tend coordinatewise
to the constant target on positive coordinates, hence converge in the actual
Pareto Hilbert norm. Closedness and the existing Mellin bridge then imply RH.

Status: conditional research reduction. ArgumentDoublingInvariant is Open.
Neither CRT orbit exhaustion nor the established floor-dilation invariance
supplies that hypothesis. No unconditional theorem of RiemannHypothesis is
claimed in this module.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

private theorem reverseResidue_head (m n : ℕ) (hn : 0 < n) (hnm : n < m + 1) :
    residueFraction (m + 1) (m * n) = 1 - (n : ℝ) / (m + 1 : ℕ) := by
  have hsub : m + 1 - n + n = m + 1 := Nat.sub_add_cancel hnm.le
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have heq : m * n = (n - 1) * (m + 1) + (m + 1 - n) := by nlinarith
  have hmod : (m * n) % (m + 1) = m + 1 - n := by
    rw [heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show m + 1 - n < m + 1 by omega)]
  simp only [residueFraction, hmod]
  rw [Nat.cast_sub hnm.le]
  have hmR : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem hilbert_tendsto_one_of_bounded_coordinates (v : ℕ → ThresholdHilbert)
    (hb : ∀ k n, 0 ≤ hilbertSequence (v k) n ∧ hilbertSequence (v k) n ≤ 1)
    (hp : ∀ n, 0 < n → Tendsto (fun k => hilbertSequence (v k) n) atTop (𝓝 1)) :
    Tendsto v atTop (𝓝 hilbertOne) := by
  have hsub (f g : ThresholdHilbert) :
      hilbertSequence (f - g) = hilbertSequence f - hilbertSequence g :=
    hilbertSequenceLinear.map_sub f g
  have hs : Tendsto (fun k => ‖v k - hilbertOne‖ ^ 2) atTop (𝓝 0) := by
    have ht := tendsto_tsum_of_dominated_convergence
      (f := fun k n => positiveWeight n *
        (hilbertSequence (v k) n - hilbertSequence hilbertOne n) ^ 2)
      (g := fun _ : ℕ => (0 : ℝ)) (𝓕 := atTop)
      positiveWeight_summable ?_ ?_
    · simpa only [hilbert_norm_weighted_sq, hsub, Pi.sub_apply,
        tsum_zero] using ht
    · intro n
      by_cases hn : n = 0
      · subst n
        simp
      · have ht := ((hp n (Nat.pos_of_ne_zero hn)).sub
          (tendsto_const_nhds (x := hilbertSequence hilbertOne n))).pow 2
        simpa [hilbertOne_sequence, zeroAnchor, hn] using ht.const_mul (positiveWeight n)
    · exact Eventually.of_forall (fun k n => by
        cases n with
        | zero => simpa using positiveWeight_nonneg 0
        | succ n =>
          have h := hb k (n + 1)
          have h1 : hilbertSequence hilbertOne (n + 1) = 1 := by
            rw [hilbertOne_sequence]
            simp [zeroAnchor]
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))]
          have he : (hilbertSequence (v k) (n + 1) -
              hilbertSequence hilbertOne (n + 1)) ^ 2 ≤ 1 := by
            rw [h1]
            nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
          simpa using mul_le_mul_of_nonneg_left he (positiveWeight_nonneg (n + 1)))
  have hn : Tendsto (fun k => ‖v k - hilbertOne‖) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- The known floor dilation is different from the required even sampling. -/
theorem floorDilation_ne_argumentDoubling :
    dilation 2 (residueFraction 3) ≠ fun n => residueFraction 3 (2 * n) := by
  intro he
  have h1 := congrFun he 1
  norm_num [dilation, residueFraction] at h1

namespace CoefficientStabilization

/-- Invariance under sampling even arguments, expressed in physical coordinates.
This property is an open hypothesis, not the already proved floor-dilation invariance. -/
def ArgumentDoublingInvariant : Prop :=
  ∀ f : ThresholdHilbert, f ∈ closedSpace →
    ∃ g : ThresholdHilbert, g ∈ closedSpace ∧
      hilbertSequence g = fun n => hilbertSequence f (2 * n)

theorem iterated_argumentDoubling (h : ArgumentDoublingInvariant)
    (k : ℕ) (f : ThresholdHilbert) (hf : f ∈ closedSpace) :
    ∃ g : ThresholdHilbert, g ∈ closedSpace ∧
      hilbertSequence g = fun n => hilbertSequence f (2 ^ k * n) := by
  induction k with
  | zero => exact ⟨f, hf, by simp⟩
  | succ k ih =>
    obtain ⟨g, hg, he⟩ := ih
    obtain ⟨u, hu, hue⟩ := h g hg
    refine ⟨u, hu, ?_⟩
    rw [hue, he]
    simp only [pow_succ, Nat.mul_assoc]

theorem hilbertOne_mem_of_argumentDoubling (h : ArgumentDoublingInvariant) :
    hilbertOne ∈ closedSpace := by
  have hex (k : ℕ) : ∃ g : ThresholdHilbert, g ∈ closedSpace ∧
      hilbertSequence g = fun n =>
        hilbertSequence (normalizedResidueHilbert (2 ^ k + 1) (by positivity))
          (2 ^ k * n) :=
    iterated_argumentDoubling h k _ ((Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
      (normalizedResidue_mem_atomSpan _ (by positivity)))
  choose v hv hseq using hex
  have hf (k n : ℕ) : hilbertSequence (v k) n =
      residueFraction (2 ^ k + 1) (2 ^ k * n) := by
    rw [hseq k, normalizedResidueHilbert_sequence]
  have hb (k n : ℕ) :
      0 ≤ hilbertSequence (v k) n ∧ hilbertSequence (v k) n ≤ 1 := by
    rw [hf]
    unfold residueFraction
    constructor
    · positivity
    · apply le_of_lt
      apply (div_lt_one (by positivity : (0 : ℝ) < ((2 ^ k + 1 : ℕ) : ℝ))).mpr
      exact_mod_cast Nat.mod_lt (2 ^ k * n) (by positivity : 0 < 2 ^ k + 1)
  have hd : Tendsto (fun k : ℕ => ((2 ^ k + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)))
  have hi := tendsto_inv_atTop_zero.comp hd
  have hp (n : ℕ) (hn : 0 < n) :
      Tendsto (fun k => hilbertSequence (v k) n) atTop (𝓝 1) := by
    have hl : Tendsto (fun k : ℕ => 1 - (n : ℝ) * ((2 ^ k + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 1) := by
      simpa only [Function.comp_def, mul_zero, sub_zero] using
        tendsto_const_nhds.sub (hi.const_mul (n : ℝ))
    apply (tendsto_congr' ?_).mpr hl
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [hf, reverseResidue_head _ _ hn (by
      have ht := Nat.lt_two_pow_self (n := k)
      omega)]
    rw [div_eq_mul_inv]
  have hc : IsClosed (closedSpace : Set ThresholdHilbert) :=
    Submodule.isClosed_topologicalClosure _
  exact hc.mem_of_tendsto (hilbert_tendsto_one_of_bounded_coordinates v hb hp)
    (Eventually.of_forall hv)

/-- Conditional research reduction. The argument-doubling hypothesis remains open. -/
theorem riemannHypothesis_of_argumentDoubling
    (h : ArgumentDoublingInvariant) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (hilbertOne_mem_of_argumentDoubling h))


end CoefficientStabilization
end RiemannResearch.RH.Pareto
