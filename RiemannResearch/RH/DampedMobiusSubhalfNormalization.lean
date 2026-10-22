/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.VectorKronecker
import RiemannResearch.RH.DampedMobiusUniformHalfRange

/-!
# Unconditional normalized signed limits below half damping

Every epsilon < 1/2 has full signed cutoff norm negligible relative to
(M+1)^(1/2-epsilon). The normalized full energy, diagonal, and signed
off-diagonal all tend to zero. The normalized signed physical heads
vanish uniformly in their head cutoff. This includes zero damping.

The only arithmetic input is the already checked natural-order Hilbert
convergence at epsilon = 1/2. Exact inverse-power factorization and the
vector Kronecker lemma transfer it to the normalized smaller-damping
cutoffs. Norms and absolute values are taken after signed sums.

Source for the underlying endpoint membership statement: J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and
a theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166. The normalized transfer is proved
explicitly from the repository endpoint and the classical Kronecker
argument; no novelty claim is made.

The normalizing powers grow for epsilon < 1/2. These results do not
assert bounded unnormalized cutoff norms, subhalf arithmetic finite
energy, or RH.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Below half damping the full signed vector, after its critical power
normalization, tends to zero unconditionally. -/
theorem dampedMobius_subhalf_normalized_vector_tendsto {ε : ℝ}
    (hε : ε < (1 / 2 : ℝ)) :
    Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ (ε - 1 / 2) •
      arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M) atTop (𝓝 0) := by
  obtain ⟨f, _, hf⟩ := dampedMobius_half_cutoffs_converge
  have hp : Tendsto (signedVectorPrefix
      (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m)) atTop (𝓝 f) := by
    convert hf using 1
    funext n
    simp only [signedVectorPrefix, Finset.sum_neg_distrib, arithmeticFloorHilbertPartial]
  have h := signedVector_power_undamping_tendsto _ hp
    (show 0 < (1 / 2 : ℝ) - ε by linarith)
  simpa only [show -((1 / 2 : ℝ) - ε) = ε - 1 / 2 by ring,
    dampedMobiusPartial_from_half, show -(ε - 1 / 2) = (1 / 2 : ℝ) - ε by ring] using h

/-- The complete signed norm is negligible relative to the critical
power (M+1)^(1/2-epsilon), including at zero and negative damping. -/
theorem dampedMobius_subhalf_normalized_norm_tendsto {ε : ℝ}
    (hε : ε < (1 / 2 : ℝ)) :
    Tendsto (fun M : ℕ =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ /
        ((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε)) atTop (𝓝 0) := by
  have h := (dampedMobius_subhalf_normalized_vector_tendsto hε).norm
  have he (M : ℕ) : ‖((M + 1 : ℕ) : ℝ) ^ (ε - 1 / 2) •
      arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ =
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ /
        ((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε) := by
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      show ε - 1 / 2 = -((1 / 2 : ℝ) - ε) by ring, Real.rpow_neg (by positivity)]
    ring
  simpa only [he, norm_zero] using h

/-- The full cutoff energy vanishes after critical power normalization. -/
theorem dampedMobius_subhalf_normalized_energy_tendsto {ε : ℝ}
    (hε : ε < (1 / 2 : ℝ)) :
    Tendsto (fun M : ℕ =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 /
        ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have h := (dampedMobius_subhalf_normalized_norm_tendsto hε).pow 2
  have he (M : ℕ) :
      (((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε)) ^ 2 =
        ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  simpa only [div_pow, he, zero_pow (by norm_num : 2 ≠ 0)] using h

/-- Exact atom-square factorization, with no sign or positivity premise
on the damping parameter. -/
theorem dampedMobiusResidue_norm_sq_from_half (ε : ℝ) (m : ℕ) :
    ‖arithmeticResidueTerm (dampedMobiusWeight ε) m‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) ^ (1 - 2 * ε) *
        ‖arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m‖ ^ 2 := by
  rw [dampedMobiusResidue_from_half, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- The diagonal is negligible on the same scale even at zero damping,
where its unnormalized infinite sum is not assumed finite. -/
theorem dampedMobius_subhalf_normalized_diagonal_tendsto {ε : ℝ}
    (hε : ε < (1 / 2 : ℝ)) :
    Tendsto (fun M : ℕ => dampedMobiusGramDiagonal ε M /
      ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have hp : Tendsto (signedVectorPrefix (fun m =>
      ‖arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m‖ ^ 2)) atTop
      (𝓝 (dampedMobiusExactDiagonal (1 / 2))) :=
    (dampedMobiusResidue_norm_sq_summable (by norm_num : (0 : ℝ) < 1 / 2)).hasSum.tendsto_sum_nat
  have h := signedVector_power_undamping_tendsto _ hp
    (show 0 < 1 - 2 * ε by linarith)
  have he (M : ℕ) : ((M + 1 : ℕ) : ℝ) ^ (-(1 - 2 * ε)) •
      ∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℝ) ^ (1 - 2 * ε) •
        ‖arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) n‖ ^ 2 =
      dampedMobiusGramDiagonal ε M / ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε) := by
    simp only [smul_eq_mul, ← dampedMobiusResidue_norm_sq_from_half,
      Real.rpow_neg (by positivity : 0 ≤ ((M + 1 : ℕ) : ℝ)),
      dampedMobiusGramDiagonal]
    ring
  simpa only [he] using h

/-- The signed off-diagonal has the same vanishing normalized limit. -/
theorem dampedMobius_subhalf_normalized_offDiagonal_tendsto {ε : ℝ}
    (hε : ε < (1 / 2 : ℝ)) :
    Tendsto (fun M : ℕ => dampedMobiusGramOffDiagonal ε M /
      ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have h := (dampedMobius_subhalf_normalized_energy_tendsto hε).sub
    (dampedMobius_subhalf_normalized_diagonal_tendsto hε)
  simpa only [dampedMobius_partial_norm_sq_eq_signed, add_div, add_sub_cancel_left,
    sub_self] using h

/-- The absolute value is taken only after the complete signed Gram sum.
Its head is controlled by the full vector energy and the finite diagonal. -/
theorem dampedMobiusHeadOffDiagonal_abs_le_full_energy_add_diagonal
    (ε : ℝ) (H M : ℕ) :
    |dampedMobiusHeadOffDiagonal ε H M| ≤
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 +
        dampedMobiusGramDiagonal ε M := by
  have he := dampedMobius_partial_head_eq_signed ε H M
  have hp := paretoHeadPairing_self_le H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  have hp0 := paretoHeadPairing_self_nonneg H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  have hd : dampedMobiusHeadDiagonal ε H M ≤ dampedMobiusGramDiagonal ε M :=
    Finset.sum_le_sum (fun m _ =>
      paretoHeadPairing_self_le H (arithmeticResidueTerm (dampedMobiusWeight ε) m))
  rw [abs_le]
  constructor
  · linarith [sq_nonneg ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖]
  · linarith [dampedMobiusHeadDiagonal_nonneg ε H M,
      dampedMobiusGramDiagonal_nonneg ε M]

/-- Below one half, every signed physical head is negligible at the
critical power scale, uniformly in the head cutoff. -/
theorem dampedMobius_subhalf_normalized_signed_heads_uniform
    {ε : ℝ} (hε : ε < (1 / 2 : ℝ)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ M : ℕ in atTop, ∀ H : ℕ,
      |dampedMobiusHeadOffDiagonal ε H M| /
        ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤ η := by
  have hb : Tendsto (fun M : ℕ =>
      (‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 +
        dampedMobiusGramDiagonal ε M) /
          ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using
      (dampedMobius_subhalf_normalized_energy_tendsto hε).add
        (dampedMobius_subhalf_normalized_diagonal_tendsto hε)
  intro η hη
  filter_upwards [(tendsto_order.mp hb).2 η hη] with M hM
  intro H
  exact (div_le_div_of_nonneg_right
    (dampedMobiusHeadOffDiagonal_abs_le_full_energy_add_diagonal ε H M)
    (Real.rpow_nonneg (by positivity) _)).trans hM.le

/-- The physical head may be arbitrary and need not tend to infinity. -/
theorem dampedMobius_subhalf_normalized_moving_head_tendsto
    {ε : ℝ} (hε : ε < (1 / 2 : ℝ)) (H M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => |dampedMobiusHeadOffDiagonal ε (H j) (M j)| /
      ((M j + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j => ha.trans_le (by positivity))
  · intro b hb
    filter_upwards [hM.eventually
      (dampedMobius_subhalf_normalized_signed_heads_uniform hε (b / 2) (by positivity))]
      with j hj
    exact (hj (H j)).trans_lt (by linarith)

/-- At zero damping the raw signed Hilbert norm divided by sqrt(M+1)
tends to zero. No RH assumption is used. -/
theorem rawMobius_norm_div_sqrt_tendsto :
    Tendsto (fun M : ℕ =>
      ‖arithmeticFloorHilbertPartial (fun d => (ArithmeticFunction.moebius d : ℝ)) M‖ /
        Real.sqrt ((M + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hw := funext dampedMobiusWeight_at_zero
  simpa only [hw,
    sub_zero, Real.sqrt_eq_rpow] using
      dampedMobius_subhalf_normalized_norm_tendsto (by norm_num : (0 : ℝ) < 1 / 2)

/-- The complete raw signed Gram energy divided by M+1 tends to zero. -/
theorem rawMobius_energy_div_cutoff_tendsto :
    Tendsto (fun M : ℕ =>
      ‖arithmeticFloorHilbertPartial (fun d => (ArithmeticFunction.moebius d : ℝ)) M‖ ^ 2 /
        ((M + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hw := funext dampedMobiusWeight_at_zero
  simpa only [hw,
    mul_zero, sub_zero, Real.rpow_one] using
      dampedMobius_subhalf_normalized_energy_tendsto (by norm_num : (0 : ℝ) < 1 / 2)

end RiemannResearch.RH.Pareto
