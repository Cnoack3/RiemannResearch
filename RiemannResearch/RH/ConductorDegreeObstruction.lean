import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoBoundedInteraction

/-!
# Fixed conductor degree: a quantitative Hilbert obstruction

Source: Christian Noack, `signal_to_noise_RH_program (2)(1).pdf`,
Conjecture 8.2. The existing `boundedPrimeSupport_no_pointwise_limit`
already proves a stronger pointwise obstruction. This module supplies its
actual Hilbert-closure bridge, an exact Pythagorean error identity, and a
centered signal/noise bound, using the already verified Mobius functional.
No RH or analytic estimate is assumed.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto
namespace ConductorDegreeObstruction

/-- The actual integrated packets whose conductors belong to a chosen set. -/
def span (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f : ThresholdHilbert | ∃ q : ℕ,
    q ∈ A ∧ f = ramanujanPacketHilbert q}

/-- Omitting every multiple of one conductor forces an exact continuous zero. -/
theorem span_le_kernel (A : Set ℕ) (m : ℕ) (hm : 1 < m)
    (hA : ∀ q ∈ A, 0 < q ∧ ¬ m ∣ q) :
    span A ≤ (mobiusDifferenceCLM m).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, hq, rfl⟩
  change mobiusDifferenceCLM m (ramanujanPacketHilbert q) = 0
  rw [mobiusDifferenceCLM_ramanujanPacketHilbert m q hm (hA q hq).1,
    if_neg (hA q hq).2]

/-- The witness annihilates the entire Hilbert closure. -/
theorem closure_le_kernel (A : Set ℕ) (m : ℕ) (hm : 1 < m)
    (hA : ∀ q ∈ A, 0 < q ∧ ¬ m ∣ q) :
    (span A).topologicalClosure ≤ (mobiusDifferenceCLM m).ker := by
  apply Submodule.topologicalClosure_minimal
  · exact span_le_kernel A m hm hA
  · exact (mobiusDifferenceCLM m).isClosed_ker

/-- Any omitted squarefree divisor excludes the constant from the closure. -/
theorem one_not_mem_closure (A : Set ℕ) (m : ℕ) (hm : 1 < m)
    (hsf : Squarefree m) (hA : ∀ q ∈ A, 0 < q ∧ ¬ m ∣ q) :
    hilbertOne ∉ (span A).topologicalClosure := by
  intro hf
  have hz : mobiusDifferenceCLM m hilbertOne = 0 := closure_le_kernel A m hm hA hf
  rw [mobius_coordinate_one m (by omega)] at hz
  have hmu := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
  exact hmu (by exact_mod_cast hz)

/-- Conjecture 8.2, strengthened to allow nonsquarefree conductors as well. -/
theorem fixed_prime_support_one_not_mem_closure (D : ℕ) :
    hilbertOne ∉ (span {q : ℕ | 0 < q ∧ q.primeFactors.card ≤ D}).topologicalClosure := by
  obtain ⟨m, hm, hsf, hcard⟩ := exists_squarefree_large_prime_support D
  apply one_not_mem_closure _ m hm hsf
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro hd
  have hc := Finset.card_le_card (Nat.primeFactors_mono hd (ne_of_gt hq.1))
  have hqcard := hq.2
  omega

/-- A squarefree witness has strictly positive squared operator norm. -/
theorem coordinate_norm_sq_pos (m : ℕ) (hm : 0 < m) (hsf : Squarefree m) :
    0 < ‖mobiusDifferenceCLM m‖ ^ 2 := by
  have hmu : (ArithmeticFunction.moebius m : ℝ) ≠ 0 := by
    exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
  have hn : mobiusDifferenceCLM m ≠ 0 := by
    intro he
    have h := mobius_coordinate_one m hm
    rw [he] at h
    simp only [zero_apply] at h
    exact hmu h.symm
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

/-- Exact error decomposition retaining the signed witness correction.
The denominator is the finite sum in `mobiusDifferenceCLM_norm_sq`. -/
theorem error_identity (m : ℕ) (hm : 0 < m) (hsf : Squarefree m)
    (F : ThresholdHilbert) (hF : mobiusDifferenceCLM m F = 0) :
    ‖hilbertOne - F‖ ^ 2 =
      (ArithmeticFunction.moebius m : ℝ) ^ 2 / ‖mobiusDifferenceCLM m‖ ^ 2 +
      ‖hilbertOne - F +
        (-(ArithmeticFunction.moebius m : ℝ) / ‖mobiusDifferenceCLM m‖ ^ 2) •
          mobiusRieszHilbert m‖ ^ 2 := by
  have hi : inner ℝ (hilbertOne - F) (mobiusRieszHilbert m) =
      (ArithmeticFunction.moebius m : ℝ) := by
    rw [real_inner_comm, mobiusRieszHilbert_inner, map_sub,
      mobius_coordinate_one m hm, hF, sub_zero]
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, mobiusRieszHilbert_norm]
  have hn : ‖mobiusDifferenceCLM m‖ ^ 2 ≠ 0 :=
    ne_of_gt (coordinate_norm_sq_pos m hm hsf)
  field_simp [hn]
  ring

/-- A concrete positive error floor, valid for every vector in the kernel. -/
theorem error_floor (m : ℕ) (hm : 0 < m) (hsf : Squarefree m)
    (F : ThresholdHilbert) (hF : mobiusDifferenceCLM m F = 0) :
    0 < (ArithmeticFunction.moebius m : ℝ) ^ 2 / ‖mobiusDifferenceCLM m‖ ^ 2 ∧
      (ArithmeticFunction.moebius m : ℝ) ^ 2 / ‖mobiusDifferenceCLM m‖ ^ 2 ≤
        ‖hilbertOne - F‖ ^ 2 := by
  constructor
  · apply div_pos
    · apply sq_pos_of_ne_zero
      exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
    · exact coordinate_norm_sq_pos m hm hsf
  · rw [error_identity m hm hsf F hF]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- Sharp centered Cauchy bound from the finite-support witness.
For squarefree m, the Mobius square is one, so this reads
mean(F)^2 ≤ (B_m - 1) Var(F). No covariance truncation occurs. -/
theorem centered_signal_bound (m : ℕ) (hm : 0 < m)
    (F : ThresholdHilbert) (hF : mobiusDifferenceCLM m F = 0) :
    (ArithmeticFunction.moebius m : ℝ) ^ 2 * (inner ℝ hilbertOne F) ^ 2 ≤
      (‖mobiusDifferenceCLM m‖ ^ 2 - (ArithmeticFunction.moebius m : ℝ) ^ 2) *
        ‖F - (inner ℝ hilbertOne F) • hilbertOne‖ ^ 2 := by
  let mu : ℝ := ArithmeticFunction.moebius m
  let a : ℝ := inner ℝ hilbertOne F
  let R : ThresholdHilbert := mobiusRieszHilbert m
  have hRone : inner ℝ R hilbertOne = mu := by
    dsimp [R, mu]
    rw [mobiusRieszHilbert_inner, mobius_coordinate_one m hm]
  have hRF : inner ℝ R F = 0 := by
    dsimp [R]
    rw [mobiusRieszHilbert_inner, hF]
  have hnorm : ‖R - mu • hilbertOne‖ ^ 2 =
      ‖mobiusDifferenceCLM m‖ ^ 2 - mu ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hilbertOne_norm_sq, real_inner_smul_right, hRone]
    dsimp [R]
    rw [mobiusRieszHilbert_norm]
    ring
  have hcross : inner ℝ (R - mu • hilbertOne) (F - a • hilbertOne) = -mu * a := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      hRone, hRF]
    dsimp [a]
    ring
  have hc := real_inner_mul_inner_self_le (R - mu • hilbertOne) (F - a • hilbertOne)
  rw [hcross, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hnorm] at hc
  change mu ^ 2 * a ^ 2 ≤
    (‖mobiusDifferenceCLM m‖ ^ 2 - mu ^ 2) * ‖F - a • hilbertOne‖ ^ 2
  nlinarith only [hc]

end ConductorDegreeObstruction
end RiemannResearch.RH.Pareto
