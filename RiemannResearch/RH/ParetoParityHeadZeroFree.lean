import RiemannResearch.RH.ParetoParityHeadMellin
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Growth of the full error and zero-free strips for parity heads

The Mellin lower bound detects each zero separately. Little-o growth at one
specified exponent excludes zeros on the corresponding boundary as well.
The converse construction uses the natural approximation proposition explicitly.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- A zero forces a positive power of the physical head length in every
cofinal family of complete errors. -/
theorem parity_zero_free_of_little_o_heads
    (p : ℝ) (n : ℕ → ℕ) (v : ℕ → ThresholdHilbert)
    (hn : Tendsto n atTop atTop)
    (hv : ∀ i, v i ∈ closedSpace)
    (hhead : ∀ i k, k ≤ n i → hilbertSequence (v i) k = hilbertSequence parityAdjointPacket k)
    (hrate : Tendsto (fun i => ‖parityAdjointPacket - v i‖ ^ 2 / (n i : ℝ) ^ p)
      atTop (𝓝 0))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hp : p ≤ 2 * s.re - 1) : riemannZeta s ≠ 0 := by
  intro hz
  let c : ℝ := ((1 / 6 : ℝ) * (1 / ‖s‖)) ^ 2 * (2 * s.re - 1)
  have hs0 : s ≠ 0 := by
    intro he
    norm_num [he] at hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (sq_pos_of_pos (by positivity)) (by linarith)
  obtain ⟨i, hi, hiRate⟩ := ((hn.eventually (eventually_ge_atTop 1)).and
    (hrate.eventually_lt_const hc)).exists
  have hi' : (1 : ℝ) ≤ n i := by exact_mod_cast hi
  have hx : 0 < (n i : ℝ) ^ p := Real.rpow_pos_of_pos (zero_lt_one.trans_le hi') _
  have hf := parityAdjointPacket_exact_head_power_lower s hs hs1 hz (n i) hi (v i)
    (hv i) (hhead i)
  have hle := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hi' hp) hc.le
  exact (not_lt_of_ge (hle.trans hf)) ((div_lt_iff₀ hx).mp hiRate)

/-- Complete errors smaller than every positive power exclude every zero
strictly to the right of the critical line. The finite supports may grow independently. -/
theorem riemannHypothesis_of_parity_subpower_heads
    (n : ℕ → ℕ) (v : ℕ → ThresholdHilbert)
    (hn : Tendsto n atTop atTop)
    (hv : ∀ i, v i ∈ closedSpace)
    (hhead : ∀ i k, k ≤ n i → hilbertSequence (v i) k = hilbertSequence parityAdjointPacket k)
    (hrate : ∀ p : ℝ, 0 < p →
      Tendsto (fun i => ‖parityAdjointPacket - v i‖ ^ 2 / (n i : ℝ) ^ p) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt
  have hs1 : s ≠ 1 := by
    intro he
    norm_num [he] at hlt
  exact parity_zero_free_of_little_o_heads (2 * s.re - 1) n v hn hv hhead
    (hrate _ (by linarith)) s hs hs1 le_rfl

/-- Natural approximation yields exact finite parity heads to every positive
prescribed full squared error, with support allowed to exceed head length. -/
theorem parity_finite_exact_heads_of_naturalApproximation
    (h : BaezDuarte.NaturalApproximation) (budget : ℕ → ℝ)
    (hbudget : ∀ N, 0 < budget N) :
    ∃ support : ℕ → ℕ, ∃ v : ℕ → ThresholdHilbert,
      ∀ N, N ≤ support N ∧ v N ∈ finiteSpace (support N) ∧
        (∀ k, 0 < k → k ≤ N → hilbertSequence (v N) k = hilbertSequence parityAdjointPacket k) ∧
        ‖v N - parityAdjointPacket‖ ^ 2 < budget N := by
  have he := normalizedParityCapture_eq_upper_iff.mpr (normalizedScreenedTwo_norm_eq_one_iff.mp
    (normalizedScreenedTwo_norm_eq_one_iff_naturalApproximation.mpr h))
  exact exists_legal_exact_head_arbitrary_error_budget parityAdjointPacket
    (normalizedParityCapture_eq_upper_iff_adjointParity_mem.mp he) budget hbudget

end RiemannResearch.RH.Pareto.PrimePowerSchur
