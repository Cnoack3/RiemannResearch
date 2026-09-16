import RiemannResearch.RH.CoupledResidualCorrections
import RiemannResearch.RH.TwoSeedAnnihilatorCharge
import RiemannResearch.Analysis.ResidualHarmonicGain

/-!
# The exact open logarithmic correction target and its RH consequence

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Sections 1, 6, and 10. The source supports the statements and strategy.
The two named bounds below are propositions, not axioms or proof providers.
We prove their equivalence and their implication to mathlib's RH.
No lower bound for the actual arithmetic gain is asserted unconditionally.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket
open RiemannResearch.Analysis.CorrelationCorrection

theorem gain_nonneg (M : ℕ) : 0 ≤ gain M :=
  sub_nonneg.mpr (distance_antitone (by omega : M ≤ 2*M))

/-- Exact feasibility equivalence, including the zero-gain obstruction. -/
theorem normalized_cost_iff_gain (M : ℕ) (B : ℝ) (hB : 0 < B) :
    (∃ w : ThresholdHilbert, w ∈ budgetHilbert (2*M) ∧
      w ∈ (budgetHilbert M)ᗮ ∧ inner ℝ (error M) w = distance M ∧
      ‖w‖^2 ≤ B*distance M) ↔ distance M ≤ B*gain M := by
  constructor
  · rintro ⟨w, hw, _, hc, hn⟩
    have hcs := nested_correlation_sq_le (budgetHilbert M) (budgetHilbert (2*M))
      (budgetHilbert_mono (by omega : M ≤ 2*M)) hilbertOne w hw
    change (inner ℝ (error M) w)^2 ≤ gain M * ‖w‖^2 at hcs
    rw [hc] at hcs
    have hb := mul_le_mul_of_nonneg_left hn (gain_nonneg M)
    apply le_of_mul_le_mul_left ?_ (distance_pos M)
    nlinarith
  · intro h
    have hg : 0 < gain M := by
      have hd := distance_pos M
      by_contra hg
      have hn := mul_nonpos_of_nonneg_of_nonpos hB.le (le_of_not_gt hg)
      linarith
    obtain ⟨w, hw, ho, hc, hn⟩ := reconstruction_optimum M hg
    refine ⟨w, hw, ho, hc, ?_⟩
    rw [hn]
    apply (div_le_iff₀ hg).mpr
    have hh := mul_le_mul_of_nonneg_right h (distance_pos M).le
    nlinarith

/-- OPEN mathematical estimate: normalized legal corrections at logarithmic cost. -/
def LogarithmicCostBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M →
    ∃ w : ThresholdHilbert, w ∈ budgetHilbert (2*M) ∧
      w ∈ (budgetHilbert M)ᗮ ∧ inner ℝ (error M) w = distance M ∧
      ‖w‖^2 ≤ (C*Real.log (2*(M:ℝ)))*distance M

/-- OPEN, equivalent signed arithmetic gain bound on the actual residual. -/
def LogarithmicGainBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 1 ≤ M →
    distance M ≤ (C*Real.log (2*(M:ℝ)))*gain M

theorem logarithmicCostBound_iff_gainBound :
    LogarithmicCostBound ↔ LogarithmicGainBound := by
  constructor
  · rintro ⟨C, hC, M₀, h⟩
    refine ⟨C, hC, M₀, fun M hM hpos => ?_⟩
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hpos
    exact (normalized_cost_iff_gain M _
      (mul_pos hC (Real.log_pos (by linarith)))).mp (h M hM hpos)
  · rintro ⟨C, hC, M₀, h⟩
    refine ⟨C, hC, M₀, fun M hM hpos => ?_⟩
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hpos
    exact (normalized_cost_iff_gain M _
      (mul_pos hC (Real.log_pos (by linarith)))).mpr (h M hM hpos)

theorem budget_le_twoSeedClosure (M : ℕ) :
    budgetHilbert M ≤ hilbertLegalClosure {2,3} := by
  rw [← canonicalHilbertFamily_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨hm, _, hs⟩ := (mem_canonicalIndices M i.val).mp i.property
  unfold canonicalHilbertFamily
  apply generator_mem_twoSeedClosure
  rcases hs with h | ⟨h, _⟩
  · exact Or.inr h
  · exact Or.inl h

theorem riemannHypothesis_of_distance_convergence (J : ℕ → ℕ)
    (h : Tendsto (fun n => distance (J n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hn : Tendsto (fun n => ‖error (J n)‖) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa [Function.comp_def, distance, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hs
  have hp : Tendsto (fun n => fit (J n)) atTop (𝓝 hilbertOne) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa [error, norm_sub_rev] using hn
  have hc : IsClosed (hilbertLegalClosure {2,3} : Set ThresholdHilbert) :=
    (hilbertLegalSubspace {2,3}).isClosed_topologicalClosure
  apply riemannHypothesis_of_twoSeed_closure
  apply hc.mem_of_tendsto hp
  exact Filter.Eventually.of_forall (fun n =>
    budget_le_twoSeedClosure (J n) ((budgetHilbert (J n)).starProjection_apply_mem _))

/-- A conditional research reduction; the arithmetic loss is the only open input. -/
theorem riemannHypothesis_of_dyadic_loss (J : ℕ) (a : ℝ) (ha : 0 < a)
    (h : ∀ n : ℕ, a/((n:ℝ)+1)*distance (2^(J+n)) ≤ gain (2^(J+n))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_distance_convergence (fun n => 2^(J+n))
  apply RiemannResearch.Analysis.ResidualGain.tendsto_zero_of_harmonic_loss
    (a := a) (fun n => (distance_pos _).le) ha
  intro n
  have hh := h n
  have he : 2*2^(J+n) = 2^(J+(n+1)) := by
    rw [show J+(n+1) = (J+n)+1 by omega, pow_succ]
    omega
  simpa only [gain, he] using hh

/-- No RH conclusion is unconditional: this theorem consumes the named open bound. -/
theorem riemannHypothesis_of_logarithmicGainBound (h : LogarithmicGainBound) :
    RiemannHypothesis := by
  obtain ⟨C, hC, J, h⟩ := h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := C*Real.log 2*((J:ℝ)+1)
  have hB : 0 < B := by dsimp [B]; positivity
  apply riemannHypothesis_of_dyadic_loss J (1/B) (one_div_pos.mpr hB)
  intro n
  have lepow (k : ℕ) : k ≤ 2^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 2^k := pow_pos (by omega) k
      omega
  have hJ : J ≤ 2^(J+n) := le_trans (Nat.le_add_right J n) (lepow _)
  have hp : 1 ≤ 2^(J+n) := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hh := h (2^(J+n)) hJ hp
  have hlog : Real.log (2*((2^(J+n):ℕ):ℝ)) =
      ((J:ℝ)+(n:ℝ)+1)*Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat,
      show (2:ℝ)*2^(J+n) = 2^(J+n+1) by rw [pow_succ]; ring, Real.log_pow]
    push_cast
    ring
  have hscale : C*Real.log (2*((2^(J+n):ℕ):ℝ)) ≤ B*((n:ℝ)+1) := by
    rw [hlog]
    have hj : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hc : 0 ≤ C*Real.log 2 := (mul_pos hC hl).le
    dsimp [B]
    nlinarith [mul_nonneg hj hn, mul_nonneg hc (mul_nonneg hj hn)]
  have hd : distance (2^(J+n)) ≤ (B*((n:ℝ)+1))*gain (2^(J+n)) :=
    hh.trans (mul_le_mul_of_nonneg_right hscale (gain_nonneg _))
  have hdiv : distance (2^(J+n))/(B*((n:ℝ)+1)) ≤ gain (2^(J+n)) :=
    (div_le_iff₀ (mul_pos hB (by positivity))).mpr (by simpa [mul_comm] using hd)
  simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc, mul_comm,
    mul_left_comm] using hdiv

theorem riemannHypothesis_of_logarithmicCostBound (h : LogarithmicCostBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_logarithmicGainBound (logarithmicCostBound_iff_gainBound.mp h)

end RiemannResearch.RH.Pareto.CoupledResidual
