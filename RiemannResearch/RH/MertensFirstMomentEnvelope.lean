import RiemannResearch.RH.CanonicalMobiusLogEnvelopeEnergy
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Absolute first moments for squarefree Möbius heads

The middle-window bound and the reciprocal-charge estimate are from
CanonicalMobiusQuantitativeEnergy and CanonicalMobiusLogEnvelopeEnergy.
Keeping the absolute defect before summation allows a single power of
the physical envelope in a scalar pairing with the displacement.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QAnnihilatorTailEscape QSquarefreeResidualTail QSquarefreeDisplacementRigidity
open Pareto RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- An explicit envelope for the absolute error at a physical site. -/
def errorEnvelope (N n : ℕ) (ε : ℝ) : ℝ :=
  if n ≤ N then 0 else min (3 * (N : ℝ))
    (2 + (n : ℝ) * (ε * (2 + Real.log (n : ℝ)) +
      5 * (ε * (1 + Real.log (1 / ε)))))

theorem abs_defect_le_errorEnvelope (N n : ℕ) (hN : 0 < N) (ε : ℝ)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ ε * y) :
    |qSequence (defect N) n| ≤ errorEnvelope N n ε := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp [errorEnvelope]
  have hd : qSequence (defect N) n = 1 - Pareto.canonicalMobiusHead N n := by
    change qSequenceLinear (qOne - QMobiusExactHead.exactHead N) n = _
    rw [map_sub]
    change qSequence qOne n - qSequence (QMobiusExactHead.exactHead N) n = _
    rw [QMobiusExactHead.exactHead_sequence]
    simp [qOneSequence, hn.ne']
  rw [hd, errorEnvelope]
  split_ifs with hnN
  · simp [Pareto.canonicalMobiusHead_exact N n hn hnN]
  have hD : |1 - Pareto.canonicalMobiusHead N n| ≤ 1 + |Pareto.canonicalMobiusHead N n| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_one] using
      abs_add_le (1 : ℝ) (-Pareto.canonicalMobiusHead N n)
  refine le_min ?_ ?_
  · have hm := Pareto.canonicalMobiusHead_abs_le_two_mul N hN n
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hnM (t : ℕ) (ht : N ≤ t) :
      |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ) := by
    have hi := M_nat_difference 0 t (Nat.zero_le t)
    have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
      ext d; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    have hz : M (0 : ℝ) = 0 := by
      have hz' : Finset.Iic (0 : ℕ) = {0} := by ext n; simp
      simp [M, hz']
    rw [hset, Nat.cast_zero, hz, sub_zero] at hi
    rw [← hi]
    exact hM _ (by exact_mod_cast ht)
  have hm := (Pareto.canonicalMobius_energy_of_uniform_mertens_log N hN ε
    hε hεone hsmall hM).1
  have hw := Pareto.canonicalMobiusHead_harmonic_window_bound N n n ε _
    hε.le ((abs_nonneg _).trans hm) (by omega)
    (by simpa using (Nat.mul_le_mul_left n (show 1 ≤ N by omega))) hnM hm
  have hH := harmonic_le_one_add_log n
  have hl : ε * ((harmonic n : ℝ) + 1) ≤ ε * (2 + Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add_right hl (5 * (ε * (1 + Real.log (1 / ε))))) (Nat.cast_nonneg n)
  linarith

/-- The cutoff pairing annihilates the mean of every orthogonal difference
of a reciprocally smoothed vector and a vector with the given moment. -/
theorem annihilator_mean_zero_of_summable_mertens_first_moment (v z : QHilbert)
    (horth : QShiftedReciprocal.B v - z ∈ ZetaTwoOptimizerStage.closureᗮ)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop, 0 < ε j ∧ ε j ≤ 1 ∧
      ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y → |M y| ≤ ε j * y)
    (G : ℕ → ℝ) (hG : Summable G)
    (hmajor : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      (positiveQWeight n * errorEnvelope (q j) n (ε j)) *
        (1 + |qSequence z n|) ≤ G n) : inner ℝ qOne (QShiftedReciprocal.B v - z) = 0 := by
  obtain ⟨A, hA⟩ := B_physical_bounded v
  have hA0 := (abs_nonneg _).trans (hA 0)
  have hw (n : ℕ) : |qSequence (B v - z) n| ≤ (A + 1) * (1 + |qSequence z n|) := by
    have he : qSequence (B v - z) n = qSequence (B v) n - qSequence z n := by
      change qSequenceLinear (B v - z) n = _
      rw [map_sub]
      rfl
    rw [he]
    have ht : |qSequence (B v) n - qSequence z n| ≤
        |qSequence (B v) n| + |qSequence z n| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (qSequence (B v) n) (-qSequence z n)
    nlinarith [hA n, mul_nonneg hA0 (abs_nonneg (qSequence z n))]
  let F (j n : ℕ) := positiveQWeight n * qSequence (defect (q j)) n * qSequence (B v - z) n
  have hsum : Tendsto (fun j => ∑' n, F j n) atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (hG.mul_left (A + 1))
    · intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [hq.eventually (eventually_ge_atTop n), hε, hM,
        hq.eventually (eventually_ge_atTop (1 : ℕ))] with j hj hjε hjM hj1
      have hd := abs_defect_le_errorEnvelope (q j) n (by omega) (ε j)
        hjε.1 hjε.2.1 hjε.2.2 hjM
      rw [errorEnvelope, if_pos hj] at hd
      have hz := abs_nonpos_iff.mp hd
      simp [F, hz]
    · filter_upwards [hmajor, hε, hM, hq.eventually (eventually_ge_atTop (1 : ℕ))]
        with j hj hjε hjM hj1 n
      have hd := abs_defect_le_errorEnvelope (q j) n (by omega) (ε j)
        hjε.1 hjε.2.1 hjε.2.2 hjM
      have hWE := mul_le_mul_of_nonneg_left hd (positiveQWeight_nonneg n)
      have hWE0 := (mul_nonneg (positiveQWeight_nonneg n) (abs_nonneg _)).trans hWE
      change ‖positiveQWeight n * qSequence (defect (q j)) n * qSequence (B v - z) n‖ ≤ (A + 1) * G n
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n)]
      calc
        _ ≤ (positiveQWeight n * errorEnvelope (q j) n (ε j)) *
              ((A + 1) * (1 + |qSequence z n|)) :=
          mul_le_mul hWE (hw n) (abs_nonneg _) hWE0
        _ = (A + 1) * ((positiveQWeight n * errorEnvelope (q j) n (ε j)) *
              (1 + |qSequence z n|)) := by ring
        _ ≤ (A + 1) * G n := mul_le_mul_of_nonneg_left (hj n) (by linarith)
  have hevent : (fun j => ∑' n, F j n) =ᶠ[atTop]
      (fun _ : ℕ => inner ℝ qOne (B v - z)) := by
    filter_upwards [hlegal] with j hj
    change (∑' n, positiveQWeight n * qSequence (defect (q j)) n * qSequence (B v - z) n) = _
    rw [← qInner_weighted, defect, inner_sub_left,
      Submodule.inner_right_of_mem_orthogonal (squarefree_exactHead_mem_closure (q j) hj)
        horth, sub_zero]
  have hz : inner ℝ qOne (B v - z) = 0 := by
    simpa using tendsto_nhds_unique tendsto_const_nhds (hsum.congr' hevent)
  exact hz

/-- Convergence of a scalar absolute first moment along legal exact heads
implies RH. The weights in the hypothesis depend only on the arithmetic
Mertens envelope and on the actual physical displacement. -/
theorem residual_zero_of_summable_mertens_first_moment
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop, 0 < ε j ∧ ε j ≤ 1 ∧
      ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y → |M y| ≤ ε j * y)
    (G : ℕ → ℝ) (hG : Summable G)
    (hmajor : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      (positiveQWeight n * errorEnvelope (q j) n (ε j)) *
        (1 + |qSequence displacement n|) ≤ G n) : limitingResidual = 0 :=
  residual_eq_zero_of_witness_mean_zero
    (annihilator_mean_zero_of_summable_mertens_first_moment pResidual displacement witness_mem_orthogonal
      q hq ε hlegal hε hM G hG hmajor)

/-- A vanishing squarefree projection residual gives Mathlib's RH. -/
theorem rh_of_zero_projection_residual (hr : limitingResidual = 0) : RiemannHypothesis := by
  have hmem : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hmem)

/-- RH follows from the summable envelope along cofinal legal heads. -/
theorem riemannHypothesis_of_summable_mertens_first_moment
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop, 0 < ε j ∧ ε j ≤ 1 ∧
      ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y → |M y| ≤ ε j * y)
    (G : ℕ → ℝ) (hG : Summable G)
    (hmajor : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      (positiveQWeight n * errorEnvelope (q j) n (ε j)) *
        (1 + |qSequence displacement n|) ≤ G n) : RiemannHypothesis :=
  rh_of_zero_projection_residual
    (residual_zero_of_summable_mertens_first_moment q hq ε hlegal hε hM G hG hmajor)

end RiemannResearch.RH.QMertensFirstMoment
