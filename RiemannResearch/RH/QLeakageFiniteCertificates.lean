import RiemannResearch.RH.QDensityLeakageSeries
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QSquarefreeRationalUpperBounds
import RiemannResearch.RH.QFullHeadControllability
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FunProp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega


/-!
# Finite rational certificates for cofinal signed leakage

Source: Christian Noack's RH Obligation Triage continuation, 16 November 2026.
The finite tail estimate comes from QFiniteEnergyBounds; the numerical
seven-atom error bound comes from QSquarefreeRationalUpperBounds. The present
assembly transfers those results to the full-residue leakage consumer.

For rational c on conductors 2,...,m+1, set
  e_c(n) = 1 - sum_i c_i * ((n mod (i+2))/(i+2)),
  A_c = 1 + sum_i |c_i|,
  C(m,K,c) = sum_{n=1}^K e_c(n)^2/n^2 + A_c^2/K.
Every term and comparison defining C is rational. All signed contributions
are retained inside each square; the final term bounds the entire tail.
For K > 0, the actual complete Q-error squared is at most C. For fixed
real coefficients, C tends to zeta(2) times the complete Q-error squared.

The requested cofinal leakage estimate is equivalent to:
for every natural j, find m >= j, K > 0 and rational c with
C(m,K,c) < 1/(j+1)^2. This is an exact conditional research reduction.
The existence of certificates at every precision remains OPEN.
No target-membership, zero-residual, or RH premise occurs in this criterion.

The seven-atom benchmark unconditionally improves the leakage coefficient
from 1/2 to 19/100. Its strict error margin also yields the eventual estimate
at epsilon = 19/100. No arbitrarily small positive coefficient is proved.
The full dictionary allows all conductors; squarefree-only density is not
inferred from this fixed squarefree benchmark.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QLeakageFiniteCertificates
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QFullResidueProjection QCovarianceInverse QDensityLeakageSeries QFiniteEnergyBounds

def synthesis (m : ℕ) (c : Fin m → ℝ) : QHilbert :=
  qSynthesis (conductor m) c

def errorVector (m : ℕ) (c : Fin m → ℝ) : QHilbert := qOne - synthesis m c

def physicalError (m : ℕ) (c : Fin m → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ i : Fin m, c i * residueFraction (i.val + 2) n

def amplitude (m : ℕ) (c : Fin m → ℝ) : ℝ := 1 + ∑ i, |c i|

def budget (m : ℕ) (c : Fin m → ℝ) (K : ℕ) : ℝ :=
  (∑ n ∈ Finset.range K, physicalError m c (n + 1) ^ 2 / (n + 1 : ℝ) ^ 2) +
    amplitude m c ^ 2 / K

def rationalBudget (m K : ℕ) (c : Fin m → ℚ) : ℚ :=
  (∑ n ∈ Finset.range K,
    (1 - ∑ i : Fin m, c i * ((n + 1) % (i.val + 2) : ℕ) / (i.val + 2 : ℚ)) ^ 2 /
      (n + 1 : ℚ) ^ 2) + (1 + ∑ i, |c i|) ^ 2 / K

theorem synthesis_mem_closure (m : ℕ) (c : Fin m → ℝ) :
    synthesis m c ∈ closure := by
  unfold synthesis qSynthesis
  apply closure.sum_mem
  intro i hi
  apply closure.smul_mem
  exact legalSpan.le_topologicalClosure
    (QFullHeadControllability.qResidue_mem_legalSpan _ (by simp [conductor]))

theorem errorVector_sequence (m : ℕ) (c : Fin m → ℝ) (n : ℕ) (hn : n ≠ 0) :
    qSequence (errorVector m c) n = physicalError m c n := by
  change qSequenceLinear (qOne - ∑ i : Fin m, c i • qResidue (conductor m i)) n = _
  simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp [qSequenceLinear, qSequence_qOne, qOneSequence, hn,
    qSequence_qResidue, physicalError, conductor]

theorem errorVector_sequence_succ (m : ℕ) (c : Fin m → ℝ) (n : ℕ) :
    qSequence (errorVector m c) (n + 1) = physicalError m c (n + 1) :=
  errorVector_sequence m c (n + 1) (by omega)

theorem amplitude_nonneg (m : ℕ) (c : Fin m → ℝ) : 0 ≤ amplitude m c := by
  unfold amplitude
  positivity

theorem physicalError_abs_le (m : ℕ) (c : Fin m → ℝ) (n : ℕ) :
    |physicalError m c n| ≤ amplitude m c := by
  have hfrac (i : Fin m) : |residueFraction (i.val + 2) n| ≤ 1 := by
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity : (0 : ℝ) < (i.val + 2 : ℕ))).mpr
    exact_mod_cast (Nat.mod_lt n (by omega : 0 < i.val + 2)).le
  calc
    _ ≤ 1 + |∑ i : Fin m, c i * residueFraction (i.val + 2) n| := by
      simpa [physicalError, Real.norm_eq_abs] using norm_sub_le (1 : ℝ)
        (∑ i : Fin m, c i * residueFraction (i.val + 2) n)
    _ ≤ 1 + ∑ i : Fin m, |c i * residueFraction (i.val + 2) n| :=
      add_le_add (le_refl 1) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ amplitude m c := by
      unfold amplitude
      apply add_le_add (le_refl 1)
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hfrac i) (abs_nonneg _)).trans_eq (mul_one _)

theorem errorVector_abs_le (m : ℕ) (c : Fin m → ℝ) (n : ℕ) :
    |qSequence (errorVector m c) n| ≤ amplitude m c := by
  by_cases hn : n = 0
  · simp [hn, amplitude_nonneg]
  · rw [errorVector_sequence m c n hn]
    exact physicalError_abs_le m c n

theorem budget_nonneg (m : ℕ) (c : Fin m → ℝ) (K : ℕ) : 0 ≤ budget m c K := by
  unfold budget
  positivity

theorem error_norm_sq_le_budget (m : ℕ) (c : Fin m → ℝ) (K : ℕ) (hK : 0 < K) :
    ‖errorVector m c‖ ^ 2 ≤ budget m c K := by
  have h := norm_sq_le_head_tail (errorVector m c) K hK
    (amplitude m c) (amplitude_nonneg m c) (errorVector_abs_le m c)
  simp_rw [errorVector_sequence_succ] at h
  have hz : 1 / zetaTwo ≤ 1 := by linarith [inverse_zetaTwo_rational_bounds.2]
  exact h.trans (by
    change (1 / zetaTwo) * budget m c K ≤ budget m c K
    simpa using mul_le_mul_of_nonneg_right hz (budget_nonneg m c K))

theorem rationalBudget_cast (m K : ℕ) (c : Fin m → ℚ) :
    (rationalBudget m K c : ℝ) = budget m (fun i => (c i : ℝ)) K := by
  simp [rationalBudget, budget, physicalError, amplitude, residueFraction,
    mul_div_assoc]

theorem budget_continuous (m K : ℕ) :
    Continuous (fun c : Fin m → ℝ => budget m c K) := by
  unfold budget physicalError amplitude
  fun_prop

theorem error_energy_series (m : ℕ) (c : Fin m → ℝ) :
    Summable (fun n : ℕ => physicalError m c (n+1)^2/(n+1 : ℝ)^2) := by
  have h := SquarefreeRadicalDifference.qNormalized_square_summable (errorVector m c)
  simp only [div_pow] at h
  have hs := (summable_nat_add_iff 1).mpr h
  simpa only [errorVector_sequence_succ, Nat.cast_add, Nat.cast_one] using hs

theorem error_energy_tsum (m : ℕ) (c : Fin m → ℝ) :
    (∑' n : ℕ, physicalError m c (n+1)^2/(n+1 : ℝ)^2) =
      zetaTwo * ‖errorVector m c‖ ^ 2 := by
  have h := norm_sq_unweighted (errorVector m c)
  simp_rw [errorVector_sequence_succ] at h
  field_simp [zetaTwo_pos.ne'] at h
  nlinarith [h]

theorem budget_tendsto (m : ℕ) (c : Fin m → ℝ) :
    Tendsto (budget m c) atTop (𝓝 (zetaTwo * ‖errorVector m c‖ ^ 2)) := by
  have hs := (error_energy_series m c).hasSum.tendsto_sum_nat
  have hi : Tendsto (fun K : ℕ => (K : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun K : ℕ => amplitude m c ^ 2 / (K : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := amplitude m c ^ 2)).mul hi
  change Tendsto (fun K => (∑ n ∈ Finset.range K,
    physicalError m c (n + 1)^2 / (n + 1 : ℝ)^2) + amplitude m c ^ 2 / K) _ _
  simpa only [error_energy_tsum, add_zero] using hs.add ht

theorem exists_rational_budget_lt_of_mem (h : qOne ∈ closure)
    (ε : ℝ) (hε : 0 < ε) (J : ℕ) :
    ∃ m K : ℕ, ∃ c : Fin m → ℚ,
      J ≤ m ∧ 0 < K ∧ (rationalBudget m K c : ℝ) < ε ^ 2 := by
  have he : Tendsto (fun m => errorVector m (coefficients m))
      atTop (𝓝 (0 : QHilbert)) := by
    simpa only [errorVector, synthesis, candidate, sub_self] using
      (tendsto_const_nhds (x := qOne)).sub (candidate_tendsto_qOne h)
  have hl : Tendsto (fun m => zetaTwo * ‖errorVector m (coefficients m)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := zetaTwo)).mul (he.norm.pow 2)
  have hm := hl.eventually (gt_mem_nhds (show 0 < ε ^ 2 / 2 by positivity))
  obtain ⟨m, hmJ, hmv⟩ := (eventually_ge_atTop J |>.and hm).exists
  have hlim := (budget_tendsto m (coefficients m)).eventually
    (gt_mem_nhds (show zetaTwo * ‖errorVector m (coefficients m)‖ ^ 2 < ε ^ 2 by
      nlinarith [sq_pos_of_pos hε]))
  obtain ⟨K, hK, hval⟩ := (eventually_ge_atTop 1 |>.and hlim).exists
  have hd : DenseRange (fun c : Fin m → ℚ => fun i => (c i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨c, hc⟩ := hd.exists_mem_open
    (isOpen_lt (budget_continuous m K) continuous_const)
    ⟨coefficients m, hval⟩
  refine ⟨m, K, c, hmJ, by omega, ?_⟩
  rw [rationalBudget_cast]
  exact hc

theorem partialLeakage_le_of_budget (m K : ℕ) (c : Fin m → ℚ)
    (hK : 0 < K) (δ : ℝ) (hδ : 0 ≤ δ)
    (hc : (rationalBudget m K c : ℝ) ≤ δ ^ 2) (N : ℕ) :
    ‖partialLeakage N‖ ≤ δ * harmonicMass N + centeredBudget := by
  have he := (error_norm_sq_le_budget m (fun i => (c i : ℝ)) K hK)
  rw [← rationalBudget_cast] at he
  have hn : ‖errorVector m (fun i => (c i : ℝ))‖ ≤ δ := by
    nlinarith [norm_nonneg (errorVector m (fun i => (c i : ℝ)))]
  have h := partialLeakage_norm_le_legal_certificate N
    (synthesis m (fun i => (c i : ℝ))) (synthesis_mem_closure _ _)
  change ‖partialLeakage N‖ ≤ harmonicMass N *
    ‖errorVector m (fun i => (c i : ℝ))‖ + centeredBudget at h
  have hm := mul_le_mul_of_nonneg_left hn (harmonicMass_nonneg N)
  nlinarith

theorem cofinal_subharmonic_iff_rational_certificates :
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ ε * harmonicMass N) ↔
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ m K : ℕ, ∃ c : Fin m → ℚ,
        J ≤ m ∧ 0 < K ∧ (rationalBudget m K c : ℝ) < ε ^ 2) := by
  constructor
  · intro h
    exact exists_rational_budget_lt_of_mem (cofinal_subharmonic_partialLeakage_iff.mp h)
  · intro h ε hε J
    obtain ⟨m, K, c, hm, hK, hc⟩ := h (ε / 2) (by positivity) 0
    have ht := harmonicMass_tendsto_atTop.eventually
      (eventually_ge_atTop (centeredBudget / (ε / 2)))
    obtain ⟨N, hNJ, hN⟩ := (eventually_ge_atTop J |>.and ht).exists
    refine ⟨N, hNJ, ?_⟩
    have hp := partialLeakage_le_of_budget m K c hK (ε / 2) (by positivity) hc.le N
    have hmass := (div_le_iff₀ (show 0 < ε / 2 by positivity)).mp hN
    nlinarith


/-- A countable criterion whose individual witnesses use rational arithmetic only. -/
theorem cofinal_subharmonic_iff_countable_rational_certificates :
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ ε * harmonicMass N) ↔
    (∀ j : ℕ, ∃ m K : ℕ, ∃ c : Fin m → ℚ,
      j ≤ m ∧ 0 < K ∧ rationalBudget m K c < 1 / (j + 1 : ℚ) ^ 2) := by
  rw [cofinal_subharmonic_iff_rational_certificates]
  constructor
  · intro h j
    obtain ⟨m, K, c, hm, hK, hc⟩ := h (1 / (j + 1 : ℝ)) (by positivity) j
    refine ⟨m, K, c, hm, hK, ?_⟩
    have hc' : (rationalBudget m K c : ℝ) < 1 / (j + 1 : ℝ) ^ 2 := by
      simpa only [one_div_pow] using hc
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_add,
      Rat.cast_natCast] using hc'
  · intro h ε hε J
    obtain ⟨j, hj⟩ := exists_nat_gt (max (J : ℝ) (1 / ε))
    have hjJ : J ≤ j := by
      exact_mod_cast ((le_max_left (J : ℝ) (1 / ε)).trans hj.le)
    have hjε : 1 / ε < (j : ℝ) :=
      (le_max_right (J : ℝ) (1 / ε)).trans_lt hj
    have hjmul := (div_lt_iff₀ hε).mp hjε
    have hslope : 1 / (j + 1 : ℝ) < ε :=
      (div_lt_iff₀ (by positivity : 0 < (j + 1 : ℝ))).mpr (by nlinarith)
    have hsquare : 1 / (j + 1 : ℝ) ^ 2 < ε ^ 2 := by
      rw [← one_div_pow]
      nlinarith [show (0 : ℝ) ≤ 1 / (j + 1 : ℝ) by positivity]
    obtain ⟨m, K, c, hm, hK, hc⟩ := h j
    refine ⟨m, K, c, hjJ.trans hm, hK, ?_⟩
    have hc' : (rationalBudget m K c : ℝ) < 1 / (j + 1 : ℝ) ^ 2 := by
      have hh := (Rat.cast_lt (K := ℝ)).mpr hc
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_add,
        Rat.cast_natCast] using hh
    exact hc'.trans hsquare

/-- Conditional RH consumer with only explicit finite rational certificates as input. -/
theorem riemannHypothesis_of_countable_rational_certificates
    (h : ∀ j : ℕ, ∃ m K : ℕ, ∃ c : Fin m → ℚ,
      j ≤ m ∧ 0 < K ∧ rationalBudget m K c < 1 / (j + 1 : ℚ) ^ 2) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_subharmonic_partialLeakage
    (cofinal_subharmonic_iff_countable_rational_certificates.mpr h)


/-- A certificate with a strict margin supplies an eventual leakage slope. -/
theorem eventually_partialLeakage_le_of_legal_certificate
    (f : QHilbert) (hf : f ∈ closure) (ε : ℝ) (hε : ‖qOne - f‖ < ε) :
    ∀ᶠ N : ℕ in atTop, ‖partialLeakage N‖ ≤ ε * harmonicMass N := by
  filter_upwards [harmonicMass_tendsto_atTop.eventually
    (eventually_ge_atTop (centeredBudget / (ε - ‖qOne - f‖)))] with N hN
  have ht := (div_le_iff₀ (show 0 < ε - ‖qOne - f‖ by linarith)).mp hN
  nlinarith [partialLeakage_norm_le_legal_certificate N f hf]

/-- The repository's seven-atom rational competitor, in the full legal span. -/
def sevenAtom : QHilbert :=
    (985587/1000000 : ℝ) • qResidue 2 +
    (963419/1000000 : ℝ) • qResidue 3 +
    (823721/1000000 : ℝ) • qResidue 5 +
    (-158232/1000000 : ℝ) • qResidue 6 +
    (91952/1000000 : ℝ) • qResidue 10 +
    (138611/1000000 : ℝ) • qResidue 15 +
    (146439/1000000 : ℝ) • qResidue 30

theorem sevenAtom_mem_closure : sevenAtom ∈ closure := by
  unfold sevenAtom
  repeat first
    | apply closure.add_mem
    | apply closure.smul_mem
    | exact legalSpan.le_topologicalClosure
        (QFullHeadControllability.qResidue_mem_legalSpan _ (by norm_num))

theorem sevenAtom_error_lt : ‖qOne - sevenAtom‖ < (19 / 100 : ℝ) := by
  change ‖QSquarefreeRationalUpperBounds.errorVector‖ < _
  nlinarith [QSquarefreeRationalUpperBounds.complete_norm_lt,
    norm_nonneg QSquarefreeRationalUpperBounds.errorVector]

theorem partialLeakage_norm_le_nineteen_hundredths (N : ℕ) :
    ‖partialLeakage N‖ ≤ (19 / 100 : ℝ) * harmonicMass N + centeredBudget := by
  have hp := partialLeakage_norm_le_legal_certificate N sevenAtom sevenAtom_mem_closure
  have hm := mul_le_mul_of_nonneg_left sevenAtom_error_lt.le (harmonicMass_nonneg N)
  nlinarith

/-- The endpoint epsilon = 19/100 is included, using the strict certificate margin. -/
theorem eventually_partialLeakage_norm_le_of_nineteen_hundredths_le
    (ε : ℝ) (hε : 19 / 100 ≤ ε) :
    ∀ᶠ N : ℕ in atTop, ‖partialLeakage N‖ ≤ ε * harmonicMass N :=
  eventually_partialLeakage_le_of_legal_certificate sevenAtom sevenAtom_mem_closure ε
    (sevenAtom_error_lt.trans_le hε)

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.synthesis_mem_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms synthesis_mem_closure

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.errorVector_sequence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms errorVector_sequence

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.errorVector_sequence_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms errorVector_sequence_succ

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.amplitude_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms amplitude_nonneg

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.physicalError_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms physicalError_abs_le

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.errorVector_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms errorVector_abs_le

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.budget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms budget_nonneg

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.error_norm_sq_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms error_norm_sq_le_budget

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.rationalBudget_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rationalBudget_cast

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.budget_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms budget_continuous

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.error_energy_series' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms error_energy_series

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.error_energy_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms error_energy_tsum

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.budget_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms budget_tendsto

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.exists_rational_budget_lt_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_rational_budget_lt_of_mem

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.partialLeakage_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_le_of_budget

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.cofinal_subharmonic_iff_rational_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_subharmonic_iff_rational_certificates

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.cofinal_subharmonic_iff_countable_rational_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_subharmonic_iff_countable_rational_certificates

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.riemannHypothesis_of_countable_rational_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_countable_rational_certificates

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.eventually_partialLeakage_le_of_legal_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_partialLeakage_le_of_legal_certificate

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.sevenAtom_mem_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sevenAtom_mem_closure

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.sevenAtom_error_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sevenAtom_error_lt

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.partialLeakage_norm_le_nineteen_hundredths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_norm_le_nineteen_hundredths

/--
info: 'RiemannResearch.RH.QLeakageFiniteCertificates.eventually_partialLeakage_norm_le_of_nineteen_hundredths_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_partialLeakage_norm_le_of_nineteen_hundredths_le

end RiemannResearch.RH.QLeakageFiniteCertificates
