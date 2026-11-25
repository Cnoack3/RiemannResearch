import RiemannResearch.RH.CenteredMeanDigammaSection
import RiemannResearch.RH.CenteredMeanQuotientTail
import RiemannResearch.RH.MixedConductorGramZeroFree
import RiemannResearch.RH.ParetoResidualShell
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.RH.RamanujanUnitMean
import RiemannResearch.RH.ThresholdHilbertAdjoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.OrderClosed

/-!
# Finite Gram tests for the centered quotient loss tail

Each finite Gram solve is tested on a finite interval of physical sites.
First fix that interval and pass to the strong section limit, then exhaust
the physical tail. The solve cutoff can depend on both endpoints.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary

/-- The Pareto-weighted squared error of one finite Gram section on the
physical sites `N + 1` through `N + H`. -/
def finiteSectionShell (B N H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H, paretoWeight (j + N) *
    (sectionCoordinate (B + 1) (j + N + 1) - 1) ^ 2

/-- One inverse Gram solve gives the whole shell. Multiplying by the positive
mean mass squared clears every coordinate denominator exactly. -/
theorem finiteSectionShell_one_solve (B N H : ℕ) :
    let c := (jumpGram (B + 1))⁻¹.mulVec (meanVector (B + 1))
    let m := dotProduct (meanVector (B + 1)) c
    m ^ 2 * finiteSectionShell B N H =
      ∑ j ∈ Finset.range H, paretoWeight (j + N) *
        (dotProduct (siteVector (B + 1) (j + N + 1)) c - m) ^ 2 := by
  let c := (jumpGram (B + 1))⁻¹.mulVec (meanVector (B + 1))
  let m := dotProduct (meanVector (B + 1)) c
  have hm : 0 < m := by
    have he : m = packetMass (B + 1) := by
      dsimp only [m, c]
      rw [jumpGram_eq]
      exact (packetMass_eq_inverseGram (B + 1)).symm
    rw [he]
    exact packetMass_pos (B + 1) (Nat.succ_pos B)
  change m ^ 2 * finiteSectionShell B N H = _
  rw [finiteSectionShell, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change m ^ 2 * (paretoWeight (j + N) *
    (dotProduct (siteVector (B + 1) (j + N + 1)) c / m - 1) ^ 2) =
    paretoWeight (j + N) * (dotProduct (siteVector (B + 1) (j + N + 1)) c - m) ^ 2
  field_simp [hm.ne']
  <;> ring

private theorem finiteSectionShell_eq_pairing (B N H : ℕ) :
    finiteSectionShell B N H = hilbertShellPairing (packetUnitMean B - hilbertOne)
      (packetUnitMean B - hilbertOne) N H := by
  rw [hilbertShellPairing_weighted]
  simp only [finiteSectionShell, sectionCoordinate_eq, positiveWeight_succ, hilbertSequence_sub,
    Pi.sub_apply, hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero, if_false, pow_two]

/-- At every finite Gram stage the complete variance splits exactly into its
initial head, the tested shell, and the omitted infinite tail. -/
theorem finiteSectionShell_variance_partition (B N H : ℕ) :
    finiteSectionShell B 0 N + finiteSectionShell B N H +
      ‖hilbertTailShift (packetUnitMean B - hilbertOne) (N + H)‖ ^ 2 =
        (1 - packetMass (B + 1)) / packetMass (B + 1) := by
  let f := packetUnitMean B - hilbertOne
  have hhead := hilbert_head_tail_pairing f f N
  have hshell := hilbert_tail_shell_pairing f f N H
  simp only [real_inner_self_eq_norm_sq] at hhead hshell
  rw [finiteSectionShell_eq_pairing, finiteSectionShell_eq_pairing, ← packetUnitMean_variance B]
  change hilbertShellPairing f f 0 N + hilbertShellPairing f f N H +
    ‖hilbertTailShift f (N + H)‖ ^ 2 = ‖f‖ ^ 2
  linarith only [hhead, hshell]

/-- At fixed physical endpoints the finite Gram shell tends to the
corresponding weighted squared coordinates of the actual snake defect. -/
theorem finiteSectionShell_tendsto (N H : ℕ) :
    Tendsto (fun B => finiteSectionShell B N H) atTop
      (𝓝 (∑ j ∈ Finset.range H, (defect.val (j + N)) ^ 2)) := by
  unfold finiteSectionShell
  apply tendsto_finsetSum
  intro j hj
  have he := hilbertSequence_weighted_square defect.val (j + N)
  change positiveWeight (j + N + 1) *
    (hilbertSequence (normalizedScreenedTwo - hilbertOne) (j + N + 1)) ^ 2 = _ at he
  simp only [positiveWeight_succ, hilbertSequence_sub, Pi.sub_apply,
    hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero, if_false] at he
  rw [← he]
  exact (((sectionCoordinate_tendsto (j + N + 1)).sub_const 1).pow 2).const_mul _

/-- One common bound on arbitrarily late solves at each fixed shell controls
the full limiting tail. No single solve has to control all shell lengths. -/
theorem scaled_lossTail_le_of_cofinal_finiteSectionShell (N : ℕ) (s C : ℝ)
    (h : ∀ H : ℕ, ∃ᶠ B : ℕ in atTop, s * finiteSectionShell B N H ≤ C) :
    s * coordinateLossTail N ≤ C / (1 + ‖defect‖ ^ 2) := by
  have ht :=
    (hilbert_coordinate_square_summable (hilbertTailShift defect.val N)).hasSum.tendsto_sum_nat
  rw [← hilbert_norm_sq] at ht
  have hs : s * ‖hilbertTailShift defect.val N‖ ^ 2 ≤ C :=
    le_of_tendsto (ht.const_mul s) (Eventually.of_forall (fun H =>
      le_of_tendsto_of_frequently ((finiteSectionShell_tendsto N H).const_mul s) (h H)))
  rw [coordinateLossTail_eq, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hs (by positivity)

/-- The centered unit vanishes exactly when a cofinal sequence of physical
cutoffs admits one common scaled bound for its finite digamma Gram shells. -/
theorem boundary_zero_iff_cofinal_finiteSectionShell :
    boundary = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      ∀ H : ℕ, ∃ᶠ B : ℕ in atTop, (N : ℝ) * finiteSectionShell B N H ≤ C := by
  constructor
  · intro hb
    have hd : defect = 0 := Subtype.ext (sub_eq_zero.mpr (boundary_eq_zero_iff_screened.mp hb))
    refine ⟨1, (Eventually.of_forall fun N H => ?_).frequently⟩
    have ht := (finiteSectionShell_tendsto N H).const_mul (N : ℝ)
    have hz : (N : ℝ) * (∑ j ∈ Finset.range H, (defect.val (j + N)) ^ 2) = 0 := by
      simp [hd]
    rw [hz] at ht
    exact ((ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).frequently
  · rintro ⟨C, hC⟩
    exact boundary_zero_iff_frequently_bounded_coordinateLossTail.mpr
      ⟨C / (1 + ‖defect‖ ^ 2), hC.mono fun N h =>
        scaled_lossTail_le_of_cofinal_finiteSectionShell N N C h⟩

open RiemannResearch.Analysis in
/-- A positive stretched scale is supplied by the Möbius energy bound.
Only a bound on actual finite digamma solves remains in this RH reduction. -/
theorem exists_riemannHypothesis_of_cofinal_stretched_finiteSectionShell :
    ∃ b : ℝ, 0 < b ∧ ∀ C : ℝ, (∃ᶠ N : ℕ in atTop, ∀ H : ℕ, ∃ᶠ B : ℕ in atTop,
      (N : ℝ) * Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) *
        finiteSectionShell B N H ≤ C) → RiemannHypothesis := by
  obtain ⟨b, hb, hRH⟩ := exists_riemannHypothesis_of_stretched_coordinateLossTail
  refine ⟨b, hb, fun C h => hRH (C / (1 + ‖defect‖ ^ 2)) ?_⟩
  exact h.mono (fun N hN => scaled_lossTail_le_of_cofinal_finiteSectionShell N _ C hN)

/-- The full infinite tail of a finite Gram section is computable from the
mass of the solve and only its first `N` physical coordinates. -/
def finiteSectionTailCost (B N : ℕ) : ℝ :=
  (1 - packetMass (B + 1)) / packetMass (B + 1) - finiteSectionShell B 0 N

theorem finiteSectionTailCost_eq (B N : ℕ) :
    finiteSectionTailCost B N = ‖hilbertTailShift (packetUnitMean B - hilbertOne) N‖ ^ 2 := by
  have h := finiteSectionShell_variance_partition B 0 N
  have hz : finiteSectionShell B 0 0 = 0 := by simp [finiteSectionShell]
  rw [hz, zero_add, Nat.zero_add] at h
  unfold finiteSectionTailCost
  linarith only [h]

/-- At each fixed physical cutoff, the complete finite-solve tail costs tend
to the complete centered-boundary tail energy. -/
theorem finiteSectionTailCost_tendsto (N : ℕ) :
    Tendsto (fun B => finiteSectionTailCost B N) atTop
      (𝓝 (‖hilbertTailShift defect.val N‖ ^ 2)) := by
  have hv := ((packetUnitMean_tendsto.sub_const hilbertOne).norm).pow 2
  rw [packetUnitMeanLimit_eq_screened] at hv
  change Tendsto (fun B => ‖packetUnitMean B - hilbertOne‖ ^ 2) atTop
    (𝓝 (‖defect.val‖ ^ 2)) at hv
  rw [hilbertTailShift_norm_sq]
  simpa only [finiteSectionTailCost, ← packetUnitMean_variance, Nat.add_zero] using
    hv.sub (finiteSectionShell_tendsto 0 N)

private theorem scaled_lossTail_le_of_cofinal_finiteSectionTailCost (N : ℕ) (s C : ℝ)
    (h : ∃ᶠ B : ℕ in atTop, s * finiteSectionTailCost B N ≤ C) :
    s * coordinateLossTail N ≤ C / (1 + ‖defect‖ ^ 2) := by
  rw [coordinateLossTail_eq, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (le_of_tendsto_of_frequently ((finiteSectionTailCost_tendsto N).const_mul s) h) (by positivity)

/-- A two-cutoff arithmetic criterion. Each cost involves one finite Gram
solve and one finite head sum, even though it measures the whole omitted tail. -/
theorem boundary_zero_iff_cofinal_finiteSectionTailCost :
    boundary = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      ∃ᶠ B : ℕ in atTop, (N : ℝ) * finiteSectionTailCost B N ≤ C := by
  constructor
  · intro hb
    have hd : defect = 0 := Subtype.ext (sub_eq_zero.mpr (boundary_eq_zero_iff_screened.mp hb))
    refine ⟨1, (Eventually.of_forall fun N => ?_).frequently⟩
    have hz : hilbertTailShift defect.val N = 0 := by
      rw [hd]
      ext j
      rfl
    have ht := (finiteSectionTailCost_tendsto N).const_mul (N : ℝ)
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at ht
    exact ((ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).frequently
  · rintro ⟨C, hC⟩
    exact boundary_zero_iff_frequently_bounded_coordinateLossTail.mpr
      ⟨C / (1 + ‖defect‖ ^ 2), hC.mono fun N =>
        scaled_lossTail_le_of_cofinal_finiteSectionTailCost N N C⟩

open RiemannResearch.Analysis in
/-- The stretched-exponential improvement also has a finite two-cutoff test. -/
theorem exists_riemannHypothesis_of_cofinal_stretched_finiteSectionTailCost :
    ∃ b : ℝ, 0 < b ∧ ∀ C : ℝ, (∃ᶠ N : ℕ in atTop, ∃ᶠ B : ℕ in atTop,
      (N : ℝ) * Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) *
        finiteSectionTailCost B N ≤ C) → RiemannHypothesis := by
  obtain ⟨b, hb, hRH⟩ := exists_riemannHypothesis_of_stretched_coordinateLossTail
  refine ⟨b, hb, fun C h => hRH (C / (1 + ‖defect‖ ^ 2)) ?_⟩
  exact h.mono (fun N => scaled_lossTail_le_of_cofinal_finiteSectionTailCost N _ C)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
