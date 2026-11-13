import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import RiemannResearch.Analysis.FiniteAccretiveCollocation
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QDivisorGcdCutoff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Canonical full-conductor CRT collocation in the actual Q space

Source: user-provided CRT_Collocation_and_Zero_Growth_2026-11-06,
Sections 2--4 and 9. Bagchi, Proc. Indian Acad. Sci. Math. Sci. 116
(2006), 137--146, Theorem 1 and its equivalent-weight observation,
https://repository.ias.ac.in/968/1/307.pdf, supplies the RH interpretation
of the full residue family; it does not supply an inverse-system bound.

All inner products and norms retain the complete physical Q tail.
The conditional projection is onto the finite divisor (gcd-cell) span.
The legal collocation solution is not asserted to be the best approximation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTFiniteCollocation
open ZetaTwoHilbert ZetaTwoProbability QPhysicalDifference
open QDivisibilityDensity SquarefreeRadicalDifference
open RiemannResearch.Analysis.FiniteAccretiveCollocation

def trialSpace (L : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (qResidue '' (↑L.divisors : Set ℕ))

def cellSpace (L : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (qDivisor '' (↑L.divisors : Set ℕ))

instance trialSpace_finiteDimensional (L : ℕ) :
    FiniteDimensional ℝ (trialSpace L) :=
  FiniteDimensional.span_of_finite ℝ (L.divisors.finite_toSet.image _)

instance cellSpace_finiteDimensional (L : ℕ) :
    FiniteDimensional ℝ (cellSpace L) :=
  FiniteDimensional.span_of_finite ℝ (L.divisors.finite_toSet.image _)

def conditionalProjection (L : ℕ) : QHilbert →L[ℝ] QHilbert :=
  (cellSpace L).starProjection

def target (L : ℕ) : QHilbert := qOne - qDivisor L

theorem qDivisor_one : qDivisor 1 = qOne := by
  apply qSequence_injective
  funext n
  simp [qSequence_qDivisor, qSequence_qOne, positiveDivisor, qOneSequence]

theorem residue_mem_trial (L d : ℕ) (hL : 0 < L) (hdL : d ∣ L) :
    qResidue d ∈ trialSpace L :=
  Submodule.subset_span ⟨d, Nat.mem_divisors.mpr ⟨hdL, ne_of_gt hL⟩, rfl⟩

theorem divisor_mem_cell (L d : ℕ) (hL : 0 < L) (hdL : d ∣ L) :
    qDivisor d ∈ cellSpace L :=
  Submodule.subset_span ⟨d, Nat.mem_divisors.mpr ⟨hdL, ne_of_gt hL⟩, rfl⟩

theorem qOne_mem_cell (L : ℕ) (hL : 0 < L) : qOne ∈ cellSpace L := by
  rw [← qDivisor_one]
  exact divisor_mem_cell L 1 hL (one_dvd L)

theorem target_mem_cell (L : ℕ) (hL : 0 < L) : target L ∈ cellSpace L :=
  (cellSpace L).sub_mem (qOne_mem_cell L hL) (divisor_mem_cell L L hL (dvd_refl L))

theorem trial_inner_multiples (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : f ∈ trialSpace L) :
    inner ℝ f (qDivisor L) = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, hd, rfl⟩
    exact qResidue_inner_qDivisor_eq_zero d L hL (Nat.dvd_of_mem_divisors hd)
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul c x hx ih => simp [real_inner_smul_left, ih]

theorem difference_residue (d : ℕ) (hd : 2 ≤ d) :
    differenceCLM (qResidue d) = (1 / (d : ℝ)) • qOne - qDivisor d := by
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  · change qSequence (differenceCLM (qResidue d)) n =
      qSequenceLinear ((1 / (d : ℝ)) • qOne - qDivisor d) n
    rw [map_sub, map_smul]
    change qSequence (differenceCLM (qResidue d)) n =
      (1 / (d : ℝ)) * qSequence qOne n - qSequence (qDivisor d) n
    simp only [
      qSequence_differenceCLM, qDifference, qSequence_qResidue,
      qSequence_qOne, qSequence_qDivisor]
    rw [residueFraction_difference d n hd (by omega)]
    simp [qOneSequence, positiveDivisor, hn]

theorem difference_mem_cell (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : f ∈ trialSpace L) : differenceCLM f ∈ cellSpace L := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, hd, rfl⟩
    have hdpos := Nat.pos_of_mem_divisors hd
    by_cases hd1 : d = 1
    · simp [hd1]
    · rw [difference_residue d (by omega)]
      exact (cellSpace L).sub_mem
        ((cellSpace L).smul_mem _ (qOne_mem_cell L hL))
        (divisor_mem_cell L d hL (Nat.dvd_of_mem_divisors hd))
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (cellSpace L).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (cellSpace L).smul_mem c ih

theorem inner_eq_of_divisor_tests (L : ℕ) (f h : QHilbert)
    (hm : ∀ d ∈ L.divisors, inner ℝ f (qDivisor d) = inner ℝ h (qDivisor d))
    (v : QHilbert) (hv : v ∈ cellSpace L) : inner ℝ f v = inner ℝ h v := by
  induction hv using Submodule.span_induction with
  | mem g hg => rcases hg with ⟨d, hd, rfl⟩; exact hm d hd
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul c x hx ih => simp [inner_smul_right, ih]

/-- Unique full divisor-moment matching for any target orthogonal to multiples. -/
theorem existsUnique_divisor_match (L : ℕ) (hL : 2 ≤ L)
    (h : QHilbert) (hh : inner ℝ h (qDivisor L) = 0) :
    ∃! f : trialSpace L, ∀ d ∈ L.divisors,
      inner ℝ (f : QHilbert) (qDivisor d) = inner ℝ h (qDivisor d) := by
  have hLp : 0 < L := by omega
  have hac : ∀ f, inner ℝ f (differenceCLM f) = 0 → f = 0 := by
    intro f hf
    exact eq_zero_of_difference_inner shiftCLM physicalShift_norm_le
      differenceCLM_injective f hf
  obtain ⟨f, hf, hu⟩ := existsUnique_test_match differenceCLM hac (trialSpace L) h
  have hfL := trial_inner_multiples L hLp f f.property
  have hLtest := hf ⟨qResidue L, residue_mem_trial L L hLp (dvd_refl L)⟩
  simp only [difference_residue L hL, inner_sub_right, inner_smul_right,
    hfL, hh, sub_zero] at hLtest
  have hmean : inner ℝ (f : QHilbert) qOne = inner ℝ h qOne :=
    mul_left_cancel₀ (one_div_ne_zero (by positivity : (L : ℝ) ≠ 0)) hLtest
  have hmatch : ∀ d ∈ L.divisors,
      inner ℝ (f : QHilbert) (qDivisor d) = inner ℝ h (qDivisor d) := by
    intro d hd
    by_cases hd1 : d = 1
    · simpa only [hd1, qDivisor_one] using hmean
    · have hdp := Nat.pos_of_mem_divisors hd
      have he := hf ⟨qResidue d,
        residue_mem_trial L d hLp (Nat.dvd_of_mem_divisors hd)⟩
      simp only [difference_residue d (by omega), inner_sub_right,
        inner_smul_right, hmean] at he
      linarith
  refine ⟨f, hmatch, ?_⟩
  intro g hg
  apply hu g
  intro v
  exact inner_eq_of_divisor_tests L g h hg (differenceCLM v)
    (difference_mem_cell L hLp v v.property)

theorem target_inner_multiples (L : ℕ) (hL : 0 < L) :
    inner ℝ (target L) (qDivisor L) = 0 := by
  rw [target, inner_sub_left, qOne_inner_qDivisor L hL,
    real_inner_self_eq_norm_sq, qDivisor_norm_sq L hL, sub_self]

theorem target_norm_sq (L : ℕ) (hL : 0 < L) :
    ‖target L‖ ^ 2 = 1 - 1 / (L : ℝ) ^ 2 := by
  rw [target, norm_sub_sq_real, qOne_norm_sq,
    qOne_inner_qDivisor L hL, qDivisor_norm_sq L hL]
  ring

def canonical (L : ℕ) (hL : 2 ≤ L) : trialSpace L :=
  (existsUnique_divisor_match L hL (target L)
    (target_inner_multiples L (by omega))).exists.choose

theorem canonical_match (L : ℕ) (hL : 2 ≤ L) :
    ∀ d ∈ L.divisors, inner ℝ (canonical L hL : QHilbert) (qDivisor d) =
      inner ℝ (target L) (qDivisor d) :=
  (existsUnique_divisor_match L hL (target L)
    (target_inner_multiples L (by omega))).exists.choose_spec

theorem conditional_inner (L : ℕ) (f v : QHilbert) (hv : v ∈ cellSpace L) :
    inner ℝ (conditionalProjection L f) v = inner ℝ f v := by
  change inner ℝ ((cellSpace L).starProjection f) v = _
  rw [(cellSpace L).inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hv]

theorem conditional_eq_of_match (L : ℕ) (f h : QHilbert)
    (hh : h ∈ cellSpace L)
    (hm : ∀ d ∈ L.divisors, inner ℝ f (qDivisor d) = inner ℝ h (qDivisor d)) :
    conditionalProjection L f = h := by
  let g := conditionalProjection L f - h
  have hg : g ∈ cellSpace L := (cellSpace L).sub_mem
    ((cellSpace L).starProjection_apply_mem f) hh
  have he := inner_eq_of_divisor_tests L f h hm g hg
  have hz : inner ℝ g g = 0 := by
    change inner ℝ (conditionalProjection L f - h) g = 0
    rw [inner_sub_left, conditional_inner L f g hg, he, sub_self]
  have hg0 : g = 0 := by
    rw [real_inner_self_eq_norm_sq] at hz
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact sub_eq_zero.mp hg0

/-! Source: the user's retained-head criterion audit, 13 November 2026.
The cutoff-one formulas require no legal-density or RH premise. -/

/-- The cutoff one retains exactly the constant cell. -/
theorem cellSpace_one :
    cellSpace 1 = Submodule.span ℝ ({qOne} : Set QHilbert) := by
  simp [cellSpace, qDivisor_one]

/-- The cutoff-one projection is the complete-Q mean times one. -/
theorem conditionalProjection_one (f : QHilbert) :
    conditionalProjection 1 f = (inner ℝ f qOne) • qOne := by
  apply conditional_eq_of_match
  · exact (cellSpace 1).smul_mem _ (qOne_mem_cell 1 (by decide))
  · intro d hd
    have hd1 : d = 1 := Nat.dvd_one.mp (Nat.dvd_of_mem_divisors hd)
    subst d
    rw [qDivisor_one, real_inner_smul_left, real_inner_self_eq_norm_sq,
      qOne_norm_sq, mul_one]

/-- info: 'RiemannResearch.RH.QCRTFiniteCollocation.conditionalProjection_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditionalProjection_one

/-- The canonical lift exactly matches every gcd-cell conditional mean. -/
theorem canonical_conditional (L : ℕ) (hL : 2 ≤ L) :
    conditionalProjection L (canonical L hL) = target L :=
  conditional_eq_of_match L _ _ (target_mem_cell L (by omega)) (canonical_match L hL)

theorem conditional_gcd_coordinates (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (n : ℕ) (hn : 0 < n) :
    qSequence (conditionalProjection L f) (Nat.gcd n L) =
      qSequence (conditionalProjection L f) n :=
  QDivisorHilbert.qSequence_gcd_of_mem_divisor_cutoff L hL _
    ((cellSpace L).starProjection_apply_mem f) n hn

/-- Exact full-tail divisor moments of the canonical lift. -/
theorem canonical_divisor_moment (L : ℕ) (hL : 2 ≤ L)
    (d : ℕ) (hd : 0 < d) (hdL : d ∣ L) :
    inner ℝ (canonical L hL : QHilbert) (qDivisor d) =
      1 / (d : ℝ) ^ 2 - 1 / (L : ℝ) ^ 2 := by
  rw [canonical_match L hL d (Nat.mem_divisors.mpr ⟨hdL, by omega⟩),
    target, inner_sub_left, qOne_inner_qDivisor d hd,
    qDivisor_inner_qDivisor L d (by omega) hd, Nat.lcm_eq_left hdL]

/-- The handoff's square conditional-moment system, with every progression tail. -/
theorem canonical_dilation_moment (L : ℕ) (hL : 2 ≤ L)
    (d : ℕ) (hd : 0 < d) (hdL : d ∣ L) :
    inversePowerMean 0 (fun n => qSequence (canonical L hL) (d * n)) =
      1 - (d : ℝ) ^ 2 / (L : ℝ) ^ 2 := by
  have he := canonical_divisor_moment L hL d hd hdL
  rw [inner_qDivisor_eq_dilation _ d hd] at he
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  field_simp [hd0, hL0] at he ⊢
  nlinarith

/-- Surjectivity onto all gcd-cell targets vanishing on multiples of L. -/
theorem exists_conditional_lift (L : ℕ) (hL : 2 ≤ L)
    (h : QHilbert) (hc : h ∈ cellSpace L) (hm : inner ℝ h (qDivisor L) = 0) :
    ∃ f : trialSpace L, conditionalProjection L f = h := by
  obtain ⟨f, hf, _⟩ := existsUnique_divisor_match L hL h hm
  exact ⟨f, conditional_eq_of_match L f h hc hf⟩

theorem conditional_injective_on_trial (L : ℕ) (hL : 0 < L)
    (f g : trialSpace L)
    (he : conditionalProjection L f = conditionalProjection L g) : f = g := by
  have hv : (f : QHilbert) - (g : QHilbert) ∈ trialSpace L :=
    (trialSpace L).sub_mem f.property g.property
  have hp : conditionalProjection L ((f : QHilbert) - g) = 0 := by
    rw [map_sub, he, sub_self]
  have hz : inner ℝ ((f : QHilbert) - g)
      (differenceCLM ((f : QHilbert) - g)) = 0 := by
    rw [← conditional_inner L _ _ (difference_mem_cell L hL _ hv), hp]
    simp
  apply Subtype.ext
  exact sub_eq_zero.mp
    (eq_zero_of_difference_inner shiftCLM physicalShift_norm_le
      differenceCLM_injective _ hz)

/-- Exact image of the finite conditional projection, including its zero cell. -/
theorem conditional_range (L : ℕ) (hL : 2 ≤ L) (h : QHilbert) :
    (∃ f : trialSpace L, conditionalProjection L f = h) ↔
      h ∈ cellSpace L ∧ inner ℝ h (qDivisor L) = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨(cellSpace L).starProjection_apply_mem f, ?_⟩
    rw [conditional_inner L _ _ (divisor_mem_cell L L (by omega) (dvd_refl L))]
    exact trial_inner_multiples L (by omega) f f.property
  · rintro ⟨hc, hm⟩
    exact exists_conditional_lift L hL h hc hm

/-- Full CRT remainder, valid for every legal function at the cutoff. -/
theorem legal_error_identity (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : f ∈ trialSpace L) :
    ‖qOne - f‖ ^ 2 = 1 / (L : ℝ) ^ 2 + ‖target L - f‖ ^ 2 := by
  have ho : inner ℝ (qDivisor L) (target L - f) = 0 := by
    rw [inner_sub_right, real_inner_comm (target L) (qDivisor L),
      target_inner_multiples L hL, real_inner_comm f (qDivisor L),
      trial_inner_multiples L hL f hf, sub_self]
  have he : qOne - f = qDivisor L + (target L - f) := by
    unfold target
    abel
  rw [he, norm_add_sq_real, ho, qDivisor_norm_sq L hL]
  ring

def leakage (L : ℕ) (hL : 2 ≤ L) : ℝ :=
  ‖(canonical L hL : QHilbert) - target L‖ ^ 2

theorem canonical_error (L : ℕ) (hL : 2 ≤ L) :
    ‖qOne - (canonical L hL : QHilbert)‖ ^ 2 =
      1 / (L : ℝ) ^ 2 + leakage L hL := by
  rw [legal_error_identity L (by omega) _ (canonical L hL).property]
  simp only [leakage, norm_sub_rev]

theorem canonical_mean (L : ℕ) (hL : 2 ≤ L) :
    inner ℝ (canonical L hL : QHilbert) qOne = 1 - 1 / (L : ℝ) ^ 2 := by
  have he := inner_eq_of_divisor_tests L _ _ (canonical_match L hL)
    qOne (qOne_mem_cell L (by omega))
  rw [he, target, inner_sub_left, real_inner_self_eq_norm_sq, qOne_norm_sq,
    real_inner_comm qOne (qDivisor L), qOne_inner_qDivisor L (by omega)]

theorem canonical_norm (L : ℕ) (hL : 2 ≤ L) :
    ‖(canonical L hL : QHilbert)‖ ^ 2 =
      1 - 1 / (L : ℝ) ^ 2 + leakage L hL := by
  have he := canonical_error L hL
  rw [norm_sub_sq_real, qOne_norm_sq,
    real_inner_comm (canonical L hL : QHilbert) qOne, canonical_mean L hL] at he
  linarith

/-- Complete energy identity; the contraction defect is not discarded. -/
theorem canonical_difference_energy (L : ℕ) (hL : 2 ≤ L) :
    ‖differenceCLM (canonical L hL) - target L‖ ^ 2 +
      (‖(canonical L hL : QHilbert)‖ ^ 2 -
        ‖physicalShift (canonical L hL)‖ ^ 2) = ‖target L‖ ^ 2 := by
  apply matched_energy shiftCLM
  exact inner_eq_of_divisor_tests L _ _ (canonical_match L hL)
    (differenceCLM (canonical L hL))
    (difference_mem_cell L (by omega) _ (canonical L hL).property)

/-- Leakage occurs with the same coefficient in the primitive and shifted
energies; it cancels from their difference. -/
theorem canonical_shift_energy (L : ℕ) (hL : 2 ≤ L) :
    ‖physicalShift (canonical L hL)‖ ^ 2 = leakage L hL +
      ‖differenceCLM (canonical L hL) - target L‖ ^ 2 := by
  have he := canonical_difference_energy L hL
  rw [canonical_norm L hL, target_norm_sq L (by omega)] at he
  linarith

theorem canonical_shift_defect_le (L : ℕ) (hL : 2 ≤ L) :
    ‖(canonical L hL : QHilbert)‖ ^ 2 - ‖physicalShift (canonical L hL)‖ ^ 2 ≤
      1 - 1 / (L : ℝ) ^ 2 := by
  have he := canonical_difference_energy L hL
  rw [target_norm_sq L (by omega)] at he
  linarith [sq_nonneg ‖differenceCLM (canonical L hL) - target L‖]

end RiemannResearch.RH.QCRTFiniteCollocation
