/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdCellProjection
import RiemannResearch.RH.QGcdCellObstruction
import RiemannResearch.RH.QCRTNestedCutoffs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact orthogonal gcd-cell innovations at a prime-power admission

Source: CanonicalPrimePowerUpdatesResearch20261107, Section 5.
The normalized innovation denominators are the actual complete Q masses.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerCellInnovations
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open QCRTFiniteCollocation QGcdCellRefinement QGcdCellProjection
open QGcdCellObstruction

def oldCell (a R e : ℕ) : Set ℕ := gcdCell (a * R) (a * e)
def newCell (p a R e : ℕ) : Set ℕ := gcdCell ((p * a) * R) ((p * a) * e)
def splitRatio (p : ℕ) : ℝ := 1 / (p : ℝ) ^ 2
def cellInnovation (p a R e : ℕ) : QHilbert :=
  eventVector (newCell p a R e) - splitRatio p • eventVector (oldCell a R e)
def innovationWeight (p a R e : ℕ) : ℝ :=
  eventMass (oldCell a R e) * splitRatio p * (1 - splitRatio p)

theorem newCell_mass (p a R e : ℕ) (hp : 0 < p) (ha : 0 < a) :
    eventMass (newCell p a R e) = splitRatio p * eventMass (oldCell a R e) :=
  gcdCell_refinement_mass a p R e ha hp

theorem newCell_subset_oldCell (p a R e : ℕ) (hp : 0 < p) (ha : 0 < a)
    (hcop : Nat.Coprime p R) : newCell p a R e ⊆ oldCell a R e := by
  intro n hn
  rw [newCell, gcdCell_mul (p * a) R e (Nat.mul_pos hp ha)] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  have hk' : Nat.gcd k R = e := hk
  change Nat.gcd ((p * a) * k) (a * R) = a * e
  have he : (p * a) * k = a * (p * k) := by ring
  rw [he, Nat.gcd_mul_left, hcop.gcd_mul_left_cancel, hk']

theorem oldCell_mem (a R e : ℕ) (ha : 0 < a) (hR : 0 < R) (he : e ∈ R.divisors) :
    eventVector (oldCell a R e) ∈ cellSpace (a * R) := by
  exact eventVector_gcdCell_mem _ _ (Nat.mul_pos ha hR)
    (Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left a (Nat.dvd_of_mem_divisors he), by positivity⟩)

theorem cellInnovation_norm_sq (p a R e : ℕ) (hp : 0 < p) (ha : 0 < a)
    (hcop : Nat.Coprime p R) :
    ‖cellInnovation p a R e‖ ^ 2 = innovationWeight p a R e := by
  exact event_innovation_norm_sq _ _ (newCell_subset_oldCell p a R e hp ha hcop)
    (splitRatio p) (newCell_mass p a R e hp ha)

theorem cellInnovation_inner_old_divisor (p a R e d : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hR : 0 < R) (hcop : Nat.Coprime p R) (hd : d ∣ a * R) :
    inner ℝ (cellInnovation p a R e) (qDivisor d) = 0 := by
  have hBE := newCell_subset_oldCell p a R e hp ha hcop
  rw [cellInnovation, inner_sub_left, real_inner_smul_left,
    event_inner_divisor_of_gcd_support (a * R) (a * e) d (Nat.mul_pos ha hR) hd _ hBE,
    event_inner_divisor_of_gcd_support (a * R) (a * e) d (Nat.mul_pos ha hR) hd
      (oldCell a R e) (Set.Subset.refl _),
    newCell_mass p a R e hp ha]
  ring

theorem cellInnovation_inner_old (p a R e : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hR : 0 < R) (hcop : Nat.Coprime p R)
    (v : QHilbert) (hv : v ∈ cellSpace (a * R)) :
    inner ℝ (cellInnovation p a R e) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, hd, rfl⟩
    exact cellInnovation_inner_old_divisor p a R e d hp ha hR hcop (Nat.dvd_of_mem_divisors hd)
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul c x hx ih => simp [inner_smul_right, ih]

theorem cellInnovation_inner (p a R e f : ℕ) (hp : 0 < p) (ha : 0 < a)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (hf : f ∈ R.divisors) :
    inner ℝ (cellInnovation p a R e) (cellInnovation p a R f) =
      if e = f then innovationWeight p a R e else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    rw [if_pos rfl, real_inner_self_eq_norm_sq, cellInnovation_norm_sq p a R e hp ha hcop]
  · rw [if_neg hef]
    have hE := cellInnovation_inner_old p a R e hp ha hR hcop _ (oldCell_mem a R f ha hR hf)
    change inner ℝ (cellInnovation p a R e)
      (eventVector (newCell p a R f) - splitRatio p • eventVector (oldCell a R f)) = 0
    rw [inner_sub_right, inner_smul_right, hE, mul_zero, sub_zero]
    rw [cellInnovation, inner_sub_left, real_inner_smul_left]
    have hneq : (p * a) * e ≠ (p * a) * f :=
      fun h => hef (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp ha) h)
    have hB : inner ℝ (eventVector (newCell p a R e)) (eventVector (newCell p a R f)) = 0 := by
      rw [newCell, newCell, gcdCell_inner, if_neg hneq]
    have hEB : inner ℝ (eventVector (oldCell a R e)) (eventVector (newCell p a R f)) = 0 := by
      apply eventVector_inner_of_disjoint
      apply Set.disjoint_left.mpr
      intro n hnE hnB
      have hE' : Nat.gcd n (a * R) = a * e := hnE
      have hF' : Nat.gcd n (a * R) = a * f := newCell_subset_oldCell p a R f hp ha hcop hnB
      exact hef (Nat.eq_of_mul_eq_mul_left ha (hE'.symm.trans hF'))
    rw [hB, hEB]
    ring

theorem innovationWeight_pos (p a R e : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (he : e ∈ R.divisors) : 0 < innovationWeight p a R e := by
  have hmass : 0 < eventMass (oldCell a R e) :=
    gcdCell_mass_pos _ _ (Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul_left a (Nat.dvd_of_mem_divisors he), by positivity⟩)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcpos : 0 < splitRatio p := by unfold splitRatio; positivity
  have hclt : splitRatio p < 1 := by
    unfold splitRatio
    apply (div_lt_iff₀ (by positivity : 0 < (p : ℝ) ^ 2)).mpr
    nlinarith
  exact mul_pos (mul_pos hmass hcpos) (by linarith)

/-- Every newly admitted divisor contains the entire newly admitted prime
power. This is proved from finite divisor arithmetic, not assumed. -/
theorem new_divisor_shape (p j R d : ℕ) (hp : p.Prime) (hR : 0 < R)
    (hd : d ∣ p ^ (j + 1) * R) (hnew : ¬ d ∣ p ^ j * R) :
    ∃ e ∈ R.divisors, d = p ^ (j + 1) * e := by
  obtain ⟨u, v, hu, hv, huv⟩ := Nat.dvd_mul.mp hd
  obtain ⟨i, hij, hi⟩ := (Nat.dvd_prime_pow hp).mp hu
  have hieq : i = j + 1 := by
    by_contra hne
    have hij' : i ≤ j := by omega
    apply hnew
    rw [← huv, hi]
    exact Nat.mul_dvd_mul (pow_dvd_pow p hij') hv
  refine ⟨v, Nat.mem_divisors.mpr ⟨hv, ne_of_gt hR⟩, ?_⟩
  rw [← huv, hi, hieq]

/-- A new divisor row is the sum of its new high-depth gcd cells. -/
theorem new_divisor_eq_sum_cells (b R e : ℕ) (hb : 0 < b) (hR : 0 < R)
    (heR : e ∣ R) :
    qDivisor (b * e) = ∑ f ∈ R.divisors,
      (if e ∣ f then (1 : ℝ) else 0) • eventVector (gcdCell (b * R) (b * f)) := by
  classical
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · change qSequence (qDivisor (b * e)) n =
      qSequenceLinear (∑ f ∈ R.divisors,
        (if e ∣ f then (1 : ℝ) else 0) • eventVector (gcdCell (b * R) (b * f))) n
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change qSequence (qDivisor (b * e)) n = ∑ f ∈ R.divisors,
      (if e ∣ f then (1 : ℝ) else 0) * qSequence (eventVector (gcdCell (b * R) (b * f))) n
    simp only [qSequence_qDivisor, qSequence_eventVector]
    by_cases hbn : b ∣ n
    · obtain ⟨k, rfl⟩ := hbn
      have hk : k ≠ 0 := by intro h; simp [h] at hn
      have hdiv : b * e ∣ b * k ↔ e ∣ k := by
        constructor
        · rintro ⟨t, ht⟩
          refine ⟨t, ?_⟩
          apply Nat.eq_of_mul_eq_mul_left hb
          simpa only [mul_assoc] using ht
        · exact Nat.mul_dvd_mul_left b
      have hc : Nat.gcd k R ∈ R.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right k R, ne_of_gt hR⟩
      have hec : e ∣ Nat.gcd k R ↔ e ∣ k :=
        ⟨fun h => h.trans (Nat.gcd_dvd_left k R), fun h => Nat.dvd_gcd h heR⟩
      have hcell (f : ℕ) : Nat.gcd (b * k) (b * R) = b * f ↔ Nat.gcd k R = f := by
        rw [Nat.gcd_mul_left]
        exact ⟨Nat.eq_of_mul_eq_mul_left hb, congrArg (b * ·)⟩
      symm
      rw [Finset.sum_eq_single (Nat.gcd k R)]
      · simp [eventSequence, gcdCell, hn, positiveDivisor, hcell, hdiv, hec]
      · intro f hf hne
        have hgf : Nat.gcd k R ≠ f := Ne.symm hne
        simp [eventSequence, gcdCell, hn, hcell, hgf]
      · intro hnot
        exact (hnot hc).elim
    · have hbe : ¬ b * e ∣ n := fun h => hbn ((dvd_mul_right b e).trans h)
      rw [show positiveDivisor (b * e) n = 0 by simp [positiveDivisor, hn, hbe]]
      symm
      apply Finset.sum_eq_zero
      intro f hf
      have hnf : Nat.gcd n (b * R) ≠ b * f := by
        intro h
        have hg := Nat.gcd_dvd_left n (b * R)
        rw [h] at hg
        exact hbn ((dvd_mul_right b f).trans hg)
      simp [eventSequence, gcdCell, hn, hnf]

theorem cellInnovation_mem_new (p a R e : ℕ) (hp : 0 < p) (ha : 0 < a)
    (hR : 0 < R) (he : e ∈ R.divisors) :
    cellInnovation p a R e ∈ cellSpace ((p * a) * R) := by
  have hM : 0 < (p * a) * R := Nat.mul_pos (Nat.mul_pos hp ha) hR
  have hLM : a * R ∣ (p * a) * R := ⟨p, by ring⟩
  apply Submodule.sub_mem
  · exact eventVector_gcdCell_mem _ _ hM
      (Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_left (p * a) (Nat.dvd_of_mem_divisors he), ne_of_gt hM⟩)
  · apply Submodule.smul_mem
    exact QCRTNestedCutoffs.cellSpace_mono_of_dvd _ _ hM hLM (oldCell_mem a R e ha hR he)

def innovationProjection (p a R : ℕ) (r : QHilbert) : QHilbert :=
  ∑ e ∈ R.divisors,
    (inner ℝ r (eventVector (newCell p a R e)) / innovationWeight p a R e) •
      cellInnovation p a R e

theorem innovationProjection_mem_new (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (r : QHilbert) :
    innovationProjection p a R r ∈ cellSpace ((p * a) * R) := by
  apply Submodule.sum_mem
  intro e he
  apply Submodule.smul_mem
  exact cellInnovation_mem_new p a R e hp.pos ha hR he

theorem innovationProjection_inner_old (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (r v : QHilbert) (hv : v ∈ cellSpace (a * R)) :
    inner ℝ (innovationProjection p a R r) v = 0 := by
  rw [innovationProjection, sum_inner]
  apply Finset.sum_eq_zero
  intro e he
  rw [real_inner_smul_left, cellInnovation_inner_old p a R e hp.pos ha hR hcop v hv, mul_zero]

theorem innovationProjection_inner_innovation (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (r : QHilbert) (e : ℕ) (he : e ∈ R.divisors) :
    inner ℝ (innovationProjection p a R r) (cellInnovation p a R e) =
      inner ℝ r (eventVector (newCell p a R e)) := by
  classical
  rw [innovationProjection, sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single e]
  · rw [cellInnovation_inner p a R e e hp.pos ha hR hcop he, if_pos rfl,
      div_mul_cancel₀ _ (ne_of_gt (innovationWeight_pos p a R e hp ha hR he))]
  · intro f hf hne
    rw [cellInnovation_inner p a R f e hp.pos ha hR hcop he, if_neg hne, mul_zero]
  · intro hnot
    exact (hnot he).elim

theorem innovationProjection_inner_newCell (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (r : QHilbert) (e : ℕ) (he : e ∈ R.divisors) :
    inner ℝ (innovationProjection p a R r) (eventVector (newCell p a R e)) =
      inner ℝ r (eventVector (newCell p a R e)) := by
  have heq : eventVector (newCell p a R e) =
      cellInnovation p a R e + splitRatio p • eventVector (oldCell a R e) := by
    unfold cellInnovation
    abel
  calc
    _ = inner ℝ (innovationProjection p a R r)
        (cellInnovation p a R e + splitRatio p • eventVector (oldCell a R e)) :=
      congrArg (fun v => inner ℝ (innovationProjection p a R r) v) heq
    _ = _ := by
      rw [inner_add_right, inner_smul_right,
        innovationProjection_inner_innovation p a R hp ha hR hcop r e he,
        innovationProjection_inner_old p a R hp ha hR hcop r _ (oldCell_mem a R e ha hR he),
        mul_zero, add_zero]

private theorem conditionalProjection_eq_innovations_of_rows (p a R : ℕ)
    (hp : p.Prime) (ha : 0 < a) (hR : 0 < R) (hcop : Nat.Coprime p R)
    (hrows : ∀ d ∈ ((p * a) * R).divisors,
      d ∣ a * R ∨ ∃ e ∈ R.divisors, d = (p * a) * e)
    (r : QHilbert) (hr : ∀ v ∈ cellSpace (a * R), inner ℝ r v = 0) :
    conditionalProjection ((p * a) * R) r = innovationProjection p a R r := by
  apply conditional_eq_of_match _ r _ (innovationProjection_mem_new p a R hp ha hR r)
  intro d hd
  rcases hrows d hd with hold | ⟨e, he, rfl⟩
  · have hmem := divisor_mem_cell (a * R) d (Nat.mul_pos ha hR) hold
    rw [hr _ hmem, innovationProjection_inner_old p a R hp ha hR hcop r _ hmem]
  · rw [new_divisor_eq_sum_cells (p * a) R e (Nat.mul_pos hp.pos ha) hR
      (Nat.dvd_of_mem_divisors he)]
    simp only [inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro f hf
    exact congrArg (fun x : ℝ => (if e ∣ f then (1 : ℝ) else 0) * x)
      (innovationProjection_inner_newCell p a R hp ha hR hcop r f hf).symm

theorem innovationProjection_norm_sq (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (r : QHilbert) :
    ‖innovationProjection p a R r‖ ^ 2 =
      ∑ e ∈ R.divisors,
        (inner ℝ r (eventVector (newCell p a R e))) ^ 2 / innovationWeight p a R e := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (innovationProjection p a R r)
    (∑ e ∈ R.divisors,
      (inner ℝ r (eventVector (newCell p a R e)) / innovationWeight p a R e) •
        cellInnovation p a R e) = _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [inner_smul_right, innovationProjection_inner_innovation p a R hp ha hR hcop r e he]
  ring

/-- The paper's exact screened-cell Parseval identity with the complete
prime-power admission arithmetic discharged. -/
theorem prime_power_revealed_parseval (p j R : ℕ) (hp : p.Prime) (hR : 0 < R)
    (hcop : Nat.Coprime p R) (r : QHilbert)
    (hr : ∀ v ∈ cellSpace (p ^ j * R), inner ℝ r v = 0) :
    ‖conditionalProjection (p ^ (j + 1) * R) r‖ ^ 2 =
      ∑ e ∈ R.divisors,
        (inner ℝ r (eventVector (gcdCell (p ^ (j + 1) * R) (p ^ (j + 1) * e)))) ^ 2 /
          (eventMass (gcdCell (p ^ j * R) (p ^ j * e)) *
            (1 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ) ^ 2)) := by
  have heq : p * p ^ j = p ^ (j + 1) := (pow_succ' p j).symm
  have hrows : ∀ d ∈ ((p * p ^ j) * R).divisors,
      d ∣ p ^ j * R ∨ ∃ e ∈ R.divisors, d = (p * p ^ j) * e := by
    intro d hd
    by_cases hold : d ∣ p ^ j * R
    · exact Or.inl hold
    · right
      rw [heq] at hd
      simpa only [heq] using new_divisor_shape p j R d hp hR (Nat.dvd_of_mem_divisors hd) hold
  have h := conditionalProjection_eq_innovations_of_rows p (p ^ j) R hp (pow_pos hp.pos _)
    hR hcop hrows r hr
  have hn := innovationProjection_norm_sq p (p ^ j) R hp (pow_pos hp.pos _) hR hcop r
  rw [← h] at hn
  simpa only [heq, innovationWeight, oldCell, newCell, splitRatio] using hn

theorem canonical_prime_power_revealed_parseval (p j R : ℕ) (hp : p.Prime) (hR : 0 < R)
    (hcop : Nat.Coprime p R) (hL : 2 ≤ p ^ j * R) :
    ‖conditionalProjection (p ^ (j + 1) * R) (QCRTNestedCutoffs.leakageVector (p ^ j * R) hL)‖ ^ 2 =
      ∑ e ∈ R.divisors,
        (inner ℝ (QCRTNestedCutoffs.leakageVector (p ^ j * R) hL)
          (eventVector (gcdCell (p ^ (j + 1) * R) (p ^ (j + 1) * e)))) ^ 2 /
          (eventMass (gcdCell (p ^ j * R) (p ^ j * e)) *
            (1 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ) ^ 2)) :=
  prime_power_revealed_parseval p j R hp hR hcop _
    (QCRTNestedCutoffs.leakageVector_inner_cell _ hL)

end RiemannResearch.RH.QPrimePowerCellInnovations
