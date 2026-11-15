/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdCellRefinement
import RiemannResearch.RH.ZetaTwoElementaryRationalBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An actual arithmetic obstruction to generic refinement-depth decay

Source: CanonicalPrimePowerUpdatesResearch20261107, Section 5.
The witness is a concrete periodic physical sequence supported on two residue
classes, scaled to any depth. It is not asserted to be canonical leakage or a
legal affine lift. The conclusion excludes a depth-decaying estimate based on
periodicity and old-cell orthogonality alone.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QGcdCellObstruction
open ZetaTwoHilbert ZetaTwoProbability QGcdCellRefinement
open QCRTFiniteCollocation QDivisibilityDensity

def residueEvent (R i : ℕ) : Set ℕ := {n | n % R = i}
def evenEvent : Set ℕ := {n | 2 ∣ n}
def residueMass (R i : ℕ) : ℝ := eventMass (residueEvent R i)
def evenResidueMass (R i : ℕ) : ℝ := eventMass (residueEvent R i ∩ evenEvent)
def signedResidueMoment (R : ℕ) : ℝ :=
  residueMass R 2 * evenResidueMass R 1 -
    residueMass R 1 * evenResidueMass R 2

/-- The scaled two-residue witness from the paper. -/
def witness (a R : ℕ) : QHilbert :=
  ((a : ℝ) * residueMass R 2) • eventVector (scaledEvent a (residueEvent R 1)) -
    ((a : ℝ) * residueMass R 1) • eventVector (scaledEvent a (residueEvent R 2))

theorem residueEvent_disjoint (R : ℕ) :
    Disjoint (residueEvent R 1) (residueEvent R 2) := by
  apply Set.disjoint_left.mpr
  intro n hn hm
  have h1 : n % R = 1 := hn
  have h2 : n % R = 2 := hm
  omega

theorem scaled_residueEvent_eq (a R i : ℕ) (ha : 0 < a) :
    scaledEvent a (residueEvent R i) = residueEvent (a * R) (a * i) := by
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    change (a * k) % (a * R) = a * i
    rw [Nat.mul_mod_mul_left, hk]
  · intro hn
    have hn' : n % (a * R) = a * i := hn
    have had : a ∣ n := by
      refine ⟨i + R * (n / (a * R)), ?_⟩
      calc
        n = n % (a * R) + (a * R) * (n / (a * R)) :=
          (Nat.mod_add_div n (a * R)).symm
        _ = a * (i + R * (n / (a * R))) := by rw [hn']; ring
    obtain ⟨k, rfl⟩ := had
    refine ⟨k, ?_, rfl⟩
    change k % R = i
    rw [Nat.mul_mod_mul_left] at hn'
    exact Nat.eq_of_mul_eq_mul_left ha hn'

theorem eventSequence_residue (L i n : ℕ) (hi : 0 < i) :
    eventSequence (residueEvent L i) n = if n % L = i then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · simp [eventSequence, hn, (ne_of_gt hi).symm]
  · by_cases hm : n % L = i <;> simp [eventSequence, residueEvent, hn, hm]

theorem scaled_residue_periodic (a R i : ℕ) (ha : 0 < a) (hi : 0 < i) (n : ℕ) :
    eventSequence (scaledEvent a (residueEvent R i)) (n + a * R) =
      eventSequence (scaledEvent a (residueEvent R i)) n := by
  rw [scaled_residueEvent_eq a R i ha,
    eventSequence_residue _ _ _ (Nat.mul_pos ha hi),
    eventSequence_residue _ _ _ (Nat.mul_pos ha hi)]
  simp

/-- The concrete witness is periodic in the old physical cutoff, including
the zero anchor. -/
theorem witness_periodic (a R : ℕ) (ha : 0 < a) :
    Function.Periodic (qSequence (witness a R)) (a * R) := by
  intro n
  change qSequenceLinear (witness a R) (n + a * R) =
    qSequenceLinear (witness a R) n
  simp only [witness, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change ((a : ℝ) * residueMass R 2) *
      qSequence (eventVector (scaledEvent a (residueEvent R 1))) (n + a * R) -
      ((a : ℝ) * residueMass R 1) *
      qSequence (eventVector (scaledEvent a (residueEvent R 2))) (n + a * R) =
    ((a : ℝ) * residueMass R 2) *
      qSequence (eventVector (scaledEvent a (residueEvent R 1))) n -
      ((a : ℝ) * residueMass R 1) *
      qSequence (eventVector (scaledEvent a (residueEvent R 2))) n
  simp only [qSequence_eventVector]
  rw [scaled_residue_periodic a R 1 ha (by omega),
    scaled_residue_periodic a R 2 ha (by omega)]

theorem witness_zero_on_multiples (a R : ℕ) (ha : 0 < a) (n : ℕ) :
    qSequence (witness a R) ((a * R) * n) = 0 := by
  have hset1 := scaled_residueEvent_eq a R 1 ha
  have hset2 := scaled_residueEvent_eq a R 2 ha
  change qSequenceLinear (witness a R) ((a * R) * n) = 0
  simp only [witness, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change ((a : ℝ) * residueMass R 2) *
      qSequence (eventVector (scaledEvent a (residueEvent R 1))) ((a * R) * n) -
    ((a : ℝ) * residueMass R 1) *
      qSequence (eventVector (scaledEvent a (residueEvent R 2))) ((a * R) * n) = 0
  simp only [qSequence_eventVector]
  rw [hset1, hset2, eventSequence_residue _ _ _ (by positivity),
    eventSequence_residue _ _ _ (by positivity)]
  simp [Nat.mul_mod_right, (ne_of_gt ha).symm,
    (Nat.mul_ne_zero (ne_of_gt ha) (by omega : 2 ≠ 0)).symm]

theorem scaledEvent_disjoint (a : ℕ) (ha : 0 < a) (S T : Set ℕ)
    (hST : Disjoint S T) : Disjoint (scaledEvent a S) (scaledEvent a T) := by
  apply Set.disjoint_left.mpr
  rintro n ⟨j, hj, he⟩ ⟨k, hk, hf⟩
  have hjk : j = k := Nat.eq_of_mul_eq_mul_left ha (he.trans hf.symm)
  subst k
  exact Set.disjoint_left.mp hST hj hk

theorem eventVector_inner_of_disjoint (S T : Set ℕ) (hST : Disjoint S T) :
    inner ℝ (eventVector S) (eventVector T) = 0 := by
  rw [eventVector_inner, Set.disjoint_iff_inter_eq_empty.mp hST, eventMass_empty]

theorem residueMass_sum_le_one (R : ℕ) :
    residueMass R 1 + residueMass R 2 ≤ 1 := by
  rw [residueMass, residueMass, ← eventMass_union_of_disjoint _ _ (residueEvent_disjoint R)]
  exact eventMass_le_one _

theorem residueMass_one_lower (R : ℕ) (hR : 3 ≤ R) :
    1 / zetaTwo ≤ residueMass R 1 := by
  have hs : ({1} : Set ℕ) ⊆ residueEvent R 1 := by
    intro n hn
    have hn1 : n = 1 := Set.mem_singleton_iff.mp hn
    subst n
    exact Nat.mod_eq_of_lt (by omega)
  have h := eventMass_mono hs
  rw [eventMass_singleton 1 (by omega)] at h
  simpa [positiveQWeight, residueMass] using h

theorem evenResidueMass_two_lower (R : ℕ) (hR : 3 ≤ R) :
    1 / (4 * zetaTwo) ≤ evenResidueMass R 2 := by
  have hs : ({2} : Set ℕ) ⊆ residueEvent R 2 ∩ evenEvent := by
    intro n hn
    have hn2 : n = 2 := Set.mem_singleton_iff.mp hn
    subst n
    exact ⟨Nat.mod_eq_of_lt (by omega), dvd_refl 2⟩
  have h := eventMass_mono hs
  rw [eventMass_singleton 2 (by omega)] at h
  simpa [positiveQWeight, evenResidueMass, mul_comm,
    show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem evenResidueMass_one_upper (R : ℕ) (hR : 3 ≤ R) :
    evenResidueMass R 1 ≤ (1 - 1 / zetaTwo) / 4 := by
  have hs : residueEvent R 1 ∩ evenEvent ⊆ scaledEvent 2 (({1} : Set ℕ)ᶜ) := by
    rintro n ⟨hn, ⟨k, hk⟩⟩
    refine ⟨k, ?_, hk.symm⟩
    intro hk1
    have hk' : k = 1 := Set.mem_singleton_iff.mp hk1
    have hn' : n % R = 1 := hn
    rw [hk, hk', mul_one, Nat.mod_eq_of_lt (by omega : 2 < R)] at hn'
    omega
  have h := eventMass_mono hs
  rw [eventMass_scaledEvent 2 (by omega), eventMass_compl,
    eventMass_singleton 1 (by omega)] at h
  simpa [positiveQWeight, evenResidueMass, div_eq_mul_inv, mul_comm,
    show (2 : ℝ) ^ 2 = 4 by norm_num] using h

/-- The signed physical residue moment stays away from zero. -/
theorem signedResidueMoment_le (R : ℕ) (hR : 3 ≤ R) :
    signedResidueMoment R ≤ -(1 / 28 : ℝ) := by
  have hw1 := residueMass_one_lower R hR
  have hw12 := residueMass_sum_le_one R
  have hv1 := evenResidueMass_one_upper R hR
  have hv2 := evenResidueMass_two_lower R hR
  have hw10 : 0 ≤ residueMass R 1 := eventMass_nonneg _
  have hw20 : 0 ≤ residueMass R 2 := eventMass_nonneg _
  have hv10 : 0 ≤ evenResidueMass R 1 := eventMass_nonneg _
  have hv20 : 0 ≤ evenResidueMass R 2 := eventMass_nonneg _
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hZupper : zetaTwo ≤ 7 / 4 := by linarith [zetaTwo_lt_five_thirds]
  have hinv : (4 / 7 : ℝ) ≤ 1 / zetaTwo := by
    apply (le_div_iff₀ hZ).mpr
    nlinarith
  have hnon : 0 ≤ 1 - 1 / zetaTwo := by linarith
  have hprod1 := mul_le_mul (show residueMass R 2 ≤ 1 - 1 / zetaTwo by linarith)
    hv1 hv10 hnon
  have hprod2 := mul_le_mul hw1 hv2 (by positivity : 0 ≤ 1 / (4 * zetaTwo)) hw10
  have hrecip : 1 / zetaTwo * (1 / (4 * zetaTwo)) = (1 / zetaTwo) ^ 2 / 4 := by
    field_simp [ne_of_gt hZ]
  rw [hrecip] at hprod2
  unfold signedResidueMoment
  nlinarith

theorem witness_norm_sq (a R : ℕ) (ha : 0 < a) :
    ‖witness a R‖ ^ 2 =
      residueMass R 1 * residueMass R 2 * (residueMass R 1 + residueMass R 2) := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hd := scaledEvent_disjoint a ha _ _ (residueEvent_disjoint R)
  rw [witness, norm_sub_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    eventVector_norm_sq, eventVector_norm_sq,
    eventMass_scaledEvent a ha, eventMass_scaledEvent a ha,
    inner_smul_right, real_inner_smul_left, eventVector_inner_of_disjoint _ _ hd]
  unfold residueMass
  field_simp [ha0]
  ring

theorem witness_norm_sq_le (a R : ℕ) (ha : 0 < a) : ‖witness a R‖ ^ 2 ≤ 1 / 4 := by
  rw [witness_norm_sq a R ha]
  have h1 : 0 ≤ residueMass R 1 := eventMass_nonneg _
  have h2 : 0 ≤ residueMass R 2 := eventMass_nonneg _
  have hs := residueMass_sum_le_one R
  have hp : residueMass R 1 * residueMass R 2 ≤ 1 / 4 := by
    nlinarith [sq_nonneg (residueMass R 1 - residueMass R 2)]
  have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg h1 h2)
  nlinarith

theorem residueEvent_subset_gcdCell (R i : ℕ) (hi : Nat.Coprime i R) :
    residueEvent R i ⊆ gcdCell R 1 := by
  intro n hn
  change Nat.gcd n R = 1
  have hn' : n % R = i := hn
  calc
    Nat.gcd n R = Nat.gcd (n % R) R := by rw [Nat.gcd_comm n R, Nat.gcd_rec]
    _ = 1 := by rw [hn']; exact hi.gcd_eq_one

theorem scaledEvent_subset_gcdCell (a R : ℕ) (_ha : 0 < a) (S : Set ℕ)
    (hS : S ⊆ gcdCell R 1) : scaledEvent a S ⊆ gcdCell (a * R) a := by
  rintro n ⟨k, hk, rfl⟩
  have hg : Nat.gcd k R = 1 := hS hk
  change Nat.gcd (a * k) (a * R) = a
  rw [Nat.gcd_mul_left, hg, mul_one]

theorem event_inner_divisor_of_gcd_support (L a d : ℕ) (hL : 0 < L)
    (hd : d ∣ L) (S : Set ℕ) (hS : S ⊆ gcdCell L a) :
    inner ℝ (eventVector S) (qDivisor d) = eventMass S * positiveDivisor d a := by
  classical
  rw [qInner_weighted, qSequence_eventVector, qSequence_qDivisor]
  calc
    _ = ∑' n : ℕ, (positiveQWeight n * eventSequence S n) * positiveDivisor d a := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · simp [eventSequence, hn]
      · by_cases hs : n ∈ S
        · have hg : Nat.gcd n L = a := hS hs
          have he := QDivisorHilbert.positiveDivisor_gcd_cutoff L d n hL
            (Nat.pos_of_ne_zero hn) hd
          rw [hg] at he
          rw [← he]
        · simp [eventSequence, hn, hs]
    _ = eventMass S * positiveDivisor d a := tsum_mul_right

/-- The witness is orthogonal to every old divisor cell. -/
theorem witness_inner_old_divisor (a R d : ℕ) (ha : 0 < a) (hR : 0 < R)
    (hodd : Nat.Coprime 2 R) (hd : d ∣ a * R) :
    inner ℝ (witness a R) (qDivisor d) = 0 := by
  have hs1 := scaledEvent_subset_gcdCell a R ha _
    (residueEvent_subset_gcdCell R 1 (Nat.coprime_one_left R))
  have hs2 := scaledEvent_subset_gcdCell a R ha _
    (residueEvent_subset_gcdCell R 2 hodd)
  rw [witness, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    event_inner_divisor_of_gcd_support (a * R) a d (Nat.mul_pos ha hR) hd _ hs1,
    event_inner_divisor_of_gcd_support (a * R) a d (Nat.mul_pos ha hR) hd _ hs2,
    eventMass_scaledEvent a ha, eventMass_scaledEvent a ha]
  unfold residueMass
  ring

theorem witness_inner_old_cell (a R : ℕ) (ha : 0 < a) (hR : 0 < R)
    (hodd : Nat.Coprime 2 R) (v : QHilbert) (hv : v ∈ cellSpace (a * R)) :
    inner ℝ (witness a R) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, hd, rfl⟩
    exact witness_inner_old_divisor a R d ha hR hodd (Nat.dvd_of_mem_divisors hd)
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul c x hx ih => simp [inner_smul_right, ih]

theorem scaled_residue_inter_new_cell (a R i : ℕ) (ha : 0 < a)
    (hodd : Nat.Coprime 2 R) (hi : Nat.Coprime i R) :
    scaledEvent a (residueEvent R i) ∩ gcdCell ((2 * a) * R) (2 * a) =
      scaledEvent a (residueEvent R i ∩ evenEvent) := by
  have hmem (k : ℕ) (hk : k ∈ residueEvent R i) :
      Nat.gcd (a * k) ((2 * a) * R) = 2 * a ↔ 2 ∣ k := by
    have hg : Nat.gcd k R = 1 := residueEvent_subset_gcdCell R i hi hk
    have he : (2 * a) * R = a * (2 * R) := by ring
    rw [he, Nat.gcd_mul_left, hodd.gcd_mul, hg, mul_one]
    constructor
    · intro h
      have heq : a * Nat.gcd k 2 = a * 2 := by simpa only [Nat.mul_comm 2 a] using h
      exact Nat.gcd_eq_right_iff_dvd.mp (Nat.eq_of_mul_eq_mul_left ha heq)
    · intro h
      rw [Nat.gcd_eq_right h]
      ring
  ext n
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hg⟩
    exact ⟨k, ⟨hk, (hmem k hk).mp hg⟩, rfl⟩
  · rintro ⟨k, ⟨hk, he⟩, rfl⟩
    exact ⟨⟨k, hk, rfl⟩, (hmem k hk).mpr he⟩

theorem witness_inner_new_cell (a R : ℕ) (ha : 0 < a)
    (hodd : Nat.Coprime 2 R) :
    inner ℝ (witness a R) (eventVector (gcdCell ((2 * a) * R) (2 * a))) =
      signedResidueMoment R / (a : ℝ) := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  rw [witness, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    eventVector_inner, eventVector_inner,
    scaled_residue_inter_new_cell a R 1 ha hodd (Nat.coprime_one_left R),
    scaled_residue_inter_new_cell a R 2 ha hodd hodd,
    eventMass_scaledEvent a ha, eventMass_scaledEvent a ha]
  unfold signedResidueMoment evenResidueMass
  field_simp [ha0]

theorem new_cell_subset_old_cell (a R : ℕ) (ha : 0 < a)
    (hodd : Nat.Coprime 2 R) :
    gcdCell ((2 * a) * R) (2 * a) ⊆ gcdCell (a * R) a := by
  intro n hn
  have hset : gcdCell ((2 * a) * R) (2 * a) =
      scaledEvent (2 * a) (gcdCell R 1) := by
    simpa only [mul_one] using gcdCell_mul (2 * a) R 1 (by omega)
  rw [hset] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  have hk' : Nat.Coprime k R := Nat.coprime_iff_gcd_eq_one.mpr hk
  change Nat.gcd ((2 * a) * k) (a * R) = a
  have he : (2 * a) * k = a * (2 * k) := by ring
  rw [he, Nat.gcd_mul_left, (hodd.mul_left hk').gcd_eq_one, mul_one]

theorem old_cell_mem_new_space (a R : ℕ) (ha : 0 < a) (hR : 0 < R) :
    eventVector (gcdCell (a * R) a) ∈ cellSpace ((2 * a) * R) := by
  have hL : 0 < a * R := Nat.mul_pos ha hR
  have hM : 0 < (2 * a) * R := by positivity
  have hLM : a * R ∣ (2 * a) * R := ⟨2, by ring⟩
  rw [eventVector_gcdCell_eq_sum (a * R) a hL
    (Nat.mem_divisors.mpr ⟨dvd_mul_right a R, ne_of_gt hL⟩)]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  exact divisor_mem_cell _ d hM ((Nat.dvd_of_mem_divisors hd).trans hLM)

def innovation (a R : ℕ) : QHilbert :=
  eventVector (gcdCell ((2 * a) * R) (2 * a)) -
    (1 / 4 : ℝ) • eventVector (gcdCell (a * R) a)

theorem innovation_mem_new_space (a R : ℕ) (ha : 0 < a) (hR : 0 < R) :
    innovation a R ∈ cellSpace ((2 * a) * R) := by
  apply Submodule.sub_mem
  · exact eventVector_gcdCell_mem _ _ (by positivity)
      (Nat.mem_divisors.mpr ⟨dvd_mul_right (2 * a) R, by positivity⟩)
  · exact Submodule.smul_mem _ _ (old_cell_mem_new_space a R ha hR)

theorem innovation_norm_sq (a R : ℕ) (ha : 0 < a) (hodd : Nat.Coprime 2 R) :
    ‖innovation a R‖ ^ 2 = (3 / 16 : ℝ) *
      eventMass (gcdCell (a * R) a) := by
  have hm : eventMass (gcdCell ((2 * a) * R) (2 * a)) =
      (1 / 4 : ℝ) * eventMass (gcdCell (a * R) a) := by
    have h := gcdCell_refinement_mass a 2 R 1 ha (by omega)
    norm_num at h ⊢
    exact h
  have h := event_innovation_norm_sq _ _ (new_cell_subset_old_cell a R ha hodd)
    (1 / 4 : ℝ) hm
  change ‖innovation a R‖ ^ 2 = _ at h
  rw [h]
  ring

theorem witness_inner_innovation (a R : ℕ) (ha : 0 < a) (hR : 0 < R)
    (hodd : Nat.Coprime 2 R) :
    inner ℝ (witness a R) (innovation a R) = signedResidueMoment R / (a : ℝ) := by
  rw [innovation, inner_sub_right, inner_smul_right,
    witness_inner_new_cell a R ha hodd,
    witness_inner_old_cell a R ha hR hodd _
      (eventVector_gcdCell_mem _ _ (Nat.mul_pos ha hR)
        (Nat.mem_divisors.mpr ⟨dvd_mul_right a R, by positivity⟩)),
    mul_zero, sub_zero]

/-- The newly revealed energy of this explicit old-cell-orthogonal witness
has an absolute lower bound independent of the scaling depth a. -/
theorem witness_revealed_norm_sq_lower (a R : ℕ) (ha : 0 < a) (hR : 3 ≤ R)
    (hodd : Nat.Coprime 2 R) :
    (1 / 147 : ℝ) ≤ ‖conditionalProjection ((2 * a) * R) (witness a R)‖ ^ 2 := by
  let f := conditionalProjection ((2 * a) * R) (witness a R)
  have heta := innovation_mem_new_space a R ha (by omega)
  have hb : |inner ℝ f (innovation a R)| ≤ ‖f‖ * ‖innovation a R‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f (innovation a R)
  have hsq : (inner ℝ f (innovation a R)) ^ 2 ≤ ‖f‖ ^ 2 * ‖innovation a R‖ ^ 2 := by
    have h := sq_le_sq.mpr (show |inner ℝ f (innovation a R)| ≤ |‖f‖ * ‖innovation a R‖| by
      simpa only [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hb)
    simpa only [mul_pow] using h
  have hp : inner ℝ f (innovation a R) = signedResidueMoment R / (a : ℝ) := by
    change inner ℝ (conditionalProjection ((2 * a) * R) (witness a R))
      (innovation a R) = _
    rw [conditional_inner _ _ _ heta, witness_inner_innovation a R ha (by omega) hodd]
  rw [hp] at hsq
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hetaScale : ‖innovation a R‖ ^ 2 * (a : ℝ) ^ 2 =
      (3 / 16 : ℝ) * eventMass (gcdCell R 1) := by
    rw [innovation_norm_sq a R ha hodd]
    have hm := gcdCell_mass_mul a R 1 ha
    simp only [mul_one] at hm
    rw [hm]
    field_simp [ha0]
  have hbScale : (signedResidueMoment R / (a : ℝ)) ^ 2 * (a : ℝ) ^ 2 =
      signedResidueMoment R ^ 2 := by field_simp [ha0]
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (a : ℝ))
  rw [hbScale] at hmul
  have hmul' : signedResidueMoment R ^ 2 ≤
      ‖f‖ ^ 2 * ((3 / 16 : ℝ) * eventMass (gcdCell R 1)) := by
    calc
      _ ≤ (‖f‖ ^ 2 * ‖innovation a R‖ ^ 2) * (a : ℝ) ^ 2 := hmul
      _ = ‖f‖ ^ 2 * (‖innovation a R‖ ^ 2 * (a : ℝ) ^ 2) := by ring
      _ = _ := by rw [hetaScale]
  have hρ := eventMass_le_one (gcdCell R 1)
  have hρf := mul_le_mul_of_nonneg_left hρ (sq_nonneg ‖f‖)
  have hneg := signedResidueMoment_le R hR
  have hbsq : (1 / 784 : ℝ) ≤ signedResidueMoment R ^ 2 := by nlinarith
  change (1 / 147 : ℝ) ≤ ‖f‖ ^ 2
  nlinarith

theorem witness_revealed_relative_lower (a R : ℕ) (ha : 0 < a) (hR : 3 ≤ R)
    (hodd : Nat.Coprime 2 R) :
    (4 / 147 : ℝ) * ‖witness a R‖ ^ 2 ≤
      ‖conditionalProjection ((2 * a) * R) (witness a R)‖ ^ 2 := by
  have h1 := witness_norm_sq_le a R ha
  have h2 := witness_revealed_norm_sq_lower a R ha hR hodd
  nlinarith

end RiemannResearch.RH.QGcdCellObstruction
