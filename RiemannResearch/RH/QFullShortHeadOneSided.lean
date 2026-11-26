/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullShortHeadLocalization
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# One-sided anchored criterion for the actual short-head Schur term

Source: the Verification Desk common-bound obligation, 14 November 2026.
The existing exact fixed-pair limit and full-displacement signed harmonic
rigidity yield a weaker sufficient hypothesis: fix one sign, one positive
residue modulus and one constant, and compare each site only with its
positive residue representative. Good stages may depend on the site.

The bound provider remains open. These declarations prove reductions,
not an unconditional common bound or the Riemann Hypothesis. The full
all-conductor displacement and all signed terms are retained.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullShortHeadOneSided
open ZetaTwoHilbert ZetaTwoProbability QFullDisplacement QFullShortHeadLocalization

theorem harmonicSide_le_of_oneSided_bound (ε C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ε * qSequence displacement n ≤ C) (X : ℕ) :
    harmonicSide ε X ≤ C * (harmonic X : ℝ) := by
  unfold harmonicSide
  calc
    _ ≤ ∑ n ∈ Finset.range (X + 1), C / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      exact div_le_div_of_nonneg_right (max_le (hb n) hC) (Nat.cast_nonneg n)
    _ = C * (harmonic X : ℝ) := by
      rw [Finset.sum_range_succ']
      simp [harmonic, div_eq_mul_inv, Finset.mul_sum]

theorem qResidual_zero_of_oneSided_displacement_bound (ε C : ℝ)
    (hε : |ε| = 1) (hb : ∀ n : ℕ, ε * qSequence displacement n ≤ C) :
    qResidual = 0 := by
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hbD : ∀ n, ε * qSequence displacement n ≤ D :=
    fun n => (hb n).trans (le_max_left _ _)
  have he : ε = 1 ∨ ε = -1 := by
    rcases le_total 0 ε with h | h
    · exact Or.inl (by simpa only [abs_of_nonneg h] using hε)
    · right
      rw [abs_of_nonpos h] at hε
      linarith
  have hlog : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  apply qResidual_zero_of_cofinal_harmonic_polylog 1 (2 * D) (by norm_num)
    (by positivity)
  apply Eventually.frequently
  filter_upwards [hlog] with X hX
  rw [Real.rpow_one]
  have hmin : minimumHarmonicPrefix X ≤ harmonicSide ε X := by
    rcases he with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _
  calc
    minimumHarmonicPrefix X ≤ harmonicSide ε X := hmin
    _ ≤ D * (harmonic X : ℝ) := harmonicSide_le_of_oneSided_bound ε D hD hbD X
    _ ≤ D * (1 + Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) hD
    _ ≤ 2 * D * Real.log (X : ℝ) := by nlinarith

/-- A positive representative of the residue class, in the fixed finite set [L, 2L). -/
def residueAnchor (L n : ℕ) : ℕ := n % L + L

/-- Only one oriented comparison with the representative is needed at each site.
The stage may depend on the site; the sign, modulus and constant are fixed. -/
theorem oneSided_displacement_bound_of_frequent_anchor
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (ε C : ℝ) (hε : |ε| = 1)
    (hSchur : ∀ n : ℕ, 0 < n →
      ∃ᶠ j in atTop, ε * shortSchur R j (H j) n (residueAnchor L n) ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ε * qSequence displacement n ≤ D := by
  let S : ℝ := ∑ r ∈ Finset.range (2 * L), |qSequence displacement r|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨|C| / zetaTwo + S, add_nonneg (div_nonneg (abs_nonneg _) zetaTwo_pos.le) hS, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    rw [qSequence_zero, mul_zero]
    exact add_nonneg (div_nonneg (abs_nonneg _) zetaTwo_pos.le) hS
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  have ha : residueAnchor L n < 2 * L := by
    dsimp [residueAnchor]
    have := Nat.mod_lt n hL
    omega
  have has : |qSequence displacement (residueAnchor L n)| ≤ S :=
    Finset.single_le_sum (fun r _ => abs_nonneg (qSequence displacement r))
      (Finset.mem_range.mpr ha)
  have hanchor : ε * qSequence displacement (residueAnchor L n) ≤ S := by
    calc
      _ ≤ |ε * qSequence displacement (residueAnchor L n)| := le_abs_self _
      _ = |qSequence displacement (residueAnchor L n)| := by
        rw [abs_mul, hε, one_mul]
      _ ≤ S := has
  have hb := le_of_tendsto_of_frequently
    ((shortSchur_tendsto R hnest hcofinal H hH n (residueAnchor L n)).const_mul ε)
    (hSchur n hnp)
  have hscaled : zetaTwo * (ε * qSequence displacement n -
      ε * qSequence displacement (residueAnchor L n)) ≤ |C| := by
    calc
      _ = ε * (zetaTwo * (qSequence displacement n -
          qSequence displacement (residueAnchor L n))) := by ring
      _ ≤ C := hb
      _ ≤ |C| := le_abs_self C
  have hdiff : ε * qSequence displacement n -
      ε * qSequence displacement (residueAnchor L n) ≤ |C| / zetaTwo :=
    (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
  linarith

/-- Conditional reduction: a single sign and one anchor per residue class suffice.
No arithmetic provider for the common bound is asserted here. -/
theorem qResidual_zero_of_frequent_oneSided_anchor
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (ε C : ℝ) (hε : |ε| = 1)
    (hSchur : ∀ n : ℕ, 0 < n →
      ∃ᶠ j in atTop, ε * shortSchur R j (H j) n (residueAnchor L n) ≤ C) :
    qResidual = 0 := by
  obtain ⟨D, _, hD⟩ := oneSided_displacement_bound_of_frequent_anchor
    R hnest hcofinal H hH L hL ε C hε hSchur
  exact qResidual_zero_of_oneSided_displacement_bound ε D hε hD

/-- The original two-sided pair condition follows with every positive bound,
once the still-open one-sided anchored hypothesis is supplied. -/
theorem eventually_abs_shortSchur_le_of_frequent_oneSided_anchor
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (ε C : ℝ) (hε : |ε| = 1)
    (hSchur : ∀ n : ℕ, 0 < n →
      ∃ᶠ j in atTop, ε * shortSchur R j (H j) n (residueAnchor L n) ≤ C)
    (c : ℝ) (hc : 0 < c) (n m : ℕ) :
    ∀ᶠ j in atTop, |shortSchur R j (H j) n m| ≤ c := by
  have hr := qResidual_zero_of_frequent_oneSided_anchor
    R hnest hcofinal H hH L hL ε C hε hSchur
  have ht := (shortSchur_tendsto R hnest hcofinal H hH n m).abs
  rw [displacement_eq_zero_of_qResidual_eq_zero hr] at ht
  simp only [show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear,
    Pi.zero_apply, sub_self, mul_zero, abs_zero] at ht
  exact (ht.eventually_lt_const hc).mono (fun _ h => h.le)

/-- Checked implication to Mathlib's RH. The common one-sided bound is open. -/
theorem riemannHypothesis_of_frequent_oneSided_anchor
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (ε C : ℝ) (hε : |ε| = 1)
    (hSchur : ∀ n : ℕ, 0 < n →
      ∃ᶠ j in atTop, ε * shortSchur R j (H j) n (residueAnchor L n) ≤ C) :
    RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp (qResidual_zero_of_frequent_oneSided_anchor
      R hnest hcofinal H hH L hL ε C hε hSchur))


/-- For each fixed sign and positive modulus the one-sided anchored criterion
is equivalent to zero residual. This is an equivalence, not a bound provider. -/
theorem qResidual_zero_iff_frequent_oneSided_anchor
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : |ε| = 1) :
    qResidual = 0 ↔ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      ∃ᶠ j in atTop, ε * shortSchur R j (H j) n (residueAnchor L n) ≤ C := by
  constructor
  · intro hr
    refine ⟨1, ?_⟩
    intro n _
    have ht := (shortSchur_tendsto R hnest hcofinal H hH n (residueAnchor L n)).const_mul ε
    rw [displacement_eq_zero_of_qResidual_eq_zero hr] at ht
    simp only [show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear,
      Pi.zero_apply, sub_self, mul_zero] at ht
    exact ((ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono
      (fun _ h => h.le)).frequently
  · rintro ⟨C, hC⟩
    exact qResidual_zero_of_frequent_oneSided_anchor R hnest hcofinal H hH L hL ε C hε hC


/-- At modulus one a single fixed anchor, the physical site 1, suffices.
Either fixed orientation may be used, but its choice cannot depend on n. -/
theorem riemannHypothesis_of_frequent_oneSided_fixed_anchor
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (ε C : ℝ) (hε : |ε| = 1)
    (hSchur : ∀ n : ℕ, 0 < n →
      ∃ᶠ j in atTop, ε * shortSchur R j (H j) n 1 ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequent_oneSided_anchor
    R hnest hcofinal H hH 1 (by norm_num) ε C hε
  simpa only [residueAnchor, Nat.mod_one, zero_add] using hSchur

/-- The zero-index evaluation is the zero functional. At a fixed positive head,
these normalized sums therefore converge to the two actual displacement charges. -/
def shortSchurHarmonicSide (R : ℕ → ℕ+) (j H X : ℕ) (ε : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), max (ε * (shortSchur R j H n 0 / zetaTwo)) 0 / (n : ℝ)

theorem shortSchurHarmonicSide_tendsto
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (X : ℕ) (ε : ℝ) :
    Tendsto (fun j => shortSchurHarmonicSide R j (H j) X ε) atTop
      (𝓝 (harmonicSide ε X)) := by
  unfold shortSchurHarmonicSide harmonicSide
  apply tendsto_finsetSum
  intro n _
  have ht := (shortSchur_tendsto R hnest hcofinal H hH n 0).div_const zetaTwo
  have hnorm : Tendsto (fun j => shortSchur R j (H j) n 0 / zetaTwo) atTop
      (𝓝 (qSequence displacement n)) := by
    have hc : zetaTwo * (qSequence displacement n - qSequence displacement 0) /
        zetaTwo = qSequence displacement n := by
      rw [qSequence_zero, sub_zero]
      field_simp [zetaTwo_pos.ne'] <;> ring
    rwa [hc] at ht
  exact (((hnorm.const_mul ε).max tendsto_const_nhds).div_const (n : ℝ))

/-- Both the orientation and the good stages may depend on the harmonic head.
Only a cofinal set of heads needs a polylogarithmic signed aggregate. -/
theorem qResidual_zero_iff_cofinal_shortSchurHarmonic
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    qResidual = 0 ↔ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∃ᶠ X : ℕ in atTop,
      ∃ᶠ j : ℕ in atTop,
        min (shortSchurHarmonicSide R j (H j) X 1)
          (shortSchurHarmonicSide R j (H j) X (-1)) ≤ C * (Real.log (X : ℝ)) ^ B := by
  have hlim (X : ℕ) : Tendsto (fun j =>
      min (shortSchurHarmonicSide R j (H j) X 1)
        (shortSchurHarmonicSide R j (H j) X (-1))) atTop (𝓝 (minimumHarmonicPrefix X)) :=
    (shortSchurHarmonicSide_tendsto R hnest hcofinal H hH X 1).min
      (shortSchurHarmonicSide_tendsto R hnest hcofinal H hH X (-1))
  constructor
  · intro hr
    refine ⟨0, 1, le_rfl, zero_le_one, (Eventually.of_forall ?_).frequently⟩
    intro X
    have h := hlim X
    have hz : minimumHarmonicPrefix X = 0 := by
      simp [minimumHarmonicPrefix, harmonicSide, displacement_eq_zero_of_qResidual_eq_zero hr,
        show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]
    rw [hz] at h
    simpa only [Real.rpow_zero, mul_one] using
      ((h.eventually_lt_const zero_lt_one).mono fun _ hlt => hlt.le).frequently
  · rintro ⟨B, C, hB, hC, hgood⟩
    exact qResidual_zero_of_cofinal_harmonic_polylog B C hB hC
      (hgood.mono fun X hX => le_of_tendsto_of_frequently (hlim X) hX)

end RiemannResearch.RH.QFullShortHeadOneSided
