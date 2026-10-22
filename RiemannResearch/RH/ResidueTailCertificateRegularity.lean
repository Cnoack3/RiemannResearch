import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ResidueTailCertificate
import RiemannResearch.RH.ParetoFirstMomentUniqueness

/-!
# First-moment and sign obstructions for actual residue tail certificates

Source: user-provided `RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 15--16, for the certificate and regularity obstruction. The checked
first-moment uniqueness theorem is reused through its finite-sieve/dyadic-tail
proof. We additionally specialize the existing sign-rigidity theorem: any
actual certificate has both signs arbitrarily far out. Hilbert membership does
not imply the excluded first-moment condition. These are obstructions to a
regular certificate, not a proof excluding every Hilbert certificate.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- Orthogonality to every normalized residue gives an actual physical legal
annihilator. No density assertion or external provider is needed. -/
theorem legalAnnihilator_of_normalizedResidue_orthogonal (h : ThresholdHilbert)
    (horth : ∀ (d : ℕ) (hd : 1 < d),
      inner ℝ h (normalizedResidueHilbert d (by omega)) = 0) :
    LegalAnnihilator {n : ℕ | 0 < n} (hilbertSequence h) := by
  have ho (d : ℕ) (hd : 0 < d) :
      inner ℝ h (normalizedResidueHilbert d hd) = 0 := by
    by_cases hd1 : d = 1
    · subst d
      have hz : normalizedResidueHilbert 1 hd = 0 := by
        apply hilbertSequence_injective
        rw [normalizedResidueHilbert_sequence]
        funext k
        cases k <;> simp [residueFraction, hilbertSequence, Nat.mod_one]
      rw [hz, inner_zero_right]
    · exact horth d (by omega)
  refine ⟨hilbertSequence_square_summable h, ?_⟩
  intro f hf
  have hex : ∃ g : ThresholdHilbert, hilbertSequence g = f ∧ inner ℝ h g = 0 := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨n, hn, m, hm, rfl⟩ := hf
      change 0 < n at hn
      refine ⟨((m * n : ℕ) : ℝ) • normalizedResidueHilbert (m * n) (by positivity) -
        (m : ℝ) • normalizedResidueHilbert m hm, ?_, ?_⟩
      · rw [hilbertSequence_sub, hilbertSequence_smul, hilbertSequence_smul,
          normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]
        funext k
        rw [residue_mul_floor]
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hm0 : (m : ℝ) ≠ 0 := by positivity
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, residueFraction, residue,
          Nat.cast_mul]
        field_simp
        <;> ring
      · rw [inner_sub_right, inner_smul_right, inner_smul_right, ho, ho,
          mul_zero, mul_zero, sub_self]
    | zero =>
      refine ⟨0, ?_, inner_zero_right _⟩
      exact hilbertSequenceLinear.map_zero
    | add x y hx hy ihx ihy =>
      obtain ⟨gx, hgx, hox⟩ := ihx
      obtain ⟨gy, hgy, hoy⟩ := ihy
      refine ⟨gx + gy, ?_, ?_⟩
      · change hilbertSequenceLinear (gx + gy) = x + y
        rw [map_add]
        change hilbertSequence gx + hilbertSequence gy = x + y
        rw [hgx, hgy]
      · rw [inner_add_right, hox, hoy, add_zero]
    | smul c x hx ih =>
      obtain ⟨gx, hgx, hox⟩ := ih
      refine ⟨c • gx, ?_, ?_⟩
      · change hilbertSequenceLinear (c • gx) = c • x
        rw [map_smul]
        change c • hilbertSequence gx = c • x
        rw [hgx]
      · rw [inner_smul_right, hox, mul_zero]
  obtain ⟨g, hg, ho⟩ := hex
  rw [← hg, ← hilbert_inner_weighted]
  exact ho

/-- Existing first-moment rigidity specialized to the full residue dictionary. -/
theorem normalizedResidue_orthogonal_eq_zero_of_firstMoment (h : ThresholdHilbert)
    (horth : ∀ (d : ℕ) (hd : 1 < d),
      inner ℝ h (normalizedResidueHilbert d (by omega)) = 0)
    (hm : Summable (fun n : ℕ => |hilbertSequence h n| / ((n : ℝ) + 1))) :
    h = 0 := by
  have ha := legalAnnihilator_of_normalizedResidue_orthogonal h horth
  apply hilbertSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    have hz := legalAnnihilator_eq_zero_of_first_absolute_moment
      (show 2 ∈ {n : ℕ | 0 < n} by norm_num) ha hm (Nat.succ_pos n)
    simpa [hilbertSequence] using hz

theorem tailCertificateAnnihilator_legal (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    LegalAnnihilator {n : ℕ | 0 < n}
      (hilbertSequence (tailCertificateAnnihilator z)) :=
  legalAnnihilator_of_normalizedResidue_orthogonal _
    (tailCertificateAnnihilator_orthogonal z hz)

/-- Section 16.1: a certificate cannot have an absolutely summable first moment.
This regularity condition is strictly additional to its Hilbert membership. -/
theorem tailCertificate_not_summable_firstMoment (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    ¬ Summable (fun n : ℕ => |hilbertSequence z n| / ((n : ℝ) + 1)) := by
  intro hm
  have hm' : Summable (fun n : ℕ =>
      |hilbertSequence (tailCertificateAnnihilator z) n| / ((n : ℝ) + 1)) := by
    apply (summable_nat_add_iff 2).mp
    have hs := (summable_nat_add_iff 2).mpr hm
    convert hs using 1
    funext n
    rw [tailCertificateAnnihilator_tail z (n + 2) (by omega)]
  have heq := normalizedResidue_orthogonal_eq_zero_of_firstMoment
    (tailCertificateAnnihilator z) (tailCertificateAnnihilator_orthogonal z hz) hm'
  have hfirst := tailCertificateAnnihilator_first z hz
  rw [heq] at hfirst
  simpa [hilbertSequence] using hfirst

/-- Stronger than simply requiring both signs: each sign occurs arbitrarily
far into the tail. The conclusion follows from the existing legal-annihilator
sign rigidity, so no absolute first-moment assumption is required. -/
theorem tailCertificate_both_signs_arbitrarily_far (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (N : ℕ) :
    (∃ k, N ≤ k ∧ 2 ≤ k ∧ 0 < hilbertSequence z k) ∧
      (∃ k, N ≤ k ∧ 2 ≤ k ∧ hilbertSequence z k < 0) := by
  have hn : hilbertSequence (tailCertificateAnnihilator z) 1 ≠ 0 := by
    rw [tailCertificateAnnihilator_first z hz]
    norm_num
  have hs := legalAnnihilator_both_signs_arbitrarily_far
    (show 2 ∈ {n : ℕ | 0 < n} by norm_num)
    (tailCertificateAnnihilator_legal z hz) (by norm_num : 0 < 1) hn (max N 2)
  rcases hs with ⟨⟨k, hk, hkpos⟩, ⟨j, hj, hjneg⟩⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right N 2) hk
  have hj2 : 2 ≤ j := le_trans (le_max_right N 2) hj
  rw [tailCertificateAnnihilator_tail z k hk2] at hkpos
  rw [tailCertificateAnnihilator_tail z j hj2] at hjneg
  exact ⟨⟨k, le_trans (le_max_left N 2) hk, hk2, hkpos⟩,
    ⟨j, le_trans (le_max_left N 2) hj, hj2, hjneg⟩⟩

/-- Source: user-provided continuation, Section 26.1. The general summable-tail
rigidity theorem is already established in ParetoSummableTailRigidity. -/
theorem normalizedResidue_orthogonal_eq_zero_of_summable_signedTail
    (h : ThresholdHilbert)
    (horth : ∀ (d : ℕ) (hd : 1 < d),
      inner ℝ h (normalizedResidueHilbert d (by omega)) = 0)
    (hA : Summable (anchoredSignedTail (hilbertSequence h))) : h = 0 := by
  apply hilbertSequence_injective
  have hz := legalAnnihilator_anchored_eq_zero_of_summable_signedTail
    (show 2 ∈ {n : ℕ | 0 < n} by norm_num)
    (legalAnnihilator_of_normalizedResidue_orthogonal h horth) hA
    (hilbertSequence_zero h)
  exact hz.trans (hilbertSequenceLinear.map_zero).symm

/-- Altering the first coordinate leaves every primitive starting at n ≥ 2 unchanged. -/
theorem tailCertificateAnnihilator_signedTail (z : ThresholdHilbert)
    (n : ℕ) (hn : 2 ≤ n) :
    anchoredSignedTail (hilbertSequence (tailCertificateAnnihilator z)) n =
      anchoredSignedTail (hilbertSequence z) n := by
  rw [anchoredSignedTail_pos _ (by omega), anchoredSignedTail_pos _ (by omega)]
  unfold signedTail
  apply tsum_congr
  intro j
  unfold signedCoefficient
  rw [tailCertificateAnnihilator_tail z (j + n) (by omega)]

/-- Section 26.1 specialized to the actual reciprocal-source tail certificate.
Unlike the earlier absolute first moment, this allows cancellation inside each tail. -/
theorem tailCertificate_not_summable_signedTail (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    ¬ Summable (anchoredSignedTail (hilbertSequence z)) := by
  intro hA
  have hA' : Summable (anchoredSignedTail
      (hilbertSequence (tailCertificateAnnihilator z))) := by
    apply (summable_nat_add_iff 2).mp
    have hs := (summable_nat_add_iff 2).mpr hA
    convert hs using 1
    funext n
    exact tailCertificateAnnihilator_signedTail z (n + 2) (by omega)
  have heq := normalizedResidue_orthogonal_eq_zero_of_summable_signedTail
    (tailCertificateAnnihilator z) (tailCertificateAnnihilator_orthogonal z hz) hA'
  have hfirst := tailCertificateAnnihilator_first z hz
  rw [heq] at hfirst
  simp [hilbertSequence] at hfirst

end RiemannResearch.RH.Pareto
