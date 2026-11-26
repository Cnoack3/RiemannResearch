import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import RiemannResearch.RH.ScreenedSectionDescent

/-! # Computing the screened Pareto energy from gcd-class characters

The Gram matrices use the complete digamma progression mass. The signed
character sums are evaluated before taking any products or squared norms.
The missing mixed modes give the exact remainder for each finite upper bound.
For the signed two-prime pairing, a finite character section plus the
Cauchy--Schwarz allowance for its exact residual gives a rigorous RH certificate.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy
open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.PrimePowerSchur
open MixedConductorBasis DigammaParseval CenteredMeanSnake.DigammaSection
open ParetoPacketCharacters

/-- Complete Pareto Gram from both gcd-class character expansions. -/
def characterGram (a b : ℕ) : ℝ :=
  ∑ r : Fin (a.lcm b), digammaWeight (a.lcm b) (r.val+1) *
    (characterPacket a (r.val+1) * characterPacket b (r.val+1))

theorem characterGram_eq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    characterGram a b = packetGramEntry a b := by
  simp only [characterGram, characterPacket_eq a _ ha, characterPacket_eq b _ hb,
    packetGramEntry_eq_weighted a b ha hb]

/-- Orthogonal mixed-conductor row computed entirely from the character Grams. -/
def characterRow (q : Index) : ℕ → ℝ :=
  let prev (r : Finset.Iio q) : ℕ → ℝ := characterRow r.val
  fun a => (characterGram q.val a - ∑ r : Finset.Iio q, prev r q.val * prev r a) /
    Real.sqrt (characterGram q.val q.val - ∑ r : Finset.Iio q, (prev r q.val)^2)
termination_by q.val
decreasing_by exact (show r.val < q from Finset.mem_Iio.mp r.property)

theorem characterRow_eq (q : Index) : ∀ a : ℕ, 0 < a → characterRow q a = digammaRow q a := by
  induction q using (measure (fun q : Index => q.val)).wf.induction with
  | h q ih =>
    intro a ha
    have hq : 0 < q.val := by have := q.property.1; omega
    have hp (r : Finset.Iio q) (k : ℕ) (hk : 0 < k) : characterRow r.val k = digammaRow r.val k :=
      ih r.val (show r.val < q from Finset.mem_Iio.mp r.property) k hk
    rw [characterRow, digammaRow]
    simp only [characterGram_eq _ _ hq ha, characterGram_eq _ _ hq hq, hp _ _ hq, hp _ _ ha]

/-- Finite orthogonal section computed from the character-Cholesky rows. -/
def partialSection (s : Finset Index) (a : ℕ) : mixedClosure :=
  ∑ q ∈ s, characterRow q a • basis q

/-- Signed finite cross pairing.  Its summands must not be discarded. -/
def crossPartial (s : Finset Index) (a b : ℕ) : ℝ :=
  ∑ q ∈ s, characterRow q a * characterRow q b

/-- Captured energy of one packet in a finite character section. -/
def energyPartial (s : Finset Index) (a : ℕ) : ℝ :=
  ∑ q ∈ s, (characterRow q a)^2

private theorem basis_inner_partialSection (s : Finset Index) (a : ℕ) (q : Index) :
    inner ℝ (basis q : mixedClosure) (partialSection s a : mixedClosure) =
      if q ∈ s then characterRow q a else 0 := by
  rw [partialSection, inner_sum]
  have ho := orthonormal_iff_ite.mp basis.orthonormal
  simp_rw [real_inner_smul_right, ho]
  simp

theorem partialSection_inner (s : Finset Index) (a b : ℕ) :
    inner ℝ (partialSection s a : mixedClosure) (partialSection s b : mixedClosure) =
      crossPartial s a b := by
  rw [partialSection, sum_inner, crossPartial]
  apply Finset.sum_congr rfl
  intro q hq
  rw [real_inner_smul_left, basis_inner_partialSection s b q, if_pos hq]

theorem partialSection_norm_sq (s : Finset Index) (a : ℕ) :
    ‖partialSection s a‖^2 = energyPartial s a := by
  rw [← real_inner_self_eq_norm_sq, partialSection_inner, energyPartial, crossPartial]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem basis_inner_packetProjection (q : Index) (a : ℕ) (ha : 0 < a) :
    inner ℝ (basis q : mixedClosure)
      (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert a)) =
        characterRow q a := by
  rw [← HilbertBasis.repr_apply_apply, packet_row_coefficient q a ha]
  exact (characterRow_eq q a ha).symm

theorem packetProjection_inner_partialSection (s : Finset Index)
    (a b : ℕ) (ha : 0 < a) :
    inner ℝ (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert a))
      (partialSection s b) = crossPartial s a b := by
  rw [partialSection, inner_sum, crossPartial]
  apply Finset.sum_congr rfl
  intro q _
  rw [real_inner_smul_right, real_inner_comm,
    basis_inner_packetProjection q a ha]
  ring

theorem crossPartial_comm (s : Finset Index) (a b : ℕ) :
    crossPartial s a b = crossPartial s b a := by
  unfold crossPartial
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The complete signed character series is the desired reverse mixed pairing. -/
theorem character_cross_series :
    (∑' q : Index, characterRow q 2 * characterRow q 3) =
      inner ℝ (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2))
        (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)) := by
  rw [← packet_row_covariance 2 3 (by decide) (by decide)]
  apply tsum_congr
  intro q
  rw [characterRow_eq q 2 (by decide), characterRow_eq q 3 (by decide)]

/-- Exact signed remainder after any finite family of character modes. -/
theorem packetProjection_cross_eq_partial_add_remainder (s : Finset Index) :
    let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
    let y := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)
    inner ℝ x y = crossPartial s 2 3 +
      inner ℝ (x - partialSection s 2) (y - partialSection s 3) := by
  dsimp only
  have hy :
      inner ℝ (partialSection s 2)
        (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)) =
          crossPartial s 2 3 := by
    rw [real_inner_comm, packetProjection_inner_partialSection s 3 2 (by decide),
      crossPartial_comm s 3 2]
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    packetProjection_inner_partialSection s 2 3 (by decide),
    hy, partialSection_inner]
  ring

/-- Exact residual energy of a finite character section. -/
theorem packetProjection_residual_norm_sq (s : Finset Index) (a : ℕ) (ha : 0 < a) :
    let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert a)
    ‖x - partialSection s a‖^2 = ‖x‖^2 - energyPartial s a := by
  dsimp only
  rw [norm_sub_sq_real, packetProjection_inner_partialSection s a a ha,
    partialSection_norm_sq, crossPartial, energyPartial]
  ring

/-- A finite signed character calculation proves RH once its captured cross
pairing dominates the exact two-prime target plus the Cauchy allowance for the
two residual tails.  In particular, a positive or nearly sufficient partial
sum is not by itself a certificate: the signed remainder is retained. -/
theorem riemannHypothesis_of_character_cross_certificate (s : Finset Index)
    (h :
      Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) -
          Real.log 2 * Real.log 3 +
          ‖mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2) -
              partialSection s 2‖ *
            ‖mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3) -
              partialSection s 3‖ ≤
        crossPartial s 2 3) :
    RiemannHypothesis := by
  let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
  let y := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3)
  let r₂ := x - partialSection s 2
  let r₃ := y - partialSection s 3
  have hcs := abs_real_inner_le_norm r₂ r₃
  have hlow : -(‖r₂‖ * ‖r₃‖) ≤ inner ℝ r₂ r₃ :=
    (neg_le_neg hcs).trans (neg_abs_le _)
  have hsplit := packetProjection_cross_eq_partial_add_remainder s
  apply riemannHypothesis_of_two_three_projected_covariance
  change Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) -
      Real.log 2 * Real.log 3 ≤ inner ℝ x y
  dsimp only [x, y, r₂, r₃] at hlow h
  linarith

def capturedMode (q : Index) : ℝ := (characterRow q 2)^2

private theorem mode_eq (q : Index) : capturedMode q = (digammaRow q 2)^2 := by
  rw [capturedMode, characterRow_eq _ _ (by decide)]

theorem capturedMode_summable : Summable capturedMode := by
  simpa only [funext mode_eq] using hasSum_parity_energy.summable

theorem character_section_balance :
    (∑' q : Index, capturedMode q) + (Real.log 2)^2 *
      inner ℝ normalizedScreenedTwo normalizedScreenedTwo = Real.log 2 := by
  simpa only [funext mode_eq] using ScreenedSectionDescent.digamma_section_energy

private theorem log_sq_pos : 0 < (Real.log 2)^2 := by positivity

/-- Exact value of the scalar as a convergent character-Gram series. -/
theorem character_section_energy :
    inner ℝ normalizedScreenedTwo normalizedScreenedTwo =
      (Real.log 2 - ∑' q : Index, capturedMode q) / (Real.log 2)^2 := by
  apply (eq_div_iff log_sq_pos.ne').mpr
  linarith only [character_section_balance,
    mul_comm (inner ℝ normalizedScreenedTwo normalizedScreenedTwo) ((Real.log 2)^2)]

def upper (s : Finset Index) : ℝ :=
  (Real.log 2 - ∑ q ∈ s, capturedMode q) / (Real.log 2)^2

/-- Every omitted mode is retained with its exact sign and weight. -/
theorem upper_eq_section_add_tail (s : Finset Index) :
    upper s = inner ℝ normalizedScreenedTwo normalizedScreenedTwo +
      (∑' q : ↥(s : Set Index)ᶜ, capturedMode q) / (Real.log 2)^2 := by
  have h : (∑ q ∈ s, capturedMode q) + (∑' q : ↥(s : Set Index)ᶜ, capturedMode q) =
      ∑' q : Index, capturedMode q := capturedMode_summable.sum_add_tsum_compl
  rw [upper, character_section_energy, ← add_div, ← h]
  ring

theorem certified_interval (s : Finset Index) :
    1 ≤ inner ℝ normalizedScreenedTwo normalizedScreenedTwo ∧
      inner ℝ normalizedScreenedTwo normalizedScreenedTwo ≤ upper s := by
  constructor
  · rw [real_inner_self_eq_norm_sq]
    nlinarith [one_le_norm_normalizedScreenedTwo]
  · rw [upper_eq_section_add_tail]
    exact le_add_of_nonneg_right (div_nonneg (tsum_nonneg fun q => sq_nonneg _) log_sq_pos.le)

theorem upper_antitone : Antitone upper := by
  intro s t h
  apply div_le_div_of_nonneg_right _ log_sq_pos.le
  exact sub_le_sub_left (Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => sq_nonneg _)) _

theorem upper_tendsto :
    Tendsto upper atTop (𝓝 (inner ℝ normalizedScreenedTwo normalizedScreenedTwo)) := by
  rw [character_section_energy]
  have h : Tendsto (fun s : Finset Index => ∑ q ∈ s, capturedMode q) atTop
      (𝓝 (∑' q : Index, capturedMode q)) := capturedMode_summable.hasSum
  exact (h.const_sub _).div_const _

/-- The actual two-mode estimate, with the ten row orthogonalized against six. -/
theorem six_ten_upper :
    upper {six, ten} =
      (Real.log 2 - ((Real.log 2 - Real.pi / (2 * Real.sqrt 3))^2 / (Real.pi / Real.sqrt 3) +
        (characterGram 10 2 - characterGram 6 10 * characterGram 6 2 / characterGram 6 6)^2 /
        (characterGram 10 10 - (characterGram 6 10)^2 / characterGram 6 6))) / (Real.log 2)^2 := by
  have hne : six ≠ ten := by
    intro h
    have h' := congrArg Subtype.val h
    exact (by decide : (6 : ℕ) ≠ 10) h'
  simp only [upper, Finset.sum_insert (by simpa using hne : six ∉ ({ten} : Finset Index)),
    Finset.sum_singleton, mode_eq, first_digamma_term, second_digamma_term,
    characterGram_eq _ _ (by decide : 0 < 10) (by decide : 0 < 2),
    characterGram_eq _ _ (by decide : 0 < 6) (by decide : 0 < 10),
    characterGram_eq _ _ (by decide : 0 < 6) (by decide : 0 < 2),
    characterGram_eq _ _ (by decide : 0 < 6) (by decide : 0 < 6),
    characterGram_eq _ _ (by decide : 0 < 10) (by decide : 0 < 10)]

/-- The remaining estimate is an arbitrary-precision finite upper certificate. -/
theorem rh_iff_character_certificates :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ s : Finset Index, upper s < 1 + ε := by
  rw [← ScreenedSectionDescent.inner_self_eq_one_iff_rh]
  constructor
  · intro h ε hε
    exact ((tendsto_order.mp (h ▸ upper_tendsto)).2 _ (by linarith)).exists
  · intro h
    have hl := (certified_interval ∅).1
    by_contra hn
    have hp : 0 < (inner ℝ normalizedScreenedTwo normalizedScreenedTwo - 1)/2 := by
      have := lt_of_le_of_ne hl (Ne.symm hn)
      linarith
    obtain ⟨s,hs⟩ := h _ hp
    linarith [(certified_interval s).2]

#print axioms character_cross_series
#print axioms packetProjection_cross_eq_partial_add_remainder
#print axioms riemannHypothesis_of_character_cross_certificate

end RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy
