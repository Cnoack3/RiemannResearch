import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import RiemannResearch.RH.ScreenedSectionDescent

/-! # Computing the screened Pareto energy from gcd-class characters

The Gram matrices use the complete digamma progression mass. The signed
character sums are evaluated before taking any products or squared norms.
The missing mixed modes give the exact remainder for each finite upper bound.
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

end RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy
