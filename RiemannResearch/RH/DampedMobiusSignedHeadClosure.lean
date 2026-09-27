import RiemannResearch.RH.DampedMobiusSignedGram
import RiemannResearch.RH.DampedMobiusEnergyClosure

/-!
# Exact finite-head signed criterion for fixed positive damping

The finite Gram expansion is elementary bilinear algebra. The arithmetic
input to the coordinate limit is the existing absolutely convergent scalar
Möbius Dirichlet series, not absolute convergence of the Hilbert series.
The new equivalence isolates the signed off-diagonal bound and does not
provide that bound. Burnol, arXiv:math/0202166, Section 4 supplies the
finite-energy application; no novelty claim is made for these reductions.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

def paretoHeadPairing (H : ℕ) (f g : ThresholdHilbert) : ℝ :=
  ∑ n ∈ Finset.range H, positiveWeight n * hilbertSequence f n * hilbertSequence g n

theorem paretoHeadPairing_self_nonneg (H : ℕ) (f : ThresholdHilbert) :
    0 ≤ paretoHeadPairing H f f := by
  apply Finset.sum_nonneg
  intro n hn
  simpa only [mul_assoc, ← pow_two] using
    mul_nonneg (positiveWeight_nonneg n) (sq_nonneg (hilbertSequence f n))

theorem paretoHeadPairing_self_le (H : ℕ) (f : ThresholdHilbert) :
    paretoHeadPairing H f f ≤ ‖f‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  simpa only [paretoHeadPairing, mul_assoc, ← pow_two] using
    Summable.sum_le_tsum (Finset.range H)
      (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
      (hilbertSequence_square_summable f)

def dampedMobiusHeadDiagonal (ε : ℝ) (H M : ℕ) : ℝ :=
  ∑ d ∈ Finset.range M, paretoHeadPairing H
    (arithmeticResidueTerm (dampedMobiusWeight ε) d)
    (arithmeticResidueTerm (dampedMobiusWeight ε) d)

/-- Both orientations are included. No absolute values occur. -/
def dampedMobiusHeadOffDiagonal (ε : ℝ) (H M : ℕ) : ℝ :=
  ∑ d ∈ Finset.range M, ∑ e ∈ (Finset.range M).erase d,
    paretoHeadPairing H (arithmeticResidueTerm (dampedMobiusWeight ε) d)
      (arithmeticResidueTerm (dampedMobiusWeight ε) e)

theorem dampedMobiusHeadDiagonal_nonneg (ε : ℝ) (H M : ℕ) :
    0 ≤ dampedMobiusHeadDiagonal ε H M :=
  Finset.sum_nonneg (fun _ _ => paretoHeadPairing_self_nonneg H _)

theorem dampedMobiusHeadDiagonal_le {ε : ℝ} (hε : 0 < ε) (H M : ℕ) :
    dampedMobiusHeadDiagonal ε H M ≤ dampedMobiusDiagonalBudget ε := by
  exact (Finset.sum_le_sum (fun d _ => paretoHeadPairing_self_le H
    (arithmeticResidueTerm (dampedMobiusWeight ε) d))).trans
      (dampedMobiusGramDiagonal_le hε M)

private theorem partial_head_expansion (w : ℕ → ℝ) (H M : ℕ) :
    paretoHeadPairing H (arithmeticFloorHilbertPartial w M)
      (arithmeticFloorHilbertPartial w M) =
      ∑ d ∈ Finset.range M, ∑ e ∈ Finset.range M,
        paretoHeadPairing H (arithmeticResidueTerm w d) (arithmeticResidueTerm w e) := by
  have hc (n : ℕ) : hilbertSequence (arithmeticFloorHilbertPartial w M) n =
      -(∑ d ∈ Finset.range M, hilbertSequence (arithmeticResidueTerm w d) n) := by
    change hilbertSequenceLinear (-(∑ d ∈ Finset.range M, arithmeticResidueTerm w d)) n = _
    simp only [map_neg, map_sum, Pi.neg_apply, Finset.sum_apply]
    rfl
  unfold paretoHeadPairing
  simp_rw [hc, mul_neg, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem dampedMobius_partial_head_eq_signed (ε : ℝ) (H M : ℕ) :
    paretoHeadPairing H (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M) =
      dampedMobiusHeadDiagonal ε H M + dampedMobiusHeadOffDiagonal ε H M := by
  rw [partial_head_expansion]
  unfold dampedMobiusHeadDiagonal dampedMobiusHeadOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_erase_add _ (fun e => paretoHeadPairing H
    (arithmeticResidueTerm (dampedMobiusWeight ε) d)
    (arithmeticResidueTerm (dampedMobiusWeight ε) e)) hd]
  ring

theorem dampedMobius_density_hasSum {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun m : ℕ => dampedMobiusWeight ε (m+1) / ((m+1 : ℕ) : ℝ))
      (1 / riemannZeta (1 + (ε : ℂ))).re := by
  have hs := dampedMobiusWeight_LSeriesHasSum (ε := ε) (s := 1) (by simpa using hε)
  change HasSum (LSeries.term (fun n => (dampedMobiusWeight ε n : ℂ)) 1) _ at hs
  have hc : HasSum (fun n : ℕ => ((dampedMobiusWeight ε n / (n : ℝ) : ℝ) : ℂ))
      (riemannZeta (1 + (ε : ℂ)))⁻¹ := by
    convert hs using 1
    funext n
    by_cases hn : n = 0
    · simp [hn, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      simp
  apply (hasSum_nat_add_iff
    (f := fun n : ℕ => dampedMobiusWeight ε n / (n : ℝ)) 1).mpr
  simpa only [Finset.sum_range_one, dampedMobiusWeight_zero, Nat.cast_zero,
    zero_div, zero_add, add_zero, Complex.ofReal_re, one_div] using Complex.hasSum_re hc

/-- Scalar coordinate convergence holds throughout ε>0, independently of
whether the infinite arithmetic vector has finite energy. -/
theorem dampedMobius_partial_coordinate_tendsto {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Tendsto (fun M => hilbertSequence
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M) n) atTop
      (𝓝 (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)) := by
  have ht := (tendsto_const_nhds (x := dampedMobiusPrefix ε n)
    (f := (atTop : Filter ℕ))).sub
    ((dampedMobius_density_hasSum hε).tendsto_sum_nat.const_mul (n : ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop n] with M hM
  exact (arithmeticFloorHilbertPartial_sequence_of_le (dampedMobiusWeight ε) M n hM).symm

/-- On a fixed head the entire omitted signed residue tail collapses to one
scalar density error BEFORE it is squared. There is no sum of absolute atom
errors in this equality. It does not bound growing physical heads. -/
theorem arithmeticFloorPartial_head_error (w : ℕ → ℝ) (C : ℝ)
    (H M : ℕ) (hHM : H ≤ M) :
    (∑ n ∈ Finset.range H, positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial w M) n -
        (arithmeticFloorPrefix w n - (n : ℝ) * C)) ^ 2) =
      (C - ∑ m ∈ Finset.range M, w (m+1) / ((m+1 : ℕ) : ℝ)) ^ 2 *
        ∑ n ∈ Finset.range H, positiveWeight n * (n : ℝ) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnM : n ≤ M := (Finset.mem_range.mp hn).le.trans hHM
  rw [arithmeticFloorHilbertPartial_sequence_of_le w M n hnM]
  ring

theorem dampedMobius_partial_head_tendsto {ε : ℝ} (hε : 0 < ε) (H : ℕ) :
    Tendsto (fun M => paretoHeadPairing H
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)) atTop
      (𝓝 (∑ n ∈ Finset.range H, positiveWeight n *
        (dampedMobiusPrefix ε n -
          (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2)) := by
  simpa only [paretoHeadPairing, mul_assoc, ← pow_two] using
    tendsto_finsetSum (Finset.range H) (fun n _ =>
      ((dampedMobius_partial_coordinate_tendsto hε n).pow 2).const_mul (positiveWeight n))

/-- Conditional research reduction: the sole arithmetic estimate is a
common upper bound on signed off-diagonal finite heads. The cutoff threshold
may depend on the physical head H. -/
theorem centered_damped_energy_of_signed_head_bound {ε : ℝ} (hε : 0 < ε)
    (B : ℝ) (hB : ∀ H, ∀ᶠ M : ℕ in atTop, dampedMobiusHeadOffDiagonal ε H M ≤ B) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) ∧
      (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) ≤
        dampedMobiusDiagonalBudget ε + B := by
  apply pareto_square_summable_of_coordinate_limit
    (fun M n => hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M) n)
    _ (dampedMobiusDiagonalBudget ε + B) (dampedMobius_partial_coordinate_tendsto hε)
  intro H
  filter_upwards [hB H] with M hM
  have he := dampedMobius_partial_head_eq_signed ε H M
  have hd := dampedMobiusHeadDiagonal_le hε H M
  simp only [paretoHeadPairing, mul_assoc, ← pow_two] at he
  linarith

/-- Exact strength of the signed-head hypothesis. It is equivalent to
membership at this fixed damping, not a proof of that membership. -/
theorem centered_damped_energy_iff_signed_head_bound {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) ↔
    ∃ B : ℝ, ∀ H, ∀ᶠ M : ℕ in atTop, dampedMobiusHeadOffDiagonal ε H M ≤ B := by
  constructor
  · intro hs
    let E := ∑' n : ℕ, positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2
    refine ⟨E + 1, ?_⟩
    intro H
    have hh : (∑ n ∈ Finset.range H, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) < E+1 := by
      have hb := Summable.sum_le_tsum (Finset.range H)
        (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) hs
      dsimp [E]
      linarith
    filter_upwards [(dampedMobius_partial_head_tendsto hε H).eventually (gt_mem_nhds hh)] with M hM
    rw [dampedMobius_partial_head_eq_signed] at hM
    linarith [dampedMobiusHeadDiagonal_nonneg ε H M]
  · rintro ⟨B, hB⟩
    exact (centered_damped_energy_of_signed_head_bound hε B hB).1

end RiemannResearch.RH.Pareto
