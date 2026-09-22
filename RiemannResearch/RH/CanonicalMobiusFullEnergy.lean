import RiemannResearch.Analysis.SublinearEnergyLimits
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.NearbyDilationGram

/-!
# The actual canonical Möbius family in the full Pareto Hilbert space

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Section 2 and the global bound used in Section 3. The exact floor expansion
holds at all coordinates, including the tail. This module does not assume
or assert the prime number theorem or vanishing approximation error.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- Exact cancellation of the linear terms, valid outside the head as well. -/
theorem canonicalMobiusHead_floor_expansion (Y n : ℕ) :
    canonicalMobiusHead Y n =
      (∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) -
      ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y *
        ((n / (Y + 1) : ℕ) : ℝ) := by
  have hsum :
      (∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) =
      (n : ℝ) * mobiusReciprocalSum Y -
        ∑ d ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 Y,
          ((n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) -
            (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [residueFraction_eq_div_sub_floor d n (Finset.mem_Icc.mp hd).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  unfold canonicalMobiusHead
  rw [hsum, residueFraction_eq_div_sub_floor (Y + 1) n (Nat.succ_pos _)]
  have hY : (((Y + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

/-- A pointwise bound uniform over the entire infinite sequence. -/
theorem canonicalMobiusHead_abs_le_two_mul (Y : ℕ) (hY : 0 < Y) (n : ℕ) :
    |canonicalMobiusHead Y n| ≤ 2 * (Y : ℝ) := by
  have hsum := finite_mobius_sum_abs Y hY (fun d => residueFraction d n) 1
    (by simp [residueFraction, Nat.mod_one])
    (fun d hd => residueFraction_abs_le_one d n (Finset.mem_Icc.mp hd).1)
  have hm := mobiusReciprocalSum_abs_le_one Y hY
  have hg := residueFraction_abs_le_one (Y + 1) n (Nat.succ_pos _)
  have hc :
      |((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y * residueFraction (Y + 1) n| ≤
      ((Y + 1 : ℕ) : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hp := mul_le_mul hm hg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hh := mul_le_mul_of_nonneg_left hp
      (Nat.cast_nonneg (Y + 1) : (0 : ℝ) ≤ _)
    nlinarith
  unfold canonicalMobiusHead
  calc
    _ ≤ |-(∑ d ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.moebius d : ℝ) * residueFraction d n)| +
        |((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y * residueFraction (Y + 1) n| :=
      abs_add_le _ _
    _ ≤ _ := by
      rw [abs_neg]
      push_cast at hc ⊢
      linarith

/-- The explicit finite legal combination, represented in the genuine Hilbert space. -/
def canonicalMobiusHilbert (Y : ℕ) : ThresholdHilbert :=
  -(∑ d ∈ (Finset.Icc 1 Y).attach,
      (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
        normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1) +
    (((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y) •
      normalizedResidueHilbert (Y + 1) (Nat.succ_pos _)

/-- Identification with the manuscript's actual physical coordinates. -/
theorem canonicalMobiusHilbert_sequence (Y : ℕ) :
    hilbertSequence (canonicalMobiusHilbert Y) = canonicalMobiusHead Y := by
  change hilbertSequenceLinear (canonicalMobiusHilbert Y) = _
  unfold canonicalMobiusHilbert
  simp only [map_add, map_neg, map_sum, map_smul]
  change -(∑ d ∈ (Finset.Icc 1 Y).attach,
      (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
        hilbertSequence (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1)) +
    (((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y) •
      hilbertSequence (normalizedResidueHilbert (Y + 1) (Nat.succ_pos _)) = _
  simp_rw [normalizedResidueHilbert_sequence]
  funext n
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, canonicalMobiusHead]
  rw [Finset.sum_attach (Finset.Icc 1 Y)
    (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) * residueFraction d n)]

theorem canonicalMobiusHilbert_exact (Y n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
    hilbertSequence (canonicalMobiusHilbert Y) n = 1 := by
  rw [canonicalMobiusHilbert_sequence]
  exact canonicalMobiusHead_exact Y n hn hnY

/-- The exact norm split retains the full infinite tail. -/
theorem canonicalMobiusHilbert_norm_sq_split (Y : ℕ) :
    ‖canonicalMobiusHilbert Y‖ ^ 2 = (Y : ℝ) / ((Y : ℝ) + 1) +
      ∑' k : ℕ, positiveWeight (k + (Y + 1)) *
        canonicalMobiusHead Y (k + (Y + 1)) ^ 2 := by
  rw [hilbert_norm_weighted_sq,
    ← (hilbertSequence_square_summable (canonicalMobiusHilbert Y)).sum_add_tsum_nat_add
      (Y + 1), canonicalMobiusHilbert_sequence]
  congr 1
  calc
    _ = ∑ k ∈ Finset.range (Y + 1), positiveWeight k := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : k = 0
      · simp [hk0, positiveWeight]
      · rw [canonicalMobiusHead_exact Y k (by omega)
          (by have := Finset.mem_range.mp hk; omega)]
        ring
    _ = _ := by
      rw [positiveWeight_sum_range (Y + 1) (Nat.succ_pos _)]
      push_cast
      field_simp
      ring

/-- The complete Pareto energy admits an unconditional linear upper bound. -/
theorem canonicalMobiusHilbert_norm_sq_le (Y : ℕ) (hY : 0 < Y) :
    ‖canonicalMobiusHilbert Y‖ ^ 2 ≤
      (Y : ℝ) * (4 * (Y : ℝ) + 1) / ((Y : ℝ) + 1) := by
  have hs : Summable (fun k : ℕ => positiveWeight k * canonicalMobiusHead Y k ^ 2) := by
    simpa only [canonicalMobiusHilbert_sequence] using
      hilbertSequence_square_summable (canonicalMobiusHilbert Y)
  have ht := (summable_nat_add_iff (Y + 1)).mpr hs
  have hw := (summable_nat_add_iff (Y + 1)).mpr positiveWeight_summable
  have hb :
      (∑' k : ℕ, positiveWeight (k + (Y + 1)) *
        canonicalMobiusHead Y (k + (Y + 1)) ^ 2) ≤
      (2 * (Y : ℝ)) ^ 2 / ((Y : ℝ) + 1) := by
    calc
      _ ≤ ∑' k : ℕ, positiveWeight (k + (Y + 1)) * (2 * (Y : ℝ)) ^ 2 := by
        apply Summable.tsum_le_tsum _ ht (hw.mul_right ((2 * (Y : ℝ)) ^ 2))
        intro k
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        have ha := mul_self_le_mul_self
          (abs_nonneg (canonicalMobiusHead Y (k + (Y + 1))))
          (canonicalMobiusHead_abs_le_two_mul Y hY (k + (Y + 1)))
        simpa only [← pow_two, sq_abs] using ha
      _ = _ := by
        rw [tsum_mul_right, positiveWeight_tail_tsum (Y + 1) (Nat.succ_pos _)]
        push_cast
        ring
  rw [canonicalMobiusHilbert_norm_sq_split]
  calc
    _ ≤ (Y : ℝ) / ((Y : ℝ) + 1) + (2 * (Y : ℝ)) ^ 2 / ((Y : ℝ) + 1) :=
      add_le_add_right hb _
    _ = _ := by ring

theorem canonicalMobiusHilbert_norm_sq_lt_four_mul (Y : ℕ) (hY : 0 < Y) :
    ‖canonicalMobiusHilbert Y‖ ^ 2 < 4 * (Y : ℝ) := by
  apply lt_of_le_of_lt (canonicalMobiusHilbert_norm_sq_le Y hY)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (Y : ℝ) + 1)).2
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  nlinarith

/-- Conditional analytic assembly of the manuscript's fixed-cutoff argument.
The arithmetic provider of these actual full-energy bounds is not supplied. -/
theorem canonicalMobiusHilbert_sublinear_of_cutoff_bounds
    (C : ℝ)
    (hcutoff : ∀ K : ℕ, 2 ≤ K →
      ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
        ∀ᶠ N in atTop,
          ‖canonicalMobiusHilbert N‖^2 / (N : ℝ) ≤ b N + C / (K : ℝ)) :
    Tendsto (fun N => ‖canonicalMobiusHilbert N‖^2 / (N : ℝ)) atTop (𝓝 0) :=
  RiemannResearch.Analysis.tendsto_zero_of_fixed_cutoff_remainder
    (Eventually.of_forall (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N))) hcutoff

namespace CoefficientStabilization

/-- Even the harmless conductor one lies in every finite residue span, as zero. -/
theorem normalizedResidueHilbert_mem_finiteSpace (Y d : ℕ) (hd : 0 < d)
    (hdY : d ≤ Y + 1) : normalizedResidueHilbert d hd ∈ finiteSpace Y := by
  by_cases h1 : d = 1
  · subst d
    have hz : normalizedResidueHilbert 1 hd = 0 := by
      apply hilbertSequence_injective
      rw [normalizedResidueHilbert_sequence]
      funext n
      cases n <;> simp [residueFraction, hilbertSequence, Nat.mod_one]
    rw [hz]
    exact (finiteSpace Y).zero_mem
  · have hlt : d - 2 < Y := by omega
    apply Submodule.subset_span
    refine ⟨⟨d - 2, hlt⟩, ?_⟩
    simp only [id_eq, residueAtom]
    congr 1
    omega

/-- The cutoff Y family uses only g_2 through g_(Y+1), before taking any closure. -/
theorem canonicalMobiusHilbert_mem_finiteSpace (Y : ℕ) :
    canonicalMobiusHilbert Y ∈ finiteSpace Y := by
  unfold canonicalMobiusHilbert
  apply (finiteSpace Y).add_mem
  · apply (finiteSpace Y).neg_mem
    apply (finiteSpace Y).sum_mem
    intro d hd
    apply (finiteSpace Y).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hh := (Finset.mem_Icc.mp d.property).2
    omega
  · apply (finiteSpace Y).smul_mem
    exact normalizedResidueHilbert_mem_finiteSpace Y (Y + 1) (Nat.succ_pos _) le_rfl

theorem canonicalMobiusHilbert_mem_closedSpace (Y : ℕ) :
    canonicalMobiusHilbert Y ∈ closedSpace := by
  apply (Submodule.le_topologicalClosure _)
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le residueAtom id Y
    (canonicalMobiusHilbert_mem_finiteSpace Y)

end CoefficientStabilization
end RiemannResearch.RH.Pareto
