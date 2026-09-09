import RiemannResearch.RH.OptimizedResidueHilbert

/-!
# Exact dyadic substitution preserving the second residue channel

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §5.
The finite equality retains its complete remainder. The remainder tends to
zero in the actual weighted Hilbert norm, by an unconditional geometric bound.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem hilbertSequence_sub_substitution (f g : ThresholdHilbert) :
    hilbertSequence (f - g) = hilbertSequence f - hilbertSequence g :=
  hilbertSequenceLinear.map_sub f g

theorem optimizedResidueHilbert_substitution :
    (2 : ℝ) • optimizedResidueHilbert - digitHilbert 2 1 (by norm_num) (by omega) =
      digitHilbert 3 1 (by norm_num) (by omega) -
        digitHilbert 3 2 (by norm_num) (by omega) := by
  apply hilbertSequence_injective
  rw [hilbertSequence_sub_substitution, hilbertSequence_sub_substitution]
  simp only [hilbertSequence_smul, optimizedResidueHilbert_sequence,
    hilbertSequence_digitHilbert]
  funext k
  have hs := congrFun optimizedResidueSeed_substitution k
  simpa [digitSequence, residue, dilation] using hs

/-- The actual Hilbert remainder: physically, r_3(floor(k/2^J)). -/
def dyadicResidueRemainder (J : ℕ) : ThresholdHilbert :=
  digitHilbert 3 (2 ^ J) (by norm_num) (pow_pos (by norm_num) J)

/-- This definition keeps the entire correction, including its next-scale term. -/
def dyadicResidueSubstitutionTerm (J : ℕ) : ThresholdHilbert :=
  dyadicResidueRemainder J - dyadicResidueRemainder (J + 1)

theorem dyadicResidueRemainder_scaled (J : ℕ) :
    dyadicResidueRemainder J =
      (1 / (2 : ℝ)) ^ J • hilbertDilation (2 ^ J) (pow_pos (by norm_num) J)
        (digitHilbert 3 1 (by norm_num) (by omega)) := by
  have hd := digitHilbert_dilation 3 1 (2 ^ J) (by norm_num) (by omega)
    (pow_pos (by norm_num) J)
  simpa only [dyadicResidueRemainder, Nat.mul_one, Nat.cast_pow, Nat.cast_ofNat,
    one_div_pow] using hd

/-- Each telescoping term is a legal dilation of the replacement pair. -/
theorem dyadicResidueSubstitutionTerm_scaled (J : ℕ) :
    dyadicResidueSubstitutionTerm J =
      (1 / (2 : ℝ)) ^ J • hilbertDilation (2 ^ J) (pow_pos (by norm_num) J)
        ((2 : ℝ) • optimizedResidueHilbert -
          digitHilbert 2 1 (by norm_num) (by omega)) := by
  rw [optimizedResidueHilbert_substitution]
  have hleft := digitHilbert_dilation 3 1 (2 ^ J) (by norm_num) (by omega)
    (pow_pos (by norm_num) J)
  have hright := digitHilbert_dilation 3 2 (2 ^ J) (by norm_num) (by omega)
    (pow_pos (by norm_num) J)
  have hs : (1 / (2 : ℝ)) ^ J = 1 / ((2 ^ J : ℕ) : ℝ) := by
    simp [one_div_pow]
  rw [hs]
  have hmap : hilbertDilation (2 ^ J) (pow_pos (by norm_num) J)
      (digitHilbert 3 1 (by norm_num) (by omega) -
        digitHilbert 3 2 (by norm_num) (by omega)) =
      hilbertDilation (2 ^ J) (pow_pos (by norm_num) J)
        (digitHilbert 3 1 (by norm_num) (by omega)) -
      hilbertDilation (2 ^ J) (pow_pos (by norm_num) J)
        (digitHilbert 3 2 (by norm_num) (by omega)) :=
    (hilbertDilationLinear (2 ^ J) (pow_pos (by norm_num) J)).map_sub _ _
  rw [hmap, smul_sub, ← hleft, ← hright]
  simp only [dyadicResidueSubstitutionTerm, dyadicResidueRemainder, Nat.mul_one,
    pow_succ]

theorem dyadicResidueSubstitution_finite (J : ℕ) :
    (∑ j ∈ Finset.range J, dyadicResidueSubstitutionTerm j) =
      digitHilbert 3 1 (by norm_num) (by omega) - dyadicResidueRemainder J := by
  induction J with
  | zero => simp [dyadicResidueRemainder]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold dyadicResidueSubstitutionTerm
    abel

theorem dyadicResidueRemainder_norm_sq (J : ℕ) :
    ‖dyadicResidueRemainder J‖ ^ 2 =
      (1 / (2 : ℝ)) ^ J * ‖digitHilbert 3 1 (by norm_num) (by omega)‖ ^ 2 := by
  have hd := digitHilbert_norm_sq_scale 3 1 (2 ^ J) (by norm_num) (by omega)
    (pow_pos (by norm_num) J)
  simpa only [dyadicResidueRemainder, Nat.mul_one, Nat.cast_pow, Nat.cast_ofNat,
    one_div_pow, div_eq_mul_inv, one_mul, mul_comm, inv_pow] using hd

theorem dyadicResidueRemainder_below (J k : ℕ) (hk : k < 2 ^ J) :
    hilbertSequence (dyadicResidueRemainder J) k = 0 := by
  simp [dyadicResidueRemainder, hilbertSequence_digitHilbert, digitSequence,
    Nat.div_eq_of_lt hk]

theorem dyadicResidueSubstitution_error_sq (J : ℕ) :
    ‖digitHilbert 3 1 (by norm_num) (by omega) -
      (∑ j ∈ Finset.range J, dyadicResidueSubstitutionTerm j)‖ ^ 2 =
      (1 / (2 : ℝ)) ^ J * ‖digitHilbert 3 1 (by norm_num) (by omega)‖ ^ 2 := by
  rw [dyadicResidueSubstitution_finite, sub_sub_cancel, dyadicResidueRemainder_norm_sq]

theorem dyadicResidueSubstitution_tendsto :
    Filter.Tendsto (fun J => ∑ j ∈ Finset.range J, dyadicResidueSubstitutionTerm j)
      Filter.atTop (nhds (digitHilbert 3 1 (by norm_num) (by omega))) := by
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  have hs : Filter.Tendsto (fun J =>
      ‖digitHilbert 3 1 (by norm_num) (by omega) -
        (∑ j ∈ Finset.range J, dyadicResidueSubstitutionTerm j)‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [dyadicResidueSubstitution_error_sq, zero_mul] using
      hg.mul_const (‖digitHilbert 3 1 (by norm_num) (by omega)‖ ^ 2)
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := hs.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [he] with J hJ
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (digitHilbert 3 1 (by norm_num) (by omega) -
    ∑ j ∈ Finset.range J, dyadicResidueSubstitutionTerm j)]

/-- Every closed invariant subspace containing the replacement pair contains r_3.
The dilation invariance here ranges over all positive integers. -/
theorem third_residue_mem_of_optimized_pair (M : Submodule ℝ ThresholdHilbert)
    (hclosed : IsClosed (M : Set ThresholdHilbert))
    (hD : ∀ f ∈ M, ∀ m (hm : 0 < m), hilbertDilation m hm f ∈ M)
    (h2 : digitHilbert 2 1 (by norm_num) (by omega) ∈ M)
    (hφ : optimizedResidueHilbert ∈ M) :
    digitHilbert 3 1 (by norm_num) (by omega) ∈ M := by
  apply hclosed.mem_of_tendsto dyadicResidueSubstitution_tendsto
  apply Filter.Eventually.of_forall
  intro J
  apply M.sum_mem
  intro j hj
  rw [dyadicResidueSubstitutionTerm_scaled]
  exact M.smul_mem _ (hD _ (M.sub_mem (M.smul_mem _ hφ) h2) _ _)

/-- The old and new seed pairs define the same closed invariant subspaces.
This statement quantifies over actual closed submodules and therefore retains
the precise Hilbert topology and every positive integer dilation. -/
theorem optimized_pair_closed_invariant_iff (M : Submodule ℝ ThresholdHilbert)
    (hclosed : IsClosed (M : Set ThresholdHilbert))
    (hD : ∀ f ∈ M, ∀ m (hm : 0 < m), hilbertDilation m hm f ∈ M) :
    (digitHilbert 2 1 (by norm_num) (by omega) ∈ M ∧
      digitHilbert 3 1 (by norm_num) (by omega) ∈ M) ↔
      (optimizedResidueHilbert ∈ M ∧ complementaryResidueHilbert ∈ M) := by
  constructor
  · rintro ⟨h2, h3⟩
    have hd : digitHilbert 3 2 (by norm_num) (by omega) ∈ M := by
      have he := digitHilbert_dilation 3 1 2 (by norm_num) (by omega) (by omega)
      norm_num at he
      rw [he]
      exact M.smul_mem _ (hD _ h3 2 (by omega))
    have htwo : (2 : ℝ) • optimizedResidueHilbert ∈ M := by
      rw [← sub_add_cancel ((2 : ℝ) • optimizedResidueHilbert)
        (digitHilbert 2 1 (by norm_num) (by omega)), optimizedResidueHilbert_substitution]
      exact M.add_mem (M.sub_mem h3 hd) h2
    have hφ : optimizedResidueHilbert ∈ M := by
      have hh := M.smul_mem (1 / 2 : ℝ) htwo
      simpa [smul_smul] using hh
    exact ⟨hφ, M.sub_mem h2 hφ⟩
  · rintro ⟨hφ, hθ⟩
    have he : optimizedResidueHilbert + complementaryResidueHilbert =
        digitHilbert 2 1 (by norm_num) (by omega) := by
      unfold complementaryResidueHilbert
      abel
    have h2 : digitHilbert 2 1 (by norm_num) (by omega) ∈ M := by
      rw [← he]
      exact M.add_mem hφ hθ
    exact ⟨h2, third_residue_mem_of_optimized_pair M hclosed hD h2 hφ⟩

end
end RiemannResearch.RH.Pareto
