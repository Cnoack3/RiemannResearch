import RiemannResearch.RH.ParetoPacketCoordinates
import RiemannResearch.RH.OptimizedResidueHilbert
import RiemannResearch.RH.ThresholdBoundedInterpolation

/-!
# A concrete mean-one legal Schur recursion

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Sections 6–7. This is the specified sequence of actual finite legal vectors,
starting from r_2/log 2 and using the optimized two-channel packets.
All finite-step invariants are proved. Uniform boundedness of this particular
sequence remains an open arithmetic assertion, explicitly named below.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def optimizedPacketIterate : ℕ → ThresholdHilbert
  | 0 => initialLegalMeanOne
  | n + 1 => paretoPacketStep (optimizedPacketIterate n)
      (optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n))
      (complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n)) (n + 1)

theorem optimizedPacketIterate_legal (n : ℕ) :
    optimizedPacketIterate n ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  induction n with
  | zero => exact initialLegalMeanOne_legal
  | succ n ih =>
      exact paretoPacketStep_legal _ _ _ _ _ ih
        (optimizedCorrectionHilbert_legal (n + 1) (Nat.succ_pos n))
        (complementaryCorrectionHilbert_legal (n + 1) (Nat.succ_pos n))

theorem optimizedPacketIterate_mean (n : ℕ) :
    inner ℝ (optimizedPacketIterate n) hilbertOne = 1 := by
  induction n with
  | zero => exact initialLegalMeanOne_mean
  | succ n ih =>
      rw [optimizedPacketIterate, paretoPacketStep_mean _ _ _ _
        (optimizedCorrectionHilbert_mean (n + 1) (Nat.succ_pos n))
        (complementaryCorrectionHilbert_mean (n + 1) (Nat.succ_pos n))]
      exact ih

theorem optimizedPacketIterate_head (n : ℕ) :
    ∀ k, 0 < k → k ≤ n → hilbertSequence (optimizedPacketIterate n) k = 1 := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
      apply paretoPacketStep_head
      · intro k hk hkn
        exact ih k hk (by omega)
      · intro k _hk hkn
        exact optimizedCorrectionHilbert_below (n + 1) k (Nat.succ_pos n) hkn
      · exact optimizedCorrectionHilbert_at (n + 1) (Nat.succ_pos n)
      · intro k _hk hkn
        exact complementaryCorrectionHilbert_through (n + 1) k (Nat.succ_pos n) hkn

/-- Every full-Hilbert error has exactly its mean-zero squared norm as excess
energy. This does not assert convergence or bound that excess. -/
theorem optimizedPacketIterate_energy_error (n : ℕ) :
    ‖optimizedPacketIterate n‖ ^ 2 =
      1 + ‖optimizedPacketIterate n - hilbertOne‖ ^ 2 :=
  pareto_mean_one_norm_sq _ (optimizedPacketIterate_mean n)

def optimizedPacketResidual (n : ℕ) : ℝ :=
  1 - hilbertSequence (optimizedPacketIterate n) (n + 1)

theorem optimizedPacketIterate_error_mean_zero (n : ℕ) :
    inner ℝ (optimizedPacketIterate n - hilbertOne) hilbertOne = 0 := by
  rw [inner_sub_left, optimizedPacketIterate_mean,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  norm_num

theorem optimizedPacketIterate_error_head (n k : ℕ) (hk : k < n) :
    hilbertGibbsPhysical (optimizedPacketIterate n - hilbertOne) k = 0 := by
  change hilbertSequenceLinear (optimizedPacketIterate n - hilbertOne) (k + 1) = 0
  rw [map_sub]
  change hilbertSequence (optimizedPacketIterate n) (k + 1) -
    hilbertSequence hilbertOne (k + 1) = 0
  rw [optimizedPacketIterate_head n (k + 1) (Nat.succ_pos k) (by omega),
    hilbertOne_sequence]
  simp [zeroAnchor]

/-- All already-corrected coordinates have exactly zero Haar coefficient. -/
theorem optimizedPacketIterate_error_coefficients_before (n j : ℕ) (hj : j < n) :
    inner ℝ (optimizedPacketIterate n - hilbertOne) (tailBasisHilbert j) = 0 :=
  tailBasis_coefficient_before_head _ n j
    (optimizedPacketIterate_error_mean_zero n)
    (optimizedPacketIterate_error_head n) hj

/-- The actual correction amplitude is exactly the next Haar coefficient
times its index, with the sign required by the causal recursion. -/
theorem optimizedPacketResidual_tail_coefficient (n : ℕ) :
    optimizedPacketResidual n = -((n : ℝ) + 1) *
      inner ℝ (optimizedPacketIterate n - hilbertOne) (tailBasisHilbert n) := by
  rw [tailBasis_coefficient_at_first _ n
    (optimizedPacketIterate_error_mean_zero n) (optimizedPacketIterate_error_head n)]
  have hp : hilbertGibbsPhysical (optimizedPacketIterate n - hilbertOne) n =
      hilbertSequence (optimizedPacketIterate n) (n + 1) - 1 := by
    change hilbertSequenceLinear (optimizedPacketIterate n - hilbertOne) (n + 1) = _
    rw [map_sub]
    change hilbertSequence (optimizedPacketIterate n) (n + 1) -
      hilbertSequence hilbertOne (n + 1) = _
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  rw [hp]
  unfold optimizedPacketResidual
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The complete signed increment, with both old/new pairings and the mixed
within-packet term included. Every pairing is the actual infinite pairing. -/
def optimizedPacketEnergyChange (n : ℕ) : ℝ :=
  let F := optimizedPacketIterate n
  let u := optimizedCorrectionHilbert (n + 1) (Nat.succ_pos n)
  let d := complementaryCorrectionHilbert (n + 1) (Nat.succ_pos n)
  let δ := optimizedPacketResidual n
  2 * δ * inner ℝ F u + δ ^ 2 * ‖u‖ ^ 2 -
    (inner ℝ F d + δ * inner ℝ u d) ^ 2 / ‖d‖ ^ 2

theorem optimizedPacketIterate_energy_step (n : ℕ) :
    ‖optimizedPacketIterate (n + 1)‖ ^ 2 =
      ‖optimizedPacketIterate n‖ ^ 2 + optimizedPacketEnergyChange n := by
  rw [optimizedPacketIterate, paretoPacketStep_energy _ _ _ _
    (complementaryCorrectionHilbert_ne_zero (n + 1) (Nat.succ_pos n))]
  simp only [optimizedPacketEnergyChange, optimizedPacketResidual]
  ring

/-- Exact cumulative energy. No mixed term has been bounded separately. -/
theorem optimizedPacketIterate_energy_telescope (N : ℕ) :
    ‖optimizedPacketIterate N‖ ^ 2 =
      ‖initialLegalMeanOne‖ ^ 2 +
        ∑ n ∈ Finset.range N, optimizedPacketEnergyChange n := by
  induction N with
  | zero => simp [optimizedPacketIterate]
  | succ N ih =>
      rw [optimizedPacketIterate_energy_step, ih, Finset.sum_range_succ]
      ring

/-- Open arithmetic target for this specified recursion. This declaration is
a proposition definition, not a proof or an assumed axiom. -/
def OptimizedPacketUniformBound : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ‖optimizedPacketIterate N‖ ^ 2 ≤ C

/-- Conditional research reduction: only the named uniform-bound hypothesis
remains open; legality, all exact heads and all mean constraints are supplied
by checked declarations for the actual two-channel recursion. -/
theorem optimizedPacketUniformBound_target_membership
    (hbound : OptimizedPacketUniformBound) :
    hilbertOne ∈ hilbertLegalClosure ({2, 3} : Set ℕ) := by
  obtain ⟨C, hC⟩ := hbound
  apply hilbertLegalClosure_of_bounded_exact_heads _ C
  intro N
  exact ⟨optimizedPacketIterate N, optimizedPacketIterate_legal N,
    optimizedPacketIterate_head N, hC N⟩

end
end RiemannResearch.RH.Pareto
