import RiemannResearch.Analysis.NoorLogarithmDensity
import RiemannResearch.RH.ParetoTailAverages
import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.RH.ExactHeadResidualTail

/-!
# Noor's shifted-residue density theorem

Source: S. Waleed Noor, "A Hardy space analysis of the Baez-Duarte criterion
for the RH", Theorem 9, https://arxiv.org/abs/1809.09577.
The cited statement is density after applying `I-S`, and the proof uses
the shifted logarithmic generators.

We identify the actual Hardy coordinates of `residueAtom i`, including
the factor `i+2`, then prove shifted density using the finite Möbius
approximation in `Analysis/NoorLogarithmDensity` and weak convergence of
the logarithmic vectors. This is a theorem about the real coefficient model;
it does not assert density of the undifferenced residue span.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.Noor
open CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

@[simp] theorem forward_zero (a : Space) :
    forwardDifference a 0 = a 0 := by
  change a 0 - 0 = a 0
  exact sub_zero _

@[simp] theorem forward_succ (a : Space) (n : ℕ) :
    forwardDifference a (n+1) = a (n+1) - a n := rfl

/-- A coefficient difference is the weighted consecutive physical difference. -/
theorem forward_hardy_physical (f : ThresholdHilbert) (n : ℕ) :
    ((n : ℝ)+1) * forwardDifference (hardyCoordinates f) (n+1) =
      hilbertSequence f (n+1) - hilbertSequence f n := by
  cases n with
  | zero =>
    have h := hardyCoordinates_reconstruction f 0
    simpa [forward_succ, hilbertGibbsPhysical_eq, hilbertSequence_zero] using h.symm
  | succ n =>
    have h1 := hardyCoordinates_reconstruction f n
    have h2 := hardyCoordinates_reconstruction f (n+1)
    rw [hilbertGibbsPhysical_eq] at h1 h2
    rw [Finset.sum_range_succ] at h2
    rw [forward_succ]
    push_cast at h1 h2 ⊢
    nlinarith

theorem forward_residue_zero (i : ℕ) :
    forwardDifference (hardyCoordinates (residueAtom i)) 0 =
      -(Real.log ((i+2 : ℕ) : ℝ) / ((i+2 : ℕ) : ℝ)) := by
  rw [forward_zero, hardyCoordinates_zero, tailAverage_zero,
    residueAtom_inner_one]

theorem forward_residue_succ (i n : ℕ) :
    forwardDifference (hardyCoordinates (residueAtom i)) (n+1) =
      (1 / ((i+2 : ℕ) : ℝ) - if i+2 ∣ n+1 then 1 else 0) / ((n : ℝ)+1) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hk : ((i+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := forward_hardy_physical (residueAtom i) n
  simp only [residueAtom, normalizedResidueHilbert_sequence] at h
  change ((n : ℝ)+1) * forwardDifference (hardyCoordinates (residueAtom i)) (n+1) =
    residueFraction (i+2) (n+1) - residueFraction (i+2) n at h
  calc
    _ = (residueFraction (i+2) (n+1) - residueFraction (i+2) n) /
        ((n : ℝ)+1) := (eq_div_iff hn).2 (by nlinarith [h])
    _ = _ := by
      congr 1
      unfold residueFraction
      rw [← sub_div]
      change (residue (i+2) (n+1) - residue (i+2) n) /
        ((i+2 : ℕ) : ℝ) = _
      have hdif := residue_difference (i+2) (n+1) (by omega)
      simp only [Nat.add_sub_cancel] at hdif
      rw [hdif]
      split_ifs <;> simp only [sub_div, div_self hk, sub_zero]

/-- Exact normalization of the actual residues as Noor's shifted logarithms. -/
theorem forward_residue_decomposition (i : ℕ) :
    ((i+2 : ℕ) : ℝ) • forwardDifference (hardyCoordinates (residueAtom i)) =
      -(Real.log ((i+2 : ℕ) : ℝ)) • (lp.single 2 0 (1 : ℝ) : Space) +
        logVector 1 - logVector (i+2) := by
  have hk : ((i+2 : ℕ) : ℝ) ≠ 0 := by positivity
  apply Subtype.ext
  funext n
  cases n with
  | zero =>
    change ((i+2 : ℕ) : ℝ) * forwardDifference (hardyCoordinates (residueAtom i)) 0 =
      -Real.log ((i+2 : ℕ) : ℝ) * (lp.single 2 0 (1 : ℝ) : Space) 0 +
        logVector 1 0 - logVector (i+2) 0
    rw [forward_residue_zero]
    simp only [logVector_apply, logSequence_zero, lp.single_apply_self,
      mul_one, add_zero, sub_zero]
    field_simp
  | succ n =>
    change ((i+2 : ℕ) : ℝ) * forwardDifference (hardyCoordinates (residueAtom i)) (n+1) =
      -Real.log ((i+2 : ℕ) : ℝ) * (lp.single 2 0 (1 : ℝ) : Space) (n+1) +
        logVector 1 (n+1) - logVector (i+2) (n+1)
    rw [forward_residue_succ]
    by_cases hd : i+2 ∣ n+1 <;>
      simp [logVector_apply, logSequence, hd]
    all_goals field_simp [hk]

theorem logVector_eq_zero_of_lt {k n : ℕ} (hnk : n < k) :
    logVector k n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [logVector_apply, logSequence]
  · have hnd : ¬ k ∣ n := by
      intro hd
      exact (Nat.not_le_of_lt hnk) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
    simp [logVector_apply, logSequence, hnd]

/-- The uniformly bounded logarithmic vectors escape every fixed initial segment. -/
theorem logVector_weak_tendsto_zero (w : Space) :
    Tendsto (fun k => inner ℝ w (logVector (k+2))) atTop (𝓝 0) := by
  have hu : Tendsto
      (fun k => ‖hilbertTailShift w k‖^2 * ‖logVector 1‖^2) atTop (𝓝 0) := by
    simpa using (hilbertTailShift_energy_tendsto_zero w).mul_const (‖logVector 1‖^2)
  have hs : Tendsto (fun k => (inner ℝ w (logVector (k+2)))^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) _ hu
    intro k
    have h := hilbertTailShift_inner_sq_le w (logVector (k+2)) k (by
      intro n hn
      exact logVector_eq_zero_of_lt (by omega))
    simpa only [logVector_norm (k+2) (by omega)] using h
  have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hh : Tendsto (fun k => ‖inner ℝ w (logVector (k+2))‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using habs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hh

theorem shiftedResidue_orthogonal_total (w : Space)
    (hw : ∀ i : ℕ, inner ℝ (forwardDifference (hardyCoordinates (residueAtom i))) w = 0) :
    w = 0 := by
  have hp (i : ℕ) : Real.log ((i+2 : ℕ) : ℝ) * w 0 =
      inner ℝ w (logVector 1) - inner ℝ w (logVector (i+2)) := by
    have h := congrArg (fun x : Space => inner ℝ w x) (forward_residue_decomposition i)
    have hz : inner ℝ w (forwardDifference (hardyCoordinates (residueAtom i))) = 0 := by
      rw [real_inner_comm]
      exact hw i
    simp [inner_smul_right, inner_add_right, inner_sub_right, lp.inner_single_right, hz] at h
    push_cast at h ⊢
    linarith
  have hlog : Tendsto (fun i : ℕ => Real.log ((i+2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 2))
  have hq := (tendsto_inv_atTop_zero.comp hlog).mul
    ((tendsto_const_nhds (x := inner ℝ w (logVector 1))).sub
      (logVector_weak_tendsto_zero w))
  have hcancel (i : ℕ) :
      (Real.log ((i+2 : ℕ) : ℝ))⁻¹ *
        (inner ℝ w (logVector 1) - inner ℝ w (logVector (i+2))) = w 0 := by
    have hne : Real.log ((i+2 : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < i+2)))
    rw [← hp i, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hw0 : w 0 = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [Function.comp_def, hcancel, zero_mul] using hq)
  have he (i : ℕ) : inner ℝ w (logVector (i+2)) = inner ℝ w (logVector 1) := by
    have h := hp i
    rw [hw0, mul_zero] at h
    linarith
  have h1 : inner ℝ w (logVector 1) = 0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [he] using logVector_weak_tendsto_zero w)
  apply eq_zero_of_orthogonal_logVector w hw0
  intro k hk
  by_cases h : k = 1
  · simpa only [h] using h1
  obtain ⟨i, rfl⟩ : ∃ i, k = i+2 := ⟨k-2, by omega⟩
  exact (he i).trans h1

/-- Noor's shifted-density theorem for the actual real Pareto/Hardy coordinates. -/
theorem shiftedResidue_density :
    (Submodule.span ℝ (Set.range (fun i =>
      forwardDifference (hardyCoordinates (residueAtom i))))).topologicalClosure = ⊤ := by
  have hb : (Submodule.span ℝ (Set.range (fun i =>
      forwardDifference (hardyCoordinates (residueAtom i)))))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro w hw
    change w = 0
    apply shiftedResidue_orthogonal_total w
    intro i
    exact hw _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← Submodule.orthogonal_orthogonal_eq_closure, hb, Submodule.bot_orthogonal_eq_top]

end RiemannResearch.RH.Pareto.Noor
