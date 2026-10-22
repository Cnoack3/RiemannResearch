import RiemannResearch.RH.NoorShiftedSource
import RiemannResearch.RH.OptimizedResidueHarmonic

/-!
# Complete arithmetic mixed Gram entries

Source: elementary deductions from the user-provided shifted-lift handoff and
its exact shifted decomposition and the complete
Hilbert inner products in NoorShiftedSource. Every signed term is retained.
The arithmetic series is convergent; no growing inverse-Gram estimate or RH
conclusion is asserted.

The harmonic coefficient formula is also equation (3.3) in F. Calderaro,
J. Manzur, W. Noor and C. Santos, "Orthogonality questions in the Hardy space
related to zeta-zeros", https://arxiv.org/html/2203.05030v3.
That reference supports the coefficient statement, not a growing inverse rate.
No mathematical novelty is asserted.
-/

noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.Noor
open RiemannResearch.Analysis.ShiftedLift
open CoefficientStabilization

/-- The complete Hardy coefficient of an arithmetic residue generator. -/
theorem hardyResidue_harmonic_scaled (i n : ℕ) :
    ((i+2 : ℕ) : ℝ) * hardyCoordinates (residueAtom i) n =
      (harmonic n : ℝ) - (harmonic (n / (i+2)) : ℝ) -
        Real.log ((i+2 : ℕ) : ℝ) := by
  have hd : ((i+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have ht (n : ℕ) :
      ((i+2 : ℕ) : ℝ) * hardyCoordinates (residueAtom i) n =
        -Real.log ((i+2 : ℕ) : ℝ) +
        ∑ k ∈ Finset.range n,
          (1 / ((k : ℝ)+1) -
            if i+2 ∣ k+1 then ((i+2 : ℕ) : ℝ) / ((k : ℝ)+1) else 0) := by
    induction n with
    | zero =>
      have h := forward_residue_zero i
      rw [forward_zero] at h
      rw [h]
      simp only [Finset.sum_range_zero, add_zero]
      field_simp
    | succ n ih =>
      have h := forward_residue_succ i n
      rw [forward_succ] at h
      have hs := congrArg (fun x : ℝ => ((i+2 : ℕ) : ℝ) * x) h
      have he :
          ((i+2 : ℕ) : ℝ) *
            ((1 / ((i+2 : ℕ) : ℝ) - if i+2 ∣ n+1 then 1 else 0) /
              ((n : ℝ)+1)) =
            1 / ((n : ℝ)+1) -
              if i+2 ∣ n+1 then ((i+2 : ℕ) : ℝ) / ((n : ℝ)+1) else 0 := by
        have hn : (n : ℝ)+1 ≠ 0 := by positivity
        split_ifs
        · field_simp
        · field_simp
          ring
      rw [mul_sub, he] at hs
      rw [Finset.sum_range_succ]
      linarith
  have hh : (∑ k ∈ Finset.range n, 1 / ((k : ℝ)+1)) =
      (harmonic n : ℝ) := by
    simp [harmonic, one_div]
  have h := ht n
  rw [Finset.sum_sub_distrib, hh,
    harmonic_divisibility_sum (i+2) n (by omega)] at h
  linarith

theorem hardyResidue_harmonic (i n : ℕ) :
    hardyCoordinates (residueAtom i) n =
      ((harmonic n : ℝ) - (harmonic (n / (i+2)) : ℝ) -
        Real.log ((i+2 : ℕ) : ℝ)) / ((i+2 : ℕ) : ℝ) := by
  have hd : ((i+2 : ℕ) : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using hardyResidue_harmonic_scaled i n

/-- The complete mixed entry as exact logarithmic moments. -/
theorem mixedResidue_inner_logMoments (i j : ℕ) :
    ((i+2 : ℕ) : ℝ) * ((j+2 : ℕ) : ℝ) *
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom i)))
        (hardyCoordinates (residueAtom j)) =
      Real.log ((i+2 : ℕ) : ℝ) * Real.log ((j+2 : ℕ) : ℝ) +
      ((j+2 : ℕ) : ℝ) *
        (inner ℝ (hardyCoordinates (residueAtom j)) (logVector 1) -
          inner ℝ (hardyCoordinates (residueAtom j)) (logVector (i+2))) := by
  have h := congrArg
    (fun x : Space => inner ℝ (hardyCoordinates (residueAtom j)) x)
    (forward_residue_decomposition i)
  simp only [inner_smul_right, inner_add_right, inner_sub_right,
    lp.inner_single_right] at h
  have hscalar (x : ℝ) : inner ℝ x (1 : ℝ) = x := by
    exact one_mul x
  simp only [hscalar] at h
  have hz := hardyResidue_harmonic_scaled j 0
  simp only [harmonic_zero, Rat.cast_zero, Nat.zero_div, sub_zero, zero_sub] at hz
  rw [real_inner_comm] at h
  linear_combination ((j+2 : ℕ) : ℝ) * h -
    Real.log ((i+2 : ℕ) : ℝ) * hz

/-- Every signed arithmetic correction to the full mixed matrix, including
its skew part. The zeroth summand is zero by totalized real division. -/
theorem mixedResidue_inner_harmonic (i j : ℕ) :
    ((i+2 : ℕ) : ℝ) * ((j+2 : ℕ) : ℝ) *
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom i)))
        (hardyCoordinates (residueAtom j)) =
      Real.log ((i+2 : ℕ) : ℝ) * Real.log ((j+2 : ℕ) : ℝ) +
      ∑' m : ℕ,
        ((harmonic m : ℝ) - (harmonic (m / (j+2)) : ℝ) -
          (harmonic ((i+2)*m) : ℝ) +
          (harmonic (((i+2)*m) / (j+2)) : ℝ)) / (m : ℝ) := by
  let u := hardyCoordinates (residueAtom j)
  have hs1 : Summable (fun m : ℕ => u m / (m : ℝ)) := by
    simpa only [one_mul] using summable_log_multiples u 1 (by omega)
  have hsd := summable_log_multiples u (i+2) (by omega)
  rw [mixedResidue_inner_logMoments,
    inner_logVector_eq_tsum_multiples _ 1 (by omega),
    inner_logVector_eq_tsum_multiples _ (i+2) (by omega)]
  simp only [one_mul]
  change _ + ((j+2 : ℕ) : ℝ) *
    ((∑' m : ℕ, u m / (m : ℝ)) -
      ∑' m : ℕ, u ((i+2)*m) / (m : ℝ)) = _
  rw [← hs1.tsum_sub hsd, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro m
  have h1 := hardyResidue_harmonic_scaled j m
  have h2 := hardyResidue_harmonic_scaled j ((i+2)*m)
  change ((j+2 : ℕ) : ℝ) * (u m / (m : ℝ) - u ((i+2)*m) / (m : ℝ)) = _
  calc
    _ = (((j+2 : ℕ) : ℝ) * u m -
      ((j+2 : ℕ) : ℝ) * u ((i+2)*m)) / (m : ℝ) := by ring
    _ = _ := by
      dsimp only [u]
      rw [h1, h2]
      ring

/-- Stage-indexed form of the full arithmetic mixed Gram formula. -/
theorem finiteMixedShiftGram_harmonic (N : ℕ) (i j : Fin N) :
    ((i.val+2 : ℕ) : ℝ) * ((j.val+2 : ℕ) : ℝ) * finiteMixedShiftGram N i j =
      Real.log ((i.val+2 : ℕ) : ℝ) * Real.log ((j.val+2 : ℕ) : ℝ) +
      ∑' m : ℕ,
        ((harmonic m : ℝ) - (harmonic (m / (j.val+2)) : ℝ) -
          (harmonic ((i.val+2)*m) : ℝ) +
          (harmonic (((i.val+2)*m) / (j.val+2)) : ℝ)) / (m : ℝ) := by
  exact mixedResidue_inner_harmonic i.val j.val

end RiemannResearch.RH.Pareto.Noor


/-! Exact leading far-dilation behavior of both orientations of the mixed Gram.
The full matrix cannot be replaced by half its symmetric part. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.Noor
open CoefficientStabilization

/-- Normalized shifted arithmetic atoms have the expected pairing limit with
every fixed coefficient vector. -/
theorem shiftedResidue_pairing_log_scaled_tendsto (w : Space) :
    Tendsto (fun i : ℕ => ((i+2 : ℕ) : ℝ) *
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom i))) w /
        Real.log ((i+2 : ℕ) : ℝ)) atTop (𝓝 (-w 0)) := by
  have hlog : Tendsto (fun i : ℕ => Real.log ((i+2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 2))
  have hsmall := ((tendsto_const_nhds (x := inner ℝ w (logVector 1))).sub
    (logVector_weak_tendsto_zero w)).mul (tendsto_inv_atTop_zero.comp hlog)
  have hlim := (tendsto_const_nhds (x := -w 0)).add hsmall
  simp only [sub_zero, mul_zero, add_zero] at hlim
  convert hlim using 1
  ext i
  have h := congrArg (fun x : Space => inner ℝ w x) (forward_residue_decomposition i)
  simp only [inner_smul_right, inner_add_right, inner_sub_right,
    lp.inner_single_right] at h
  have hscalar (x : ℝ) : inner ℝ x (1 : ℝ) = x := by
    exact one_mul x
  simp only [hscalar] at h
  rw [real_inner_comm] at h
  have hne : Real.log ((i+2 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < i+2)))
  simp only [Function.comp_def]
  rw [h]
  field_simp
  ring

/-- In one orientation, the leading mixed entry retains the full logarithmic
rank-one term. -/
theorem mixedResidue_forward_log_scaled_tendsto (j : ℕ) :
    Tendsto (fun i : ℕ => ((i+2 : ℕ) : ℝ) *
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom i)))
        (hardyCoordinates (residueAtom j)) /
      Real.log ((i+2 : ℕ) : ℝ)) atTop
        (𝓝 (Real.log ((j+2 : ℕ) : ℝ) / ((j+2 : ℕ) : ℝ))) := by
  have hz := forward_residue_zero j
  rw [forward_zero] at hz
  simpa only [hz, neg_neg] using
    shiftedResidue_pairing_log_scaled_tendsto (hardyCoordinates (residueAtom j))

private theorem forwardDifference_inner_add_swap (u v : Space) :
    inner ℝ (forwardDifference u) v + inner ℝ (forwardDifference v) u =
      inner ℝ (forwardDifference u) (forwardDifference v) := by
  have hS : inner ℝ (rightShift u) (rightShift v) = inner ℝ u v := by
    have hv : leftShift (rightShift v) = v := by
      apply Subtype.ext
      funext n
      rfl
    rw [shift_inner, hv]
  simp only [forwardDifference, inner_sub_left, inner_sub_right, hS]
  rw [real_inner_comm v u, real_inner_comm (rightShift v) u]
  ring

/-- The reversed entry has zero leading term at the same normalization. -/
theorem mixedResidue_reverse_log_scaled_tendsto (j : ℕ) :
    Tendsto (fun i : ℕ => ((i+2 : ℕ) : ℝ) *
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom j)))
        (hardyCoordinates (residueAtom i)) /
      Real.log ((i+2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := (shiftedResidue_pairing_log_scaled_tendsto
    (forwardDifference (hardyCoordinates (residueAtom j)))).sub
    (shiftedResidue_pairing_log_scaled_tendsto (hardyCoordinates (residueAtom j)))
  simp only [forward_zero, sub_self] at h
  convert h using 1
  ext i
  have hs := forwardDifference_inner_add_swap
    (hardyCoordinates (residueAtom i)) (hardyCoordinates (residueAtom j))
  have hr : inner ℝ (forwardDifference (hardyCoordinates (residueAtom j)))
      (hardyCoordinates (residueAtom i)) =
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom i)))
        (forwardDifference (hardyCoordinates (residueAtom j))) -
      inner ℝ (forwardDifference (hardyCoordinates (residueAtom i)))
        (hardyCoordinates (residueAtom j)) := by linarith
  rw [hr]
  ring

end RiemannResearch.RH.Pareto.Noor
