import RiemannResearch.NumberTheory.MertensShiftedFloorSum
import RiemannResearch.RH.MertensShiftedMobiusSeed

/-!
# Equality of the two shifted Möbius tests

At each fixed physical site n the floor part has finite support, and the
linear part is the absolutely convergent Dirichlet series of 1/ζ(1+s).
Their difference therefore gives the squarefree atom representation throughout
Re(s)>0, including the part where the unweighted coefficients need not lie in ℓ¹.
-/

noncomputable section
open scoped BigOperators LSeries.notation
namespace RiemannResearch.RH.MertensShiftedPairing

open RiemannResearch.NumberTheory.MertensShiftedTest
open ZetaTwoHilbert ZetaTwoOptimizerStage

private def dampedTerm (s : ℂ) (k : ℕ) : ℂ :=
  (ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ (-s)

private theorem hasSum_dampedTerm_inv_zeta (t : ℂ) (ht : 1 < t.re) :
    HasSum (dampedTerm t) (riemannZeta t)⁻¹ := by
  have hs : Summable (LSeries.term (↗ArithmeticFunction.moebius) t) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr ht
  have hval := LSeries_one_mul_Lseries_moebius ht
  rw [LSeries_one_eq_riemannZeta ht] at hval
  have hR := (mul_eq_one_iff_inv_eq₀ (riemannZeta_ne_zero_of_one_lt_re ht)).mp hval
  rw [hR]
  change HasSum (dampedTerm t) (∑' k, LSeries.term (↗ArithmeticFunction.moebius) t k)
  have hf : dampedTerm t = LSeries.term (↗ArithmeticFunction.moebius) t := by
    funext k
    exact (LSeries.term_def₀ (f := ↗ArithmeticFunction.moebius) (by simp) t k).symm
  rw [hf]
  exact hs.hasSum

private theorem dampedTerm_shift (s : ℂ) (k : ℕ) (hk : k ≠ 0) :
    dampedTerm (1+s) k = dampedTerm s k / (k : ℂ) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [dampedTerm, show -(1+s) = -s + -1 by ring, Complex.cpow_add _ _ hkC,
    Complex.cpow_neg_one, div_eq_mul_inv]
  ring

private def rowTerm (n : ℕ) (s : ℂ) (k : ℕ) : ℂ :=
  dampedTerm s k * ((n/k : ℕ) : ℂ) - (n : ℂ) * dampedTerm (1+s) k

private theorem rowTerm_atom (n i : ℕ) (s : ℂ) :
    rowTerm n s (i+2) =
      shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ) := by
  rw [rowTerm, dampedTerm_shift _ _ (by omega)]
  by_cases hi : Squarefree (i+2)
  · rw [squarefreeAtom, if_pos hi, qSequence_qResidue,
      Pareto.residueFraction_eq_div_sub_floor _ _ (by omega)]
    simp only [dampedTerm, shiftedMobiusCoefficient, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_intCast,
      div_eq_mul_inv]
    ring
  · have hm := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi
    simp [dampedTerm, shiftedMobiusCoefficient, hm]

private theorem hasSum_rowTerm (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    HasSum (rowTerm n s) (shiftedTest n s) := by
  have ht : 1 < (1+s).re := by simpa using hs
  have hnz : s ≠ 0 := by intro he; simp [he] at hs
  have hfloor : HasSum (fun k : ℕ => dampedTerm s k * ((n/k : ℕ) : ℂ))
      (∑ k ∈ Finset.Icc 1 n, dampedTerm s k * ((n/k : ℕ) : ℂ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    by_cases h0 : k = 0
    · simp [h0]
    · have hnk : n < k := by
        by_contra! h
        exact hk (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero h0, h⟩)
      simp [Nat.div_eq_of_lt hnk]
  rw [shiftedTest, sum_shiftedCoeff_eq_floor_sum, correction_eq_inv_zeta hnz]
  exact hfloor.sub ((hasSum_dampedTerm_inv_zeta (1+s) ht).mul_left (n : ℂ))

/-- The pole-subtracted finite Möbius sum is exactly its residue-atom series
at every positive real part, with full convergence at every physical site. -/
theorem hasSum_shiftedMobiusAtomTest (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun i => shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ))
      (shiftedTest n s) := by
  have ht := hasSum_rowTerm n s hs
  have hh : (∑ k ∈ Finset.range 2, rowTerm n s k) = 0 := by
    simp [Finset.sum_range_succ, rowTerm, dampedTerm]
  have hf : (fun i => shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ)) =
      (fun i => rowTerm n s (i+2)) := by funext i; exact (rowTerm_atom n i s).symm
  rw [hf]
  have hsum := (summable_nat_add_iff 2).mpr ht.summable
  have heq := ht.summable.sum_add_tsum_nat_add 2
  rw [hh, zero_add, ht.tsum_eq] at heq
  exact heq ▸ hsum.hasSum

theorem shiftedMobiusAtomTest_eq_shiftedTest (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    shiftedMobiusAtomTest n s = shiftedTest n s := (hasSum_shiftedMobiusAtomTest n s hs).tsum_eq

/-- The actual finite pole-subtracted row annihilates the witness on Re(s)>1. -/
theorem witnessCharge_shiftedTest (s : ℂ) (hs : 1 < s.re) :
    ∑' n, witnessCharge n * shiftedTest n s = 0 := by
  calc
    _ = ∑' n, witnessCharge n * shiftedMobiusAtomTest n s := by
      apply tsum_congr
      intro n
      rw [shiftedMobiusAtomTest_eq_shiftedTest n s (by linarith)]
    _ = 0 := witnessCharge_shiftedMobiusAtomTest s hs

end RiemannResearch.RH.MertensShiftedPairing
