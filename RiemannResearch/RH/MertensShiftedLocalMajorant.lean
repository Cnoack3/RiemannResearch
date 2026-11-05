/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensActualShiftedCriterion
import RiemannResearch.RH.CRTCarryArithmetic

/-!
# Local majorants for the shifted Möbius test

Interpolation between the bounds `1` and `n/k` for a residue gives a
summable p-series independent of the test parameter in each interior strip.
-/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.MertensShiftedPairing

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open RiemannResearch.NumberTheory.MertensShiftedTest

private theorem atom_norm_le_interpolant (n i : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖(qSequence (squarefreeAtom i) n : ℂ)‖ ≤ ((n : ℝ) / (i+2 : ℕ)) ^ a := by
  have hk : 0 < (i+2 : ℕ) := by omega
  have ht : 0 ≤ (n : ℝ) / (i+2 : ℕ) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hi : Squarefree (i+2)
  · rw [squarefreeAtom, if_pos hi, qSequence_qResidue,
      abs_of_nonneg (CRTCarryArithmetic.residueFraction_nonneg _ _)]
    by_cases h : (n : ℝ) / (i+2 : ℕ) ≤ 1
    · apply le_trans _ (Real.self_le_rpow_of_le_one ht h ha1)
      rw [Pareto.residueFraction_eq_div_sub_floor _ _ hk]
      exact sub_le_self _ (Nat.cast_nonneg _)
    · exact (CRTCarryArithmetic.residueFraction_lt_one _ _ hk).le.trans
        (Real.one_le_rpow (le_of_not_ge h) ha)
  · simp only [squarefreeAtom, if_neg hi]
    change |qSequenceLinear (0 : QHilbert) n| ≤ _
    simpa using Real.rpow_nonneg ht a

/-- Absolute bound on each coefficient times its residue at one physical site. -/
theorem norm_shiftedMobiusCoefficient_mul_atom_le (n i : ℕ) (s : ℂ) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hs : 2 * η ≤ s.re) :
    ‖shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ)‖ ≤
      (n : ℝ) ^ (1-η) * (((i+2 : ℕ) : ℝ) ^ (-1-η)) := by
  let k : ℝ := (i+2 : ℕ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ i+2 by omega)
  have hμ : |(ArithmeticFunction.moebius (i+2) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := i+2))
  have hc : ‖shiftedMobiusCoefficient s i‖ ≤ k ^ (-s.re) := by
    rw [shiftedMobiusCoefficient, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hk.le _) hμ
  calc
    ‖shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ)‖ =
          ‖shiftedMobiusCoefficient s i‖ * ‖(qSequence (squarefreeAtom i) n : ℂ)‖ := norm_mul _ _
    _ ≤ k ^ (-s.re) * ((n : ℝ)/k) ^ (1-η) :=
      mul_le_mul hc (atom_norm_le_interpolant n i (by linarith) (by linarith))
        (norm_nonneg _) (Real.rpow_nonneg hk.le _)
    _ = (n : ℝ) ^ (1-η) * k ^ ((-s.re)-(1-η)) := by
      rw [Real.div_rpow (Nat.cast_nonneg n) hk.le, Real.rpow_sub hk (-s.re) (1-η)]
      ring
    _ ≤ (n : ℝ) ^ (1-η) * (((i+2 : ℕ) : ℝ) ^ (-1-η)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hk1 (show (-s.re)-(1-η) ≤ -1-η by linarith))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Inside `2η ≤ Re(s)`, the finite shifted Möbius test grows uniformly
at most as `n^(1−η)`. The constant is an explicit p-series. -/
theorem norm_shiftedTest_le_strip (n : ℕ) (s : ℂ) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hs : 2 * η ≤ s.re) :
    ‖shiftedTest n s‖ ≤ (n : ℝ) ^ (1-η) *
      ∑' i : ℕ, ((i+2 : ℕ) : ℝ) ^ (-1-η) := by
  let f (i : ℕ) := shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ)
  let p (i : ℕ) := ((i+2 : ℕ) : ℝ) ^ (-1-η)
  have hp : Summable p := (summable_nat_add_iff 2).mpr
    (Real.summable_nat_rpow.mpr (show -1-η < -1 by linarith))
  have hb (i : ℕ) : ‖f i‖ ≤ (n : ℝ) ^ (1-η) * p i :=
    norm_shiftedMobiusCoefficient_mul_atom_le n i s η hη hη1 hs
  have hN := hp.mul_left ((n : ℝ) ^ (1-η))
  have hf := Summable.of_nonneg_of_le (fun i => norm_nonneg (f i)) hb hN
  calc
    ‖shiftedTest n s‖ = ‖∑' i, f i‖ := congrArg norm (hasSum_shiftedMobiusAtomTest n s (by linarith)).tsum_eq.symm
    _ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' i, (n : ℝ) ^ (1-η) * p i := hf.tsum_le_tsum hb hN
    _ = _ := tsum_mul_left

/-- A small positive real part already gives absolute Fubini if the physical
charge has the corresponding single power moment. The shifted row then
annihilates the witness throughout this strip. -/
theorem hasSum_witnessCharge_shiftedTest_of_power_moment (s : ℂ) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hs : 2 * η ≤ s.re)
    (hcharge : Summable (fun n : ℕ => ‖witnessCharge n‖ * (n : ℝ) ^ (1 - η))) :
    HasSum (fun n => witnessCharge n * shiftedTest n s) 0 := by
  let p (i : ℕ) := ((i+2 : ℕ) : ℝ) ^ (-1-η)
  have hp : Summable p := (summable_nat_add_iff 2).mpr
    (Real.summable_nat_rpow.mpr (show -1-η < -1 by linarith))
  have hprod : Summable (Function.uncurry (fun i n : ℕ =>
      shiftedMobiusCoefficient s i * (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ)))) := by
    have hmajor : Summable (fun q : ℕ × ℕ =>
        p q.1 * (‖witnessCharge q.2‖ * (q.2 : ℝ) ^ (1 - η))) :=
      hp.mul_of_nonneg hcharge (fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun n => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hmajor
    rintro ⟨i, n⟩
    change ‖shiftedMobiusCoefficient s i *
      (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ))‖ ≤ _
    calc
      _ = ‖witnessCharge n‖ *
          ‖shiftedMobiusCoefficient s i * (qSequence (squarefreeAtom i) n : ℂ)‖ := by
        rw [mul_left_comm, norm_mul]
      _ ≤ ‖witnessCharge n‖ * ((n : ℝ) ^ (1-η) * p i) :=
        mul_le_mul_of_nonneg_left
          (norm_shiftedMobiusCoefficient_mul_atom_le n i s η hη hη1 hs) (norm_nonneg _)
      _ = _ := by ring
  have hsum : Summable (fun n => witnessCharge n * shiftedTest n s) := by
    apply (hcharge.mul_right (∑' i, p i)).of_norm_bounded
    intro n
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_shiftedTest_le_strip n s η hη hη1 hs) (norm_nonneg _)
  have hzero : ∑' n, witnessCharge n * shiftedTest n s = 0 := by
    calc
      _ = ∑' n, ∑' i, shiftedMobiusCoefficient s i *
          (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ)) := by
        apply tsum_congr
        intro n
        rw [← (hasSum_shiftedMobiusAtomTest n s (by linarith)).tsum_eq, ← tsum_mul_left]
        apply tsum_congr
        intro i
        ring
      _ = ∑' i, ∑' n, shiftedMobiusCoefficient s i *
          (witnessCharge n * (qSequence (squarefreeAtom i) n : ℂ)) := hprod.tsum_comm
      _ = 0 := by simp_rw [tsum_mul_left, witnessCharge_atom, mul_zero]; simp
  exact hzero ▸ hsum.hasSum

/-- A counting-measure form of one-sided Fatou. For zero-total rows one only
needs an integrable lower bound to get an upper bound on the limiting mass. -/
theorem tsum_le_zero_of_lower_dominated_zero_rows
    (F : ℕ → ℕ → ℝ) (a G : ℕ → ℝ) (ha : Summable a) (hG : Summable G)
    (hrow : ∀ᶠ j in atTop, HasSum (F j) 0)
    (hpoint : ∀ n, Tendsto (fun j => F j n) atTop (𝓝 (a n)))
    (hlower : ∀ᶠ j in atTop, ∀ n, -G n ≤ F j n) : ∑' n, a n ≤ 0 := by
  have hprefix (S : Finset ℕ) : ∑ n ∈ S, (a n + G n) ≤ ∑' n, G n := by
    apply le_of_tendsto (tendsto_finsetSum S (fun n _ =>
      (hpoint n).add (tendsto_const_nhds (x := G n))))
    filter_upwards [hrow, hlower] with j hj hl
    have ht : HasSum (fun n => F j n + G n) (∑' n, G n) := by
      simpa using hj.add hG.hasSum
    exact sum_le_hasSum S (fun n _ => by linarith [hl n]) ht
  have h := le_of_tendsto' (ha.hasSum.add hG.hasSum).tendsto_sum_nat
    (fun K => hprefix (Finset.range K))
  linarith

/-- Only the negative side of the real scalar pairing needs a common
summable majorant along a boundary sequence. The coefficient interpolation
above performs Fubini separately at each shift. -/
theorem residual_zero_of_one_sided_shifted_tests
    (x : ℕ → ℂ) (hx0 : Tendsto x atTop (𝓝 0))
    (hpower : ∀ᶠ j in atTop, ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 2 * η ≤ (x j).re ∧
      Summable (fun n : ℕ => ‖witnessCharge n‖ * (n : ℝ) ^ (1-η)))
    (G : ℕ → ℝ) (hG : Summable G)
    (hlower : ∀ᶠ j in atTop, ∀ n,
      -G n ≤ (witnessCharge n * shiftedTest n (x j)).re) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  let F (j n : ℕ) := (witnessCharge n * shiftedTest n (x j)).re
  have hrow : ∀ᶠ j in atTop, HasSum (F j) 0 := by
    filter_upwards [hpower] with j hj
    obtain ⟨η, hη, hη1, hs, hc⟩ := hj
    simpa only [F, Complex.zero_re] using Complex.hasSum_re
      (hasSum_witnessCharge_shiftedTest_of_power_moment (x j) η hη hη1 hs hc)
  have ht (n : ℕ) : Tendsto (fun j => F j n) atTop
      (𝓝 (positiveQWeight n * qSequence QSquarefreeDisplacementRigidity.witness n)) := by
    have hc : Tendsto (fun j => witnessCharge n * shiftedTest n (x j)) atTop
        (𝓝 (witnessCharge n)) := by
      cases n with
      | zero => simp [witnessCharge, positiveQWeight]
      | succ n =>
        simpa only [Function.comp_apply, mul_one] using
          (tendsto_const_nhds (x := witnessCharge (n+1))).mul
            ((tendsto_shiftedTest_zero (n+1) (by omega)).comp hx0)
    change Tendsto (Complex.re ∘ (fun j => witnessCharge n * shiftedTest n (x j)))
      atTop (𝓝 (witnessCharge n).re)
    exact (Complex.continuous_re.tendsto _).comp hc
  have hm := tsum_le_zero_of_lower_dominated_zero_rows F _ G
    (ZetaTwoResolvent.targetCharge_summable QSquarefreeDisplacementRigidity.witness)
    hG hrow ht hlower
  rw [ZetaTwoResolvent.targetCharge_tsum, real_inner_comm] at hm
  apply QSquarefreeDisplacementRigidity.residual_eq_zero_of_witness_mean_zero
  apply le_antisymm hm
  have hp : 0 ≤ zetaTwo * inner ℝ qOne QSquarefreeDisplacementRigidity.witness := by
    rw [QSquarefreeDisplacementRigidity.witness_mean_energy]
    exact add_nonneg (mul_nonneg zetaTwo_pos.le (QShiftedReciprocal.B_positive _))
      (sq_nonneg _)
  by_contra! hneg
  exact (not_lt_of_ge hp) (mul_neg_of_pos_of_neg zetaTwo_pos hneg)

/-- Interior normal convergence follows from weighted moments of the actual
charge at every positive power saving. Only the boundary dominator remains. -/
theorem riemannHypothesis_of_actual_shifted_boundary
    (x : ℕ → ℂ) (hx : ∀ j, 0 < (x j).re) (hx0 : Tendsto x atTop (𝓝 0))
    (hcharge : ∀ η : ℝ, 0 < η → η < 1 →
      Summable (fun n : ℕ => ‖witnessCharge n‖ * (n : ℝ) ^ (1-η)))
    (G : ℕ → ℝ) (hG : Summable G)
    (hboundary : ∀ᶠ j in atTop, ∀ n, ‖witnessCharge n * shiftedTest n (x j)‖ ≤ G n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_actual_shifted_majorants x hx hx0 _ G hG hboundary
  intro z hz
  let η : ℝ := min (1/2) (z.re/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hzη : 2*η < z.re := by have hh : η ≤ z.re/4 := min_le_right _ _; linarith
  let C := ∑' i : ℕ, ((i+2 : ℕ) : ℝ) ^ (-1-η)
  refine ⟨{w : ℂ | 2*η < w.re}, isOpen_lt continuous_const Complex.continuous_re,
    hzη, fun w hw => lt_trans (by positivity : 0 < 2*η) hw,
    fun n => (‖witnessCharge n‖ * (n : ℝ) ^ (1-η)) * C, (hcharge η hη hη1).mul_right C, ?_⟩
  intro n w hw
  change ‖witnessCharge n * shiftedTest n w‖ ≤ (‖witnessCharge n‖ * (n : ℝ) ^ (1-η)) * C
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_shiftedTest_le_strip n w η hη hη1 hw.le) (norm_nonneg _)

open QSquarefreeDisplacementRigidity QShiftedReciprocal

/-- An arithmetic envelope on one sequence of shifted tests reduces the
remaining Hilbert-space assumption to one absolute moment of the actual
displacement. The condition on each fixed power is automatic for
E(n) = n exp(-o(log n)). -/
theorem residual_zero_of_shifted_displacement_envelope
    (x : ℕ → ℂ) (hx : ∀ᶠ j in atTop, 0 < (x j).re) (hx0 : Tendsto x atTop (𝓝 0))
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n)
    (hsub : ∀ η : ℝ, 0 < η → η < 1 →
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1-η) ≤ E n)
    (hbase : Summable (fun n => positiveQWeight n * E n))
    (hd : Summable (fun n => positiveQWeight n * E n * |qSequence displacement n|))
    (hboundary : ∀ᶠ j in atTop, ∀ n, ‖shiftedTest n (x j)‖ ≤ E n) :
    limitingResidual = 0 := by
  obtain ⟨A, hA⟩ := B_physical_bounded pResidual
  have hw (n : ℕ) : |qSequence witness n| ≤ A + |qSequence displacement n| := by
    have he : qSequence witness n = qSequence (B pResidual) n - qSequence displacement n := by
      change qSequenceLinear (B pResidual - displacement) n = _
      rw [map_sub]
      rfl
    rw [he]
    have ht : |qSequence (B pResidual) n - qSequence displacement n| ≤
        |qSequence (B pResidual) n| + |qSequence displacement n| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (qSequence (B pResidual) n) (-qSequence displacement n)
    exact ht.trans (add_le_add_left (hA n) _)
  have hm : Summable (fun n => ‖witnessCharge n‖ * E n) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (hE n))
      ?_ ((hbase.mul_left A).add hd)
    intro n
    rw [witnessCharge, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (positiveQWeight_nonneg n)]
    calc
      _ = (positiveQWeight n * E n) * |qSequence witness n| := by ring
      _ ≤ (positiveQWeight n * E n) * (A + |qSequence displacement n|) :=
        mul_le_mul_of_nonneg_left (hw n) (mul_nonneg (positiveQWeight_nonneg n) (hE n))
      _ = _ := by ring
  refine residual_zero_of_one_sided_shifted_tests x hx0 ?_ _ hm ?_
  · filter_upwards [hx] with j hj
    let η : ℝ := min (1/2) ((x j).re/2)
    have hη : 0 < η := lt_min (by norm_num) (by positivity)
    have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hs : 2 * η ≤ (x j).re := by
      have h : η ≤ (x j).re/2 := min_le_right _ _
      linarith
    refine ⟨η, hη, hη1, hs, hm.of_norm_bounded_eventually_nat ?_⟩
    filter_upwards [hsub η hη hη1] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
    exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  · filter_upwards [hboundary] with j hj n
    have hh : ‖witnessCharge n * shiftedTest n (x j)‖ ≤ ‖witnessCharge n‖ * E n := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hj n) (norm_nonneg _)
    exact (neg_le_neg ((Complex.abs_re_le_norm _).trans hh)).trans (neg_abs_le _)

end RiemannResearch.RH.MertensShiftedPairing
