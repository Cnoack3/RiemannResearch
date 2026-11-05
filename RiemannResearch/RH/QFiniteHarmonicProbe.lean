/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QResolventHarmonicPrefix
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QCofinalHarmonicWitness
import RiemannResearch.RH.QSignedChargeTail
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QMertensUniformDefectSlope
import RiemannResearch.Analysis.CofinalPrimeResiduePairing
import RiemannResearch.Analysis.CofinalLogCutoffs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-window cofinal tests using finite, matched Gram projections

The prime and Möbius probes of QCofinalDisplacementMoments are put inside
the finite conductor dictionary before testing the finite normal equations.
This permits a single physical prefix of a single finite projection difference
at each scale, with a prescribed cutoff as small as twice its square root.
The probes use the squarefree dictionary of Bagchi, Remark 8
(https://arxiv.org/pdf/math/0607733). The bound on the finite signed masses
is an arithmetic hypothesis.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSignedTailRigidity
open QSquarefreeDisplacementRigidity QAnnihilatorTailEscape QShiftedReciprocal
open RiemannResearch.Analysis RiemannResearch.Analysis.CofinalMoments

/-- Exact finite annihilator arising from the two projections onto one dictionary. -/
def finiteWitness (M : ℕ) : QHilbert := B (qOne - finitePFit M) - finiteDisplacement M

theorem finiteWitness_tendsto : Tendsto finiteWitness atTop (𝓝 witness) :=
  ((B.continuous.tendsto pResidual).comp
    (tendsto_const_nhds.sub finitePFit_tendsto)).sub finiteDisplacement_tendsto

private theorem residue_in_stage (M d : ℕ) (hd : 0 < d) (hs : Squarefree d)
    (hcap : d ≤ M + 1) : qResidue d ∈ stage M := by
  by_cases h : d = 1
  · rw [h, qResidue_one]
    exact (stage M).zero_mem
  · change qResidue d ∈ Submodule.span ℝ (Set.range (fun i : Fin M => squarefreeAtom i))
    apply Submodule.subset_span
    refine ⟨⟨d - 2, by omega⟩, ?_⟩
    change squarefreeAtom (d - 2) = qResidue d
    simp [squarefreeAtom, show d - 2 + 2 = d by omega, hs]

theorem exactHead_in_stage (M N : ℕ) (hs : Squarefree (N + 1)) (hNM : N ≤ M) :
    QMobiusExactHead.exactHead N ∈ stage M := by
  unfold QMobiusExactHead.exactHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    by_cases hsf : Squarefree d
    · exact (stage M).smul_mem _ (residue_in_stage M d hd1 hsf (by omega))
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  · exact (stage M).smul_mem _ (residue_in_stage M (N + 1) (by omega) hs (by omega))

theorem finite_prime_pairing (M p : ℕ) (hp : p.Prime) (hcap : p ≤ M + 1) :
    HasSum (fun n : ℕ => signedCoefficient (finiteWitness M) n * ((n % p : ℕ) : ℝ)) 0 := by
  apply residue_charge_hasSum_zero _ p hp.pos
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (residue_in_stage M p hp.pos hp.squarefree hcap) (finite_witness_mem_orthogonal M)

theorem finite_defect_pairing (M N : ℕ) (hs : Squarefree (N + 1)) (hNM : N ≤ M) :
    HasSum (fun n => signedCoefficient (finiteWitness M) n * qSequence (defect N) n)
      (inner ℝ qOne (finiteWitness M)) := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (exactHead_in_stage M N hs hNM) (finite_witness_mem_orthogonal M)
  change inner ℝ (QMobiusExactHead.exactHead N) (finiteWitness M) = 0 at hz
  have he : inner ℝ (finiteWitness M) (defect N) = inner ℝ qOne (finiteWitness M) := by
    rw [real_inner_comm, defect, inner_sub_left, hz, sub_zero]
  rw [← he, qInner_weighted]
  exact (qSequence_product_summable (finiteWitness M) (defect N)).hasSum

private theorem charge_prefix (u : QHilbert) (ε : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), max (ε * signedCoefficient u n) 0 * (n : ℝ)) =
      harmonicSideOf u ε X / zetaTwo := by
  rw [harmonicSideOf, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hpos := positiveQWeight_nonneg n
  have hpart : max (ε * signedCoefficient u n) 0 =
      positiveQWeight n * max (ε * qSequence u n) 0 := by
    rw [signedCoefficient, mul_left_comm ε (positiveQWeight n)]
    rcases le_total 0 (ε * qSequence u n) with h | h
    · rw [max_eq_left h, max_eq_left (mul_nonneg hpos h)]
    · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hpos h), mul_zero]
  rw [hpart]
  by_cases h : n = 0
  · simp [h]
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    unfold positiveQWeight
    field_simp [hn, zetaTwo_pos.ne']

private theorem witness_charge_prefix (u d : QHilbert) (ε : ℝ) (hε : |ε| = 1) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), max ((-ε) * signedCoefficient (B u - d) n) 0 * (n : ℝ)) ≤
      ‖u‖ + harmonicSideOf d ε X / zetaTwo := by
  have hsmooth : (∑ n ∈ Finset.range (X + 1), |signedCoefficient (B u) n| * (n : ℝ)) ≤ ‖u‖ := by
    calc
      _ ≤ ∑ n ∈ Finset.range (X + 1), positiveQWeight n * |qSequence u n| := by
        apply Finset.sum_le_sum
        intro n _
        rw [signedCoefficient, qSequence_B, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n),
          abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
        calc
          _ = (positiveQWeight n * |qSequence u n|) * ((n : ℝ) / ((n : ℝ) + 1)) := by ring
          _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (positiveQWeight_nonneg n) (abs_nonneg _))
            ((div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith))
      _ ≤ qL1 u := (qL1_summable u).sum_le_tsum _ fun n _ =>
        mul_nonneg (positiveQWeight_nonneg n) (abs_nonneg _)
      _ ≤ _ := qL1_le_norm u
  have hpoint (n : ℕ) : max ((-ε) * signedCoefficient (B u - d) n) 0 ≤
      |signedCoefficient (B u) n| + max (ε * signedCoefficient d n) 0 := by
    apply max_le
    · have hb := neg_le_abs (ε * signedCoefficient (B u) n)
      rw [abs_mul, hε, one_mul] at hb
      rw [signedCoefficient_sub]
      linarith [le_max_left (ε * signedCoefficient d n) 0]
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _)
  calc
    _ ≤ ∑ n ∈ Finset.range (X + 1),
        (|signedCoefficient (B u) n| * (n : ℝ) + max (ε * signedCoefficient d n) 0 * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, charge_prefix]
      exact add_le_add hsmooth le_rfl

set_option maxHeartbeats 800000 in
-- Elaborating the signed finite-sum bound unfolds both finite projection fits.
theorem finite_local_bound
    (M N p X Y : ℕ) (δ : ℝ) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hs : Squarefree (N + 1)) (hp : p.Prime) (hNM : N ≤ M) (hpM : p ≤ M + 1)
    (hYX : Y ≤ X) (hYp : Y < p)
    (hlin : ∀ n : ℕ, n ≤ Y → |qSequence (defect N) n| ≤ δ * n) :
    |inner ℝ qOne (finiteWitness M)| ≤ 2 * δ * (‖qOne - finitePFit M‖ +
      minimumHarmonicPrefixOf (finiteDisplacement M) X / zetaTwo) +
      (δ * (p : ℝ)) * (∑' n : ℕ, if X < n then |signedCoefficient (finiteWitness M) n| else 0) +
      (3 * (N : ℝ)) * (∑' n : ℕ, if Y < n then |signedCoefficient (finiteWitness M) n| else 0) := by
  have existsSign : ∃ s : ℝ, |s| = 1 ∧ harmonicSideOf (finiteDisplacement M) s X =
      minimumHarmonicPrefixOf (finiteDisplacement M) X := by
    rcases le_total (harmonicSideOf (finiteDisplacement M) 1 X)
      (harmonicSideOf (finiteDisplacement M) (-1) X) with h | h
    · exact ⟨1, abs_one, (min_eq_left h).symm⟩
    · exact ⟨-1, by norm_num, (min_eq_right h).symm⟩
  obtain ⟨ε, hε, hside⟩ := existsSign
  let c := -ε
  have hc : |c| = 1 := by simpa only [c, abs_neg] using hε
  let b := signedCoefficient (finiteWitness M)
  have hsumm := (signedCoefficient_summable (finiteWitness M)).mul_left c
  have hm := (finite_defect_pairing M N hs hNM).mul_left c
  have hz := (finite_prime_pairing M p hp hpM).mul_left c
  have h := pairing_le_local_residue_head (fun n => c * b n) (qSequence (defect N))
    X Y p (c * inner ℝ qOne (finiteWitness M)) δ (3 * (N : ℝ)) hYX hYp hδ hsumm
    (by simpa only [b, mul_assoc] using hm)
    (by simpa only [b, mul_assoc, mul_zero] using hz) hlin
    (fun n _ => QMertensFirstMoment.abs_defect_le_three_mul N n hN)
  simp only [abs_mul, hc, one_mul] at h
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_two hδ)
  simpa only [c, b, finiteWitness, hside] using
    witness_charge_prefix (qOne - finitePFit M) (finiteDisplacement M) ε hε X

private theorem generic_scaled_tail (w : QHilbert) (X : ℕ) (R : ℝ) (hR : R ^ 2 ≤ (X : ℝ) + 1) :
    R * (∑' n : ℕ, if X < n then |signedCoefficient w n| else 0) ≤
      ‖w‖ ^ 2 + 2 / zetaTwo := by
  have e (n : ℕ) :
      (if n ∈ Finset.range (X + 1) then (0 : ℝ) else |signedCoefficient w n|) =
      (if X < n then |signedCoefficient w n| else 0) := by
    by_cases h : X < n
    · simp [Finset.mem_range, not_le.mpr h, h]
    · simp [Finset.mem_range, le_of_not_gt h, h]
  simpa only [e] using scaled_absoluteCoefficient_tail_le w X R hR

theorem finite_mean_eighth_power_bound (A : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ, 2 * k ^ 4 ≤ M →
      |inner ℝ qOne (finiteWitness M)| ≤
        (2 / (6 + Real.log (k : ℝ)) ^ A) *
          (‖qOne - finitePFit M‖ +
            minimumHarmonicPrefixOf (finiteDisplacement M) (k ^ 8) / zetaTwo) +
        2 * (‖finiteWitness M‖ ^ 2 + 2 / zetaTwo) / (6 + Real.log (k : ℝ)) ^ A +
        6 * (‖finiteWitness M‖ ^ 2 + 2 / zetaTwo) / (k : ℝ) := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (QMertensFirstMoment.eventually_abs_defect_le_div_shifted_log_pow A)
  filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
  intro M hM
  have h1 : 1 ≤ k := (le_max_right _ _).trans hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast h1
  obtain ⟨N, p, hs, hkN, hN2, hp, hYp, hp2⟩ :=
    exists_eighth_power_prime_scales (show 0 < k by omega)
  have hN : 0 < N := by omega
  let L := (6 + Real.log (k : ℝ)) ^ A
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hlin (n : ℕ) : |qSequence (defect N) n| ≤ (1 / L) * n := by
    have hNN := hk₀ N ((le_max_left _ _).trans (hk.trans hkN)) n
    have hpow : L ≤ (6 + Real.log (N : ℝ)) ^ A :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 6 + Real.log (k : ℝ))
        (add_le_add_right (Real.log_le_log hkR (by exact_mod_cast hkN)) 6) A
    calc
      _ ≤ _ := hNN
      _ ≤ (n : ℝ) / L := div_le_div_of_nonneg_left (Nat.cast_nonneg n) hL hpow
      _ = _ := by ring
  have hXY : k ^ 4 ≤ k ^ 8 := Nat.pow_le_pow_right h1 (by decide)
  have hk4 : k ≤ k ^ 4 := by simpa using (Nat.pow_le_pow_right h1 (show 1 ≤ 4 by decide))
  have h := finite_local_bound M N p (k ^ 8) (k ^ 4) (1 / L)
    hN (one_div_nonneg.mpr hL.le) hs.squarefree hp (by omega) (by omega) hXY hYp (fun n _ => hlin n)
  let T := ‖finiteWitness M‖ ^ 2 + 2 / zetaTwo
  let tailB (X : ℕ) := ∑' n : ℕ, if X < n then |signedCoefficient (finiteWitness M) n| else 0
  have ht (X : ℕ) : 0 ≤ tailB X :=
    tsum_nonneg (fun n => by split <;> simp [abs_nonneg])
  have h8 : (k : ℝ) ^ 4 * tailB (k ^ 8) ≤ T := by
    apply generic_scaled_tail
    push_cast
    nlinarith only [show 0 ≤ (1 : ℝ) by norm_num,
      show ((k : ℝ) ^ 4) ^ 2 = (k : ℝ) ^ 8 by ring]
  have h4 : (k : ℝ) ^ 2 * tailB (k ^ 4) ≤ T := by
    apply generic_scaled_tail
    push_cast
    nlinarith only [show 0 ≤ (1 : ℝ) by norm_num,
      show ((k : ℝ) ^ 2) ^ 2 = (k : ℝ) ^ 4 by ring]
  have hpR : (p : ℝ) ≤ 2 * (k : ℝ) ^ 4 := by exact_mod_cast hp2
  have hNR : (N : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hN2
  have ht8 : (1 / L * (p : ℝ)) * tailB (k ^ 8) ≤ 2 * T / L := by
    apply (le_div_iff₀ hL).2
    calc
      _ = (p : ℝ) * tailB (k ^ 8) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpR (ht _)
      _ ≤ 2 * T := by dsimp only [tailB] at *; linarith
  have ht4 : (3 * (N : ℝ)) * tailB (k ^ 4) ≤ 6 * T / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    calc
      _ ≤ (3 * (2 * (k : ℝ)) * tailB (k ^ 4)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNR (by norm_num)) (ht _)) hkR.le
      _ = 6 * ((k : ℝ) ^ 2 * tailB (k ^ 4)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by norm_num)
  change _ ≤ (2 / L) * _ + 2 * T / L + 6 * T / (k : ℝ)
  rw [show 2 / L = 2 * (1 / L) by ring]
  exact h.trans (add_le_add (add_le_add le_rfl ht8) ht4)

/-- A polylogarithmic bound on just one prefix of one finite matched Gram
difference for arbitrarily large k suffices. The scale is k ^ 8 and any
stage schedule covering the prime probe at 2 * k ^ 4 works. -/
theorem riemannHypothesis_of_finite_probe_prefix (m : ℕ → ℕ)
    (hm : ∀ᶠ k : ℕ in atTop, 2 * k ^ 4 ≤ m k) (E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (h : ∃ᶠ k : ℕ in atTop, minimumHarmonicPrefixOf (finiteDisplacement (m k)) (k ^ 8) ≤
      C * (Real.log (k : ℝ)) ^ E) : RiemannHypothesis := by
  have hmTop : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro L
    filter_upwards [hm, eventually_ge_atTop (max L 1)] with k hmk hk
    have hk1 : 1 ≤ k := (le_max_right L 1).trans hk
    have hk4 : k ≤ k ^ 4 := by simpa using Nat.pow_le_pow_right hk1 (show 1 ≤ 4 by decide)
    omega
  obtain ⟨A, hEA⟩ := exists_nat_ge E
  let S := ‖pResidual‖ + 1
  let T := ‖witness‖ ^ 2 + 2 / zetaTwo + 1
  let C' := C / zetaTwo
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T :=
    add_nonneg (add_nonneg (sq_nonneg _) (div_nonneg zero_le_two zetaTwo_pos.le)) zero_le_one
  have hC' : 0 ≤ C' := div_nonneg hC zetaTwo_pos.le
  have hpLim : Tendsto (fun k => ‖qOne - finitePFit (m k)‖) atTop (𝓝 ‖pResidual‖) :=
    (tendsto_const_nhds.sub (finitePFit_tendsto.comp hmTop)).norm
  have hW := finiteWitness_tendsto.comp hmTop
  have hwLim : Tendsto (fun k => ‖finiteWitness (m k)‖ ^ 2 + 2 / zetaTwo) atTop
        (𝓝 (‖witness‖ ^ 2 + 2 / zetaTwo)) :=
    (hW.norm.pow 2).add tendsto_const_nhds
  have hmean : Tendsto (fun k => |inner ℝ qOne (finiteWitness (m k))|) atTop
        (𝓝 |inner ℝ qOne witness|) := (tendsto_const_nhds.inner hW).abs
  have hbound := finite_mean_eighth_power_bound (A + 2)
  let F := fun k : ℕ => (2 / (6 + Real.log (k : ℝ)) ^ (A + 2)) *
      (S + C' * (Real.log (k : ℝ)) ^ E) + 2 * T / (6 + Real.log (k : ℝ)) ^ (A + 2) +
      6 * T / (k : ℝ)
  have hF : Tendsto F atTop (𝓝 0) := tendsto_budget A E S C' T hE hEA hS hC' hT
  have hle : ∃ᶠ k : ℕ in atTop, |inner ℝ qOne (finiteWitness (m k))| ≤ F k := by
    apply (h.and_eventually (hm.and (hbound.and ((eventually_ge_atTop (1 : ℕ)).and
      ((hpLim.eventually (gt_mem_nhds (show ‖pResidual‖ < S by dsimp [S]; linarith))).and
       (hwLim.eventually (gt_mem_nhds (show ‖witness‖ ^ 2 + 2 / zetaTwo < T by
         dsimp [T]; linarith)))))))).mono
    rintro k ⟨hg, hmk, hb, hk, hp, hw⟩
    refine (hb (m k) hmk).trans ?_
    have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
    have hpow : 0 ≤ (6 + Real.log (k : ℝ)) ^ (A + 2) := by positivity
    refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hp.le ?_)
      (div_nonneg (by norm_num) hpow)) ?_) ?_
    · simpa only [C', div_mul_eq_mul_div] using div_le_div_of_nonneg_right hg zetaTwo_pos.le
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw.le (by norm_num)) hpow
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw.le (by norm_num))
        (Nat.cast_nonneg k)
  exact riemannHypothesis_of_witness_mean_zero
    (abs_nonpos_iff.mp (le_of_tendsto_of_tendsto_of_frequently hmean hF hle))

/-- The prescribed conductor schedule leaves just one arithmetic bound on one
finite Gram pair per good physical window. -/
theorem riemannHypothesis_of_sqrt_stage_harmonic_prefix (E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (h : ∃ᶠ k : ℕ in atTop,
      minimumHarmonicPrefixOf (finiteDisplacement (2 * k ^ 4)) (k ^ 8) ≤
        C * (Real.log (k : ℝ)) ^ E) : RiemannHypothesis :=
  riemannHypothesis_of_finite_probe_prefix (fun k => 2 * k ^ 4)
    (Eventually.of_forall fun _ => le_rfl) E C hE hC h

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
