/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteSchurEighth
import RiemannResearch.RH.QPrimeForcingObstruction
import RiemannResearch.NumberTheory.CofinalPrimeGaps

/-! # Divergence of the unrestricted inverse Schur evaluation rows

Three head evaluations isolate a prime contrast. The inverse diagonal is large
when a nearby legal conductor has small contrast energy. A cofinal family of
close prime pairs forces a large row budget, uniformly over all larger stages.
The matched input is a specific vector of signed averages of a Pareto residual.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert QSquarefreeTailResponse QSquarefreeSchurCoercivity ArithmeticCumulative
open RiemannResearch.Analysis.FiniteHilbertGram RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertConstraints RiemannResearch.Analysis.FiniteGramCoercivity

private def primeCharge (p : ℕ) : QHilbert →L[ℝ] ℝ :=
  qEvalCLM 1 - qEvalCLM p + qEvalCLM (p - 1)

private theorem primeCharge_apply (p : ℕ) (x : QHilbert) :
    primeCharge p x = qSequence x 1 - qSequence x p + qSequence x (p-1) := by
  simp [primeCharge]

private theorem primeCharge_scaled_residue (p d : ℕ) (hp : p.Prime) (hd : 2 ≤ d) :
    primeCharge p ((d : ℝ) • qResidue d) = if d = p then (p : ℝ) else 0 := by
  rw [map_smul, primeCharge_apply]
  simp only [smul_eq_mul, qSequence_qResidue]
  have hj := SquarefreeRadicalDifference.residueFraction_difference d p hd hp.pos
  have h1 : residueFraction d 1 = 1 / (d : ℝ) := by
    simp only [residueFraction, Nat.mod_eq_of_lt (show 1 < d by omega), Nat.cast_one]
  rw [h1]
  by_cases he : d = p
  · subst d
    rw [if_pos rfl]
    rw [if_pos (dvd_refl p)] at hj
    have heq : 1 / (p : ℝ) - residueFraction p p + residueFraction p (p - 1) = 1 := by
      linarith
    rw [heq, mul_one]
  · have hnd : ¬ d ∣ p := fun h => ((Nat.dvd_prime hp).mp h).elim (fun h1 => by omega) he
    rw [if_neg he]
    rw [if_neg hnd, sub_zero] at hj
    have heq : 1 / (d : ℝ) - residueFraction d p + residueFraction d (p - 1) = 0 := by
      linarith
    rw [heq, mul_zero]

private theorem primeCharge_schur (N T d0 : ℕ) (p : lowConductors T) (hp : p.val.Prime)
    (ha : T < d0) (i : Option (lowConductors T)) :
    primeCharge p.val (squarefreeSchurFamily N T d0 i) =
      if i = some p then (p.val : ℝ) else 0 := by
  have hpd := ((mem_lowConductors T p.val).mp p.property).1
  let W := tailStage N T
  let u := squarefreeHeadFamily T d0 i
  have hm : W.starProjection u ∈ headNull T := (W.starProjection_apply_mem u).2
  have hz : primeCharge p.val (W.starProjection u) = 0 := by
    rw [primeCharge_apply,
      physical_zero_of_mem hm 1 (by omega),
      physical_zero_of_mem hm p.val hpd.2,
      physical_zero_of_mem hm (p.val - 1) (by omega)]
    ring
  change primeCharge p.val (u - W.starProjection u) = _
  rw [map_sub, hz, sub_zero]
  have h0 : primeCharge p.val ((d0 : ℝ) • qResidue d0) = 0 := by
    rw [primeCharge_scaled_residue p.val d0 hp (by omega), if_neg (by omega)]
  cases i with
  | none => exact h0
  | some t =>
    change primeCharge p.val ((t.val : ℝ) • qResidue t.val - (d0 : ℝ) • qResidue d0) = _
    rw [map_sub, h0, sub_zero, primeCharge_scaled_residue p.val t.val hp
      (((mem_lowConductors T t.val).mp t.property).1.1)]
    by_cases ht : t = p
    · subst t; simp
    · have hv : t.val ≠ p.val := fun he => ht (Subtype.ext he)
      simp [ht, hv]

/-- At a low prime, three physical rows extract the corresponding inverse-Gram row. -/
theorem prime_schur_row_charge (N T d0 : ℕ) (p : lowConductors T)
    (hp : p.val.Prime) (ha : T < d0) (j : Option (lowConductors T)) :
    schurEvaluationRow N T d0 1 j - schurEvaluationRow N T d0 p.val j +
        schurEvaluationRow N T d0 (p.val - 1) j =
      (p.val : ℝ) * (gramMatrix (squarefreeSchurFamily N T d0))⁻¹ (some p) j := by
  classical
  let v := squarefreeSchurFamily N T d0
  let A := (gramMatrix v)⁻¹
  change (∑ i, qSequence (v i) 1 * A i j) - (∑ i, qSequence (v i) p.val * A i j) +
      (∑ i, qSequence (v i) (p.val - 1) * A i j) = _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i, (if i = some p then (p.val : ℝ) else 0) * A i j := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := primeCharge_schur N T d0 p hp ha i
      rw [primeCharge_apply] at h
      change qSequence (v i) 1 - qSequence (v i) p.val + qSequence (v i) (p.val-1) = _ at h
      rw [← h]
      ring
    _ = _ := by simp [ite_mul, A, v]

/-- Testing two low conductor rows costs at most the raw (unscreened) contrast energy. -/
theorem prime_schur_diagonal_contrast (N T d0 : ℕ) (p d : lowConductors T)
    (hT : 1 ≤ T) (ha : T < d0) (hne : d ≠ p) :
    1 ≤ (gramMatrix (squarefreeSchurFamily N T d0))⁻¹ (some p) (some p) *
          ‖(p.val : ℝ) • qResidue p.val - (d.val : ℝ) • qResidue d.val‖^2 := by
  classical
  let v := squarefreeSchurFamily N T d0
  let b : Option (lowConductors T) → ℝ := fun i => if i = some p then 1 else 0
  have hv : LinearIndependent ℝ v := squarefreeSchurFamily_linearIndependent N T d0 hT ha
  have he : capacity hv b = (gramMatrix v)⁻¹ (some p) (some p) := by
    calc
      _ = inverseSource hv b (some p) := by
        simp [capacity, b, mul_ite]
      _ = (gramMatrix v)⁻¹.mulVec b (some p) := congrFun (gramMatrix_inverseSource hv b).symm _
      _ = _ := by simp [Matrix.mulVec, dotProduct, b, mul_ite]
  have hobs : inner ℝ (v (some p) - v (some d)) (minimumVector hv b) = 1 := by
    rw [inner_sub_left, minimumVector_observation, minimumVector_observation]
    simp [b, hne]
  have hcs : (1 : ℝ) ≤ capacity hv b * ‖v (some p) - v (some d)‖^2 := by
    have h := real_inner_mul_inner_self_le (v (some p) - v (some d)) (minimumVector hv b)
    rw [hobs, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← capacity_eq_norm_sq] at h
    simpa only [one_mul, mul_comm] using h
  let a : QHilbert := (p.val : ℝ) • qResidue p.val - (d.val : ℝ) • qResidue d.val
  let W := tailStage N T
  have hs : v (some p) - v (some d) = a - W.starProjection a := by
    change (((p.val : ℝ) • qResidue p.val - (d0 : ℝ) • qResidue d0) -
        W.starProjection ((p.val : ℝ) • qResidue p.val - (d0 : ℝ) • qResidue d0)) -
      (((d.val : ℝ) • qResidue d.val - (d0 : ℝ) • qResidue d0) -
        W.starProjection ((d.val : ℝ) • qResidue d.val - (d0 : ℝ) • qResidue d0)) =
      ((p.val : ℝ) • qResidue p.val - (d.val : ℝ) • qResidue d.val) -
        W.starProjection ((p.val : ℝ) • qResidue p.val - (d.val : ℝ) • qResidue d.val)
    simp only [map_sub]
    abel
  have hnorm : ‖v (some p) - v (some d)‖^2 ≤ ‖a‖^2 := by
    have h := RiemannResearch.Analysis.projection_trial_energy W a 0 (Submodule.zero_mem _)
    rw [sub_zero, sub_zero] at h
    rw [hs]
    linarith only [h, sq_nonneg ‖W.starProjection a‖]
  have hfinal := hcs.trans (mul_le_mul_of_nonneg_left hnorm (capacity_nonneg hv b))
  rw [he] at hfinal
  exact hfinal

private theorem row_site_eighth_le (N T d0 p n : ℕ) (hn : 0 < n) (hpn : n ≤ p)
    (hN : n ≤ N) (i : Option (lowConductors T)) :
    |schurEvaluationRow N T d0 n i|^8 ≤ (p : ℝ) ^ 2 * schurRowEighthHead N T d0 := by
  classical
  let e (k : ℕ) := ∑ j, (schurEvaluationRow N T d0 k j) ^ 2
  have hpos (k : ℕ) : 0 ≤ e k := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsite : (schurEvaluationRow N T d0 n i) ^ 2 ≤ e n :=
    Finset.single_le_sum (fun j _ => sq_nonneg (schurEvaluationRow N T d0 n j))
      (Finset.mem_univ i)
  have hpart : (e n) ^ 4 / (n : ℝ) ^ 2 ≤ schurRowEighthHead N T d0 :=
    Finset.single_le_sum (s := Finset.range (N+1))
      (f := fun k => (e k) ^ 4 / (k : ℝ) ^ 2) (fun k _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hN))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow : 0 ≤ schurRowEighthHead N T d0 := by
    unfold schurRowEighthHead
    exact Finset.sum_nonneg (fun k _ => by positivity)
  have hnle : (n : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
    gcongr
  calc
    _ = ((schurEvaluationRow N T d0 n i) ^ 2) ^ 4 := by
      rw [Even.pow_abs (by decide : Even 8)]; ring
    _ ≤ (e n) ^ 4 := pow_le_pow_left₀ (sq_nonneg _) hsite 4
    _ ≤ schurRowEighthHead N T d0 * (n : ℝ) ^ 2 := (div_le_iff₀ (sq_pos_of_pos hnR)).mp hpart
    _ ≤ schurRowEighthHead N T d0 * (p : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hnle hrow
    _ = _ := mul_comm _ _

/-- Universal row budgets must pay for every nearby pair of low conductors
whose upper member is prime. This argument uses only real, legal atoms. -/
theorem prime_schur_row_eighth_obstruction (N T d0 : ℕ) (p d : lowConductors T)
    (hp : p.val.Prime) (hne : d ≠ p) (hTN : T ≤ N) (ha : T < d0) :
    (p.val : ℝ) ^ 8 ≤ ((3 : ℝ) ^ 8 * (p.val : ℝ) ^ 2 * schurRowEighthHead N T d0) *
      ‖(p.val : ℝ) • qResidue p.val - (d.val : ℝ) • qResidue d.val‖^16 := by
  classical
  have hpd := ((mem_lowConductors T p.val).mp p.property).1
  let G := (gramMatrix (squarefreeSchurFamily N T d0))⁻¹ (some p) (some p)
  let a := ‖(p.val : ℝ) • qResidue p.val - (d.val : ℝ) • qResidue d.val‖
  let R := fun k => schurEvaluationRow N T d0 k (some p)
  let M := max |R 1| (max |R p.val| |R (p.val - 1)|)
  have h1 : R 1 ≤ M := (le_abs_self _).trans (le_max_left _ _)
  have h2 : -R p.val ≤ M := (neg_le_abs _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h3 : R (p.val-1) ≤ M := (le_abs_self _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hc : R 1 - R p.val + R (p.val - 1) = (p.val : ℝ)*G :=
    prime_schur_row_charge N T d0 p hp ha (some p)
  have hvar : 1 ≤ G * a ^ 2 := prime_schur_diagonal_contrast N T d0 p d (by omega) ha hne
  have hG : 0 ≤ G := by
    by_contra! hbad
    have hn := mul_nonpos_of_nonpos_of_nonneg hbad.le (sq_nonneg a)
    linarith only [hvar, hn]
  have hpR : (0 : ℝ) ≤ p.val := Nat.cast_nonneg _
  have hpG : 0 ≤ (p.val : ℝ) * G := mul_nonneg hpR hG
  have hpeak : (p.val : ℝ) * G ≤ 3 * M := by linarith only [h1,h2,h3,hc]
  have hM : M ^ 8 ≤ (p.val : ℝ) ^ 2 * schurRowEighthHead N T d0 := by
    have h (k : ℕ) (hpos : 0 < k) (hle : k ≤ p.val) :
        |R k|^8 ≤ (p.val : ℝ) ^ 2 * schurRowEighthHead N T d0 :=
      row_site_eighth_le N T d0 p.val k hpos hle (by omega) (some p)
    dsimp only [M]
    simp only [max_def]
    split_ifs <;> first | exact h 1 (by omega) (by omega)
                        | exact h p.val hp.pos le_rfl
                        | exact h (p.val - 1) (by omega) (by omega)
  have hfinal : ((p.val : ℝ) * G) ^ 8 ≤
      (3 : ℝ) ^ 8 * (p.val : ℝ) ^ 2 * schurRowEighthHead N T d0 := by
    calc
      _ ≤ (3 * M) ^ 8 := pow_le_pow_left₀ hpG hpeak 8
      _ = (3 : ℝ) ^ 8 * M ^ 8 := mul_pow _ _ _
      _ ≤ (3 : ℝ) ^ 8 * ((p.val : ℝ) ^ 2 * schurRowEighthHead N T d0) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  have hpbound : (p.val : ℝ) ≤ (p.val : ℝ) * G * a ^ 2 := by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hvar hpR
  calc
    _ ≤ ((p.val : ℝ) * G * a ^ 2) ^ 8 := pow_le_pow_left₀ hpR hpbound 8
    _ = ((p.val : ℝ) * G) ^ 8 * a ^ 16 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfinal (by positivity : 0 ≤ a ^ 16)

open ZetaTwoHilbert ZetaTwoProbability QSquarefreeSchurCoercivity
open RiemannResearch.NumberTheory

private theorem eventually_log_le_eighth_power :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (1 / 8 : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  change ‖Real.log x‖ ≤ (1 : ℝ) * ‖x ^ (1 / 8 : ℝ)‖ at hx
  have hx0 : 0 ≤ x := by linarith
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hx

private theorem small_gap_contrast_sixteenth (p q : ℕ) (hp : p.Prime) (hq : 0 < q)
    (hqp : q ≤ p) (hgap : ((p - q : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ))
    (hlog : Real.log (p : ℝ) ≤ (p : ℝ) ^ (1 / 8 : ℝ)) :
    ‖(p : ℝ) • qResidue p - (q : ℝ) • qResidue q‖ ^ 16 ≤
      (4 / zetaTwo : ℝ) ^ 8 * (p : ℝ) ^ 5 := by
  let F := 2 * (1 + Real.log (p : ℝ)) / zetaTwo
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hL0 := Real.log_nonneg hp1
  have hz := zetaTwo_pos
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hR : (1 : ℝ) ≤ (p : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow hp1 (by norm_num)
  have hF : F ≤ (4 / zetaTwo : ℝ) * (p : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ (4 * (p : ℝ) ^ (1 / 8 : ℝ)) / zetaTwo :=
        div_le_div_of_nonneg_right (by linarith only [hR, hlog]) hz.le
      _ = _ := by ring
  have hF8 : F ^ 8 ≤ (4 / zetaTwo : ℝ) ^ 8 * (p : ℝ) := by
    have hid : ((p : ℝ) ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = (p : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
      norm_num
    simpa only [mul_pow, hid] using pow_le_pow_left₀ hF0 hF 8
  have hg16 : ((p - q : ℕ) : ℝ) ^ 16 ≤ (p : ℝ) ^ 4 := by
    calc
      _ ≤ ((p : ℝ) ^ (1 / 4 : ℝ)) ^ (16 : ℕ) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hgap 16
      _ = _ := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ (1 / 4 : ℝ)), ← Real.rpow_mul hp0]
        norm_num
  have hs : (Real.sqrt F) ^ (16 : ℕ) = F ^ 8 := by
    calc
      _ = ((Real.sqrt F) ^ 2) ^ (8 : ℕ) := by ring
      _ = _ := by rw [Real.sq_sqrt hF0]
  have hn : ‖(p : ℝ) • qResidue p - (q : ℝ) • qResidue q‖
      ≤ ((p - q : ℕ) : ℝ) * Real.sqrt F :=
    QPrimeForcingObstruction.raw_residue_gap_norm_le_log p q hq hqp
  calc
    _ ≤ (((p - q : ℕ) : ℝ) * Real.sqrt F) ^ (16 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hn 16
    _ = ((p - q : ℕ) : ℝ) ^ 16 * F ^ 8 := by rw [mul_pow, hs]
    _ ≤ (p : ℝ) ^ 4 * ((4 / zetaTwo : ℝ) ^ 8 * (p : ℝ)) :=
      mul_le_mul hg16 hF8 (pow_nonneg hF0 _) (pow_nonneg hp0 _)
    _ = _ := by ring

/-- The unrestricted Euclidean row budget grows beyond every fixed bound,
uniformly in the stage and the high anchor as the input cutoff grows. -/
theorem schurRowEighthHead_uniformly_eventually_ge (C : ℝ) :
    ∃ T₀ : ℕ, ∀ N T d0 : ℕ, T₀ ≤ T → T ≤ N → T < d0 →
      C ≤ schurRowEighthHead N T d0 := by
  classical
  let K : ℝ := (3 : ℝ) ^ 8 * (4 / zetaTwo : ℝ) ^ 8
  have hz := zetaTwo_pos
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨X, hX⟩ := eventually_atTop.1 eventually_log_le_eighth_power
  obtain ⟨B, hB⟩ := exists_nat_ge X
  obtain ⟨D, hD⟩ := exists_nat_ge (K * C)
  obtain ⟨q, p, hpair, hq, hp, hqp, hgap⟩ := exists_primes_gap_le_quarter_power (max B D)
  have hBp : B ≤ p := ((le_max_left _ _).trans hpair).trans hqp.le
  have hDp : D ≤ p := ((le_max_right _ _).trans hpair).trans hqp.le
  have hlog := hX (p : ℝ) (hB.trans (by exact_mod_cast hBp))
  have hn := small_gap_contrast_sixteenth p q hp hq.pos hqp.le hgap hlog
  refine ⟨p, ?_⟩
  intro N T d0 hpT hTN ha
  let i : lowConductors T :=
    ⟨p, (mem_lowConductors T p).mpr ⟨⟨hp.two_le, hpT⟩, hp.squarefree⟩⟩
  let j : lowConductors T :=
    ⟨q, (mem_lowConductors T q).mpr ⟨⟨hq.two_le, hqp.le.trans hpT⟩, hq.squarefree⟩⟩
  have hji : j ≠ i := fun he => hqp.ne (congrArg Subtype.val he)
  let R := schurRowEighthHead N T d0
  have hR : 0 ≤ R := by
    unfold R schurRowEighthHead
    exact Finset.sum_nonneg fun k _ => by positivity
  have ho := prime_schur_row_eighth_obstruction N T d0 i j hp hji hTN ha
  change (p : ℝ) ^ 8 ≤ ((3 : ℝ) ^ 8 * (p : ℝ) ^ 2 * R) *
    ‖(p : ℝ) • qResidue p - (q : ℝ) • qResidue q‖^16 at ho
  have hscaled : (p : ℝ) ^ 7 * (p : ℝ) ≤ (p : ℝ) ^ 7 * (K * R) := calc
    _ = (p : ℝ) ^ 8 := by ring
    _ ≤ _ := ho
    _ ≤ ((3 : ℝ) ^ 8 * (p : ℝ) ^ 2 * R) * ((4 / zetaTwo : ℝ) ^ 8 * (p : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by dsimp only [K]; ring
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl := (mul_le_mul_iff_right₀ (pow_pos hp0 7)).mp hscaled
  have hc : K * C ≤ (p : ℝ) := hD.trans (by exact_mod_cast hDp)
  exact (mul_le_mul_iff_right₀ hK).mp (hc.trans hl)

/-- The obstruction also allows the high anchor to move with the stage. -/
theorem schurRowEighthHead_tendsto_atTop (T d0 : ℕ → ℕ) (hT : Tendsto T atTop atTop)
    (ha : ∀ᶠ N : ℕ in atTop, T N < d0 N ∧ d0 N ≤ N + 1) :
    Tendsto (fun N => schurRowEighthHead N (T N) (d0 N)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  obtain ⟨B, hB⟩ := schurRowEighthHead_uniformly_eventually_ge C
  filter_upwards [hT.eventually (eventually_ge_atTop B), ha] with N hBN hN
  exact hB N (T N) (d0 N) hBN (by have := hN.1; have := hN.2; omega) hN.1

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
