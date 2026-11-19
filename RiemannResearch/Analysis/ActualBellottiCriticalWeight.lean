/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualLewkoCriticalWeight

/-!
# Critical exponential mass with a bounded number of zeros at the VK edge

Bellotti, *A new zero-density estimate for ζ(s) and the error term in the
prime number theorem*, Bull. London Math. Soc. **58** (2026), e70442,
doi:10.1112/blms.70442, Theorem 1.1 at α = 0. The proof in §3.1 counts
σ₀ ≤ β < 1 and X < γ ≤ T. Its disk bound (Lemma 2.4, based on the
logarithmic derivative) counts the analytic multiplicities.

For each fixed multiple of the asymptotic VK width, the actual inclusive
positive-height count remains bounded as T increases. At the critical
weight b = 2 each of these finitely many copies costs at most
T exp(−2(1 − bellottiAbscissa T) log T). The complete remainder is
bounded by the compact-strip and Huxley estimates with a smaller order.
The resulting normalized mass saves an extra full log T and retains the
coefficient 2. No fixed zero-free half-plane occurs in this argument.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Fixed-K specialization of Bellotti's Theorem 1.1. The fixed VK
constant is already included in 1 − bellottiAbscissa T. -/
def BellottiBoundedEdgeCount : Prop :=
  ∀ M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
    rightInclusiveCount T (1 - M * (1 - bellottiAbscissa T)) ≤ C

private theorem displacement_le_of_strictTail_zero {T U : ℝ} (h : strictTail T U = 0)
    (c : Copies T) : copyDisplacement T c ≤ U := by
  classical
  by_contra! hc
  let f := fun j : Copies T => if U < copyDisplacement T j then (1 : ℝ) else 0
  have hsum : f c ≤ ∑ j, f j :=
    Finset.single_le_sum (f := f) (fun i _ => by dsimp [f]; split_ifs <;> norm_num) (Finset.mem_univ c)
  have hz : (∑ j, f j) = 0 := h
  rw [hz] at hsum
  simp only [f, if_pos hc] at hsum
  norm_num at hsum

/-- A finite edge with E copies contributes at most E times its maximal
weight. Below D a uniform weighted tail budget transfers by layer cake. -/
private theorem exponential_sum_split_at_edge {T L δ D U K E : ℝ}
    (hL : 1 ≤ L) (hδ : 0 ≤ δ) (hδD : δ ≤ D) (hD : D ≤ 1 / 2)
    (hK : 0 ≤ K) (hzero : strictTail T U = 0) (hedge : strictTail T D ≤ E)
    (hbulk : ∀ t ∈ Icc δ D, strictTail T t * Real.exp (2 * L * t) ≤ K) :
    badWeightedSum T δ (fun t => Real.exp (2 * L * t)) ≤
      2 * K * L + E * Real.exp (2 * L * U) := by
  classical
  let s := (Finset.univ : Finset (Copies T))
  let d := copyDisplacement T
  let v := fun c : Copies T => min (d c) D
  let φ := fun t : ℝ => Real.exp (2 * L * t)
  let f := fun t : ℝ => 2 * L * φ t
  have hLp : 0 ≤ 2 * L := by linarith only [hL]
  have hd (c : Copies T) : d c ≤ U := displacement_le_of_strictTail_zero hzero c
  have ht (t : ℝ) : FiniteStrictTail.tail s v t ≤ strictTail T t := by
    apply Finset.sum_le_sum
    intro c _
    by_cases h : t < v c
    · have h' : t < copyDisplacement T c := h.trans_le (min_le_left _ _)
      simp only [if_pos h, if_pos h', le_refl]
    · simp only [if_neg h]; split_ifs <;> norm_num
  have hsum : badWeightedSum T δ φ ≤ FiniteStrictTail.badSum s v φ δ + strictTail T D * φ U := by
    unfold badWeightedSum strictTail FiniteStrictTail.badSum FiniteStrictTail.tail
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c _
    by_cases hDc : D < d c
    · have he : φ (d c) ≤ φ U := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hd c) hLp)
      have hδc := hδD.trans_lt hDc
      have hpos : 0 ≤ if δ < v c then φ (v c) else 0 := by split_ifs <;> positivity
      change (if δ < d c then φ (d c) else 0) ≤ _ + (if D < d c then 1 else 0) * φ U
      simp only [if_pos hDc, if_pos hδc, one_mul]
      linarith only [he, hpos]
    · have hv : v c = d c := min_eq_left (le_of_not_gt hDc)
      change (if δ < d c then φ (d c) else 0) ≤
        (if δ < v c then φ (v c) else 0) + (if D < d c then 1 else 0) * φ U
      rw [hv, if_neg hDc, zero_mul, add_zero]
  have hderiv (t : ℝ) : HasDerivAt φ (f t) t := by
    simpa only [φ, f, Function.comp_def, one_mul, mul_one, mul_comm] using
      (Real.hasDerivAt_exp (2 * L * t)).comp t ((hasDerivAt_id t).const_mul (2 * L))
  have hf : Continuous f := by dsimp [f, φ]; fun_prop
  have htv (t : ℝ) (ht' : t ∈ Icc δ D) : FiniteStrictTail.tail s v t * φ t ≤ K :=
    (mul_le_mul_of_nonneg_right (ht _) (Real.exp_pos _).le).trans (hbulk _ ht')
  have hint : (∫ t in δ..D, FiniteStrictTail.tail s v t * f t) ≤ ∫ _ in δ..D, 2 * L * K := by
    apply intervalIntegral.integral_mono_on hδD (FiniteStrictTail.intervalIntegrable_tail_mul s v f hf _ _)
      intervalIntegrable_const
    intro t ht'
    calc
      _ = 2 * L * (FiniteStrictTail.tail s v t * φ t) := by dsimp [f]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (htv _ ht') hLp
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hbase := htv δ ⟨le_rfl, hδD⟩
  have hKL := le_mul_of_one_le_right hK hL
  have hlen := mul_le_mul_of_nonneg_right (show D - δ ≤ 1 / 2 by linarith only [hD, hδ]) (mul_nonneg hLp hK)
  have hcap : FiniteStrictTail.badSum s v φ δ ≤ 2 * K * L := by
    rw [FiniteStrictTail.layerCake s v φ f hf hderiv δ D hδD (fun i _ => min_le_right _ _)]
    linarith only [hint, hbase, hKL, hlen]
  exact hsum.trans (add_le_add hcap (mul_le_mul_of_nonneg_right hedge (Real.exp_pos _).le))

private theorem eventually_bulk_bound {δ e : ℝ} (he : e < 0)
    (hcompact : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1/2 + δ) (7/8),
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ C * T ^ (1 + e))
    (hH : HuxleyDensityHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ ∈ Icc (1/2 + δ) (1 - 26 * (1 - bellottiAbscissa T)),
        rightInclusiveCount T σ * T ^ (2 * (σ - 1/2)) ≤
          C * T * (Real.exp (-2 * (1 - bellottiAbscissa T) * Real.log T) / Real.log T) := by
  obtain ⟨C, hC, hc⟩ := hcompact
  obtain ⟨H, hHpos, hH⟩ := hH
  let K := max C H
  have hK := hC.trans_le (le_max_left C H)
  refine ⟨K, hK, ?_⟩
  have hg : Tendsto (fun T : ℝ => 1 - bellottiAbscissa T) atTop (nhds 0) :=
    by simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_bellottiAbscissa
  filter_upwards [hc, hH, hg.eventually (Iio_mem_nhds (show 0 < -e/4 by linarith)),
    eventually_loglog_le_bellottiWidth 45 (by norm_num), eventually_gt_atTop (Real.exp 1)]
    with T hcomp hH' hsmall hlog hT
  let g := 1 - bellottiAbscissa T
  let L := Real.log T
  let l := Real.log L
  have hTp := (Real.exp_pos _).trans hT
  have hL : 1 < L := by simpa [L] using Real.log_lt_log (Real.exp_pos _) hT
  have hLp := zero_lt_one.trans hL
  have hlp : 0 < l := Real.log_pos hL
  have hgL : 45 * l ≤ g * L := (div_le_iff₀ hLp).mp hlog
  have hgp : 0 < g := by by_contra! h; nlinarith only [hgL, hlp, mul_nonpos_of_nonpos_of_nonneg h hLp.le]
  have hbound (c : ℝ) (hc' : c ≤ K) :
      c * Real.exp (L - 2*g*L - l) ≤ K * T * (Real.exp (-2*g*L) / L) := by
    calc
      _ = c * (T * (Real.exp (-2*g*L) / L)) := by
        rw [show L - 2*g*L - l = (L + -2*g*L) + -l by ring, Real.exp_add, Real.exp_add,
          Real.exp_neg l, Real.exp_log hLp, Real.exp_log hTp]
        dsimp [L]
        ring
      _ ≤ K * (T * (Real.exp (-2*g*L) / L)) := mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = _ := by ring
  intro σ hσ
  by_cases hs : σ ≤ 7 / 8
  · have h := hcomp σ ⟨hσ.1, hs⟩
    have hsmall' : g < -e / 4 := hsmall
    have hex := mul_lt_mul_of_pos_right hsmall' hLp
    have he' : L * (1 + e) ≤ L - 2*g*L - l := by linarith only [hex, hgL, hlp]
    rw [Real.rpow_def_of_pos hTp (1 + e)] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he') hC.le).trans (hbound _ (le_max_left _ _)))
  · have hhi : σ ≤ 1 - 26 * g := hσ.2
    have hσ1 : σ ≤ 1 := by linarith only [hhi, hgp]
    have hx := hH' σ ⟨by linarith only [lt_of_not_ge hs], hσ1⟩
    let F := 3 * (1 - σ) / (3 * σ - 1)
    have hm := (huxley_critical_weight_margin (σ₀ := (7 / 8 : ℝ)) (by norm_num)).2 σ ⟨(lt_of_not_ge hs).le, hσ1⟩
    rw [show (2 - 3 / (3 * (7/8) - 1) : ℝ) = 2/13 by norm_num] at hm
    have hm' : L * (F + 2*(σ - 1/2)) ≤ L * (1 - (2/13)*(1-σ)) :=
      mul_le_mul_of_nonneg_left hm hLp.le
    have hs' := mul_le_mul_of_nonneg_right hhi hLp.le
    have he' : L*F + l*44 + L*(2*(σ-1/2)) ≤ L - 2*g*L - l := by linarith only [hm', hs', hgL, hlp]
    calc
      _ ≤ (H * T ^ F * L ^ (44 : ℝ)) * T ^ (2*(σ-1/2)) :=
        mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hTp.le _)
      _ = H * Real.exp (L*F + l*44 + L*(2*(σ-1/2))) := by
        rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos hTp, Real.rpow_def_of_pos hLp,
          Real.rpow_def_of_pos hTp]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he') hHpos.le).trans (hbound _ (le_max_right _ _))

/-- The bounded edge gives the exact VK stretch and an inverse logarithm
at every fixed displacement above one quarter. -/
theorem normalized_critical_weight_vkEdgeDecay_of_lewko (hLw : LewkoDensityHypothesis)
    (hH : HuxleyDensityHypothesis) (hV : BellottiKorobovVinogradovNonvanishing)
    (hEdge : BellottiBoundedEdgeCount) {δ : ℝ} (hδ : δ ∈ Ioc (1 / 4 : ℝ) (1 / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
        C * (Real.exp (-2 * (1 - bellottiAbscissa T) * Real.log T) / Real.log T) := by
  by_cases hhalf : 1 / 2 ≤ δ
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    rw [badWeightedSum_eq_zero_of_half_le T δ _ hhalf, zero_div]
    exact mul_nonneg (by norm_num) (div_nonneg (Real.exp_pos _).le (Real.log_pos hT).le)
  let lo := min (1 / 2 + δ) (7 / 8)
  have hlo : 3 / 4 < lo := lt_min (by linarith only [hδ.1]) (by norm_num)
  let E := lewkoCriticalWeightExponent lo (7/8)
  have hE : E < 0 := lewkoCriticalWeightExponent_neg hlo (min_le_right _ _) (by norm_num)
  obtain ⟨J, hJ, hj⟩ := weighted_compact_count_of_lewko hLw hlo (min_le_right _ _) (by norm_num : (7/8 : ℝ) ≤ 1)
    (show 0 < -E/2 by linarith)
  have hbulk := eventually_bulk_bound (δ := δ) (e := E/2) (by linarith) (by
    refine ⟨J, hJ, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    intro σ hσ
    have h := hj T hT σ ⟨(min_le_left _ _).trans hσ.1, hσ.2⟩
    have heq : 1 + (lewkoCriticalWeightExponent lo (7/8) + -E/2) = 1 + E/2 := by change 1 + (E + -E/2) = _; ring
    simpa only [heq] using h) hH
  obtain ⟨K, hK, hb⟩ := hbulk
  obtain ⟨F, hF, hf⟩ := hEdge 26 (by norm_num)
  refine ⟨16 * Real.pi * (4 * K + 2 * F), by positivity, ?_⟩
  have hg : Tendsto (fun T : ℝ => 1 - bellottiAbscissa T) atTop (nhds 0) :=
    by simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_bellottiAbscissa
  filter_upwards [hb, hf, bellotti_count_of_nonvanishing hV, eventually_count_ge_log,
    hg.eventually (Iio_mem_nhds (show 0 < (1/2 - δ)/26 by linarith only [lt_of_not_ge hhalf])),
    eventually_loglog_le_bellottiWidth 1 (by norm_num), eventually_gt_atTop (Real.exp 1)]
    with T hbc hfc hzero hN hg' hgpos hT
  let L := Real.log T
  let g := 1 - bellottiAbscissa T
  let D := 1 / 2 - 26 * g
  let U := 1 / 2 - g
  let W := Real.exp (-2 * g * L)
  have hTp := (Real.exp_pos _).trans hT
  have hL : 1 < L := by simpa [L] using Real.log_lt_log (Real.exp_pos _) hT
  have hLp := zero_lt_one.trans hL
  have hgp : 0 ≤ g := (div_nonneg (mul_nonneg zero_le_one (Real.log_pos hL).le) hLp.le).trans hgpos
  have hδ₀ : 0 ≤ δ := by linarith only [hδ.1]
  have hδD : δ ≤ D := by change g < (1/2 - δ)/26 at hg'; dsimp [D]; linarith only [hg']
  have hDU : D ≤ U := by dsimp [D,U]; linarith only [hgp]
  have heD : 1/2 + D = 1 - 26*g := by dsimp [D]; ring
  have heU : 1/2 + U = bellottiAbscissa T := by dsimp [U,g]; ring
  have htailD := strictTail_le_twice_inclusive T D (hδ₀.trans hδD)
  rw [heD] at htailD
  have htailU := strictTail_le_twice_inclusive T U ((hδ₀.trans hδD).trans hDU)
  change rightInclusiveCount T (bellottiAbscissa T) = 0 at hzero
  rw [heU, hzero, mul_zero] at htailU
  have htail (t : ℝ) (ht : t ∈ Icc δ D) :
      strictTail T t * Real.exp (2 * L * t) ≤ 2 * (K * T * (W / L)) := by
    have hc := hbc (1/2 + t) ⟨by linarith only [ht.1], by dsimp [D,g] at ht; linarith only [ht.2]⟩
    rw [show 1/2 + t - 1/2 = t by ring, Real.rpow_def_of_pos hTp] at hc
    have h := mul_le_mul_of_nonneg_right (strictTail_le_twice_inclusive T t (hδ₀.trans ht.1)) (Real.exp_pos (2*L*t)).le
    rw [show 2*L*t = Real.log T*(2*t) by dsimp [L]; ring] at h ⊢
    linarith only [h, hc]
  have h := exponential_sum_split_at_edge hL.le hδ₀ hδD (show D ≤ 1/2 by dsimp [D]; linarith only [hgp])
    (show 0 ≤ 2*(K*T*(W/L)) by dsimp [W]; positivity) (le_antisymm htailU (strictTail_nonneg _ _))
    (htailD.trans (mul_le_mul_of_nonneg_left hfc (by norm_num))) htail
  have he : Real.exp (2 * L * U) = T * W := by
    rw [show 2*L*U = L + -2*g*L by dsimp [U]; ring, Real.exp_add, Real.exp_log hTp]
  rw [he] at h
  have hNpos := lt_of_lt_of_le (show 0 < (1/(16 * Real.pi)) * T * L by positivity) hN
  apply (div_le_iff₀ hNpos).mpr
  calc
    _ ≤ _ := h
    _ = 16 * Real.pi * (4*K + 2*F) * (W/L) * ((1/(16*Real.pi))*T*L) := by field_simp [Real.pi_ne_zero, hLp.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by dsimp [W]; positivity)

end RiemannResearch.Analysis.ActualZeroOrdinate
