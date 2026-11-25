import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import RiemannResearch.RH.PrimeTreeGridLaw
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Continuous macroscopic tests of the actual zeta-zero ordinates

Each uniform height bin has an exact multiplicity count given by a difference
of cumulative counts. Its normalized mass tends to the bin length. Uniform
continuity extends the resulting finite-grid law to all continuous tests.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate RiemannResearch.RH.PrimeTreeHaarRows

private def cellStep (b x : ℝ) : ℝ := if x ≤ b then 1 else 0

private theorem scaledHeightCount_eq_steps {T b : ℝ} (hT : 1 < T) (hb : b ≤ 1) :
    scaledHeightCount T b = (∑ i : Copies T, cellStep b (copyOrdinate T i / T)) /
      unfoldedCutoff T := by
  have ht := zero_lt_one.trans hT
  rw [scaledHeightCount, cumulative_copy_steps (by simpa using mul_le_mul_of_nonneg_right hb ht.le)]
  simp only [cellStep, div_le_iff₀ ht]

/-- The normalized actual ordinate heights integrate every continuous real
test against the uniform law on the closed unit interval. Every zero is
included with its analytic multiplicity. -/
theorem scaledHeightTest_tendsto (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto (fun T : ℝ => (∑ i : Copies T, g (copyOrdinate T i / T)) / unfoldedCutoff T)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, g x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 5 := by linarith
  obtain ⟨δ,hδ,hu⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) (ε/5) he
  have hquad := Metric.tendsto_nhds.mp (gridMean_tendsto g hg) (ε/5) he
  obtain ⟨n,hn,hd,hq⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ).and hquad)).exists
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let p := fun j : ℕ => (j : ℝ) / n
  have hp₀ : p 0 = 0 := by simp [p]
  have hpₙ : p n = 1 := by simp [p,hnR.ne']
  have hp (k : ℕ) : 0 ≤ p k := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hp₁ (k : ℕ) (hk : k ≤ n) : p k ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hk)
  have hmono (k : ℕ) : p k ≤ p (k+1) :=
    (div_le_div_iff_of_pos_right hnR).mpr (by exact_mod_cast Nat.le_succ k)
  have hstep (k : ℕ) : p (k+1) - p k = 1/(n : ℝ) := by
    simp only [p,Nat.cast_add,Nat.cast_one]
    ring
  let W := fun (k : ℕ) (x : ℝ) => cellStep (p (k+1)) x - cellStep (p k) x
  have hmass (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      (∑ k ∈ Finset.range n, W k x) = 1 := by
    unfold W
    rw [Finset.sum_range_sub (fun k => cellStep (p k) x) n, hp₀,hpₙ]
    simp [cellStep,hx.2,not_le.mpr hx.1]
  have hrow (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      |g x - ∑ k ∈ Finset.range n, g (p k) * W k x| ≤ ε/5 := by
    have hosc (k : ℕ) (hk : k ∈ Finset.range n) :
        |g x * W k x - g (p k) * W k x| ≤ (ε/5) * W k x := by
      by_cases hlo : x ≤ p k
      · simp [W,cellStep,hlo,hlo.trans (hmono k)]
      by_cases hhi : x ≤ p (k+1)
      · have hk' := (Finset.mem_range.mp hk).le
        have hdist : dist x (p k) ≤ δ := by
          rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hlo))]
          linarith only [hhi,hstep k,hd]
        have hgu := hu x ⟨hx.1.le,hx.2⟩ (p k) ⟨hp k,hp₁ k hk'⟩ hdist
        simpa [W,cellStep,hlo,hhi,Real.dist_eq] using hgu
      · simp [W,cellStep,hlo,hhi]
    have hgx : g x = ∑ k ∈ Finset.range n, g x * W k x := by
      rw [← Finset.mul_sum,hmass x hx,mul_one]
    have hdiff : g x - ∑ k ∈ Finset.range n, g (p k) * W k x =
        ∑ k ∈ Finset.range n, (g x * W k x - g (p k) * W k x) := by
      rw [Finset.sum_sub_distrib, ← hgx]
    rw [hdiff]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans_eq (by
      rw [← Finset.mul_sum,hmass x hx,mul_one]))
  let bins := fun T : ℝ => ∑ k ∈ Finset.range n, g (p k) *
    (scaledHeightCount T (p (k+1)) - scaledHeightCount T (p k))
  have hlimit : Tendsto bins atTop (𝓝 (gridMean g n)) := by
    have h := tendsto_finsetSum (Finset.range n) (fun k _ =>
      ((scaledHeightCount_tendsto (hp (k+1))).sub (scaledHeightCount_tendsto (hp k))).const_mul
        (g (p k)))
    have heq : (∑ k ∈ Finset.range n, g (p k) * (p (k+1) - p k)) = gridMean g n := by
      simp only [hstep,gridMean,p,mul_one_div,Finset.sum_div]
    rwa [heq] at h
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_count_div_mainTerm.eventually_lt_const (show (1:ℝ) < 2 by norm_num),
    Metric.tendsto_nhds.mp hlimit (ε/5) he] with T hT hN hb
  have ht := zero_lt_one.trans hT
  let x := fun i : Copies T => copyOrdinate T i / T
  let D := unfoldedCutoff T
  have hD : 0 < D := div_pos (mul_pos ht (Real.log_pos hT)) (by positivity)
  have hx (i : Copies T) : x i ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (mem_cutoff.mp i.1.property).2.1 ht,
      (div_le_iff₀ ht).mpr (by rw [one_mul]; exact (mem_cutoff.mp i.1.property).2.2)⟩
  have hbrow : bins T = (∑ i : Copies T, ∑ k ∈ Finset.range n, g (p k) * W k (x i)) / D := by
    calc
      bins T = ∑ k ∈ Finset.range n, (∑ i : Copies T, g (p k) * W k (x i)) / D := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn := Finset.mem_range.mp hk
        rw [scaledHeightCount_eq_steps hT (hp₁ _ hkn),scaledHeightCount_eq_steps hT (hp₁ _ hkn.le),
          ← sub_div, ← Finset.sum_sub_distrib, ← Finset.mul_sum]
        change g (p k) * (_ / D) = (g (p k) * _) / D
        ring
      _ = _ := by rw [← Finset.sum_div,Finset.sum_comm]
  have herr : |(∑ i : Copies T, g (x i)) / D - bins T| ≤ 2*(ε/5) := by
    rw [hbrow,← sub_div,abs_div,abs_of_pos hD,← Finset.sum_sub_distrib]
    have hs := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Copies T))) => hrow (x i) (hx i)))
    simp only [Finset.sum_const,Finset.card_univ,card_copies,nsmul_eq_mul] at hs
    apply (div_le_div_of_nonneg_right hs hD.le).trans
    change (Ncount 0 T : ℝ) / D < 2 at hN
    calc (Ncount 0 T : ℝ) * (ε / 5) / D = ((Ncount 0 T : ℝ) / D) * (ε / 5) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hN.le he.le
  have htotal := dist_triangle ((∑ i : Copies T, g (x i)) / D) (bins T) (∫ u in (0 : ℝ)..1, g u)
  have hmid := dist_triangle (bins T) (gridMean g n) (∫ u in (0 : ℝ)..1, g u)
  rw [Real.dist_eq] at hb hq
  simp only [Real.dist_eq] at htotal hmid ⊢
  change |(∑ i : Copies T, g (x i)) / D - (∫ u in (0 : ℝ)..1, g u)| < ε
  linarith only [htotal,hmid,hb,hq,herr,hε]

end RiemannResearch.Analysis.MontgomeryPositiveGap
