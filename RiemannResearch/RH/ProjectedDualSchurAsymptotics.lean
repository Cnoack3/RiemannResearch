import RiemannResearch.RH.ProjectedDualSchurMass
import RiemannResearch.RH.ParetoPrimeSourceDivergence
/-!
# Schur amplification and a relative little-o bound

Source: continuation of the user's inverse-column investigation, 28 September
2026. The proof splits the summable coefficient-mode energy before applying
Cauchy--Schwarz. For every fixed d it gives B_(n,d)^2=o(S_n), where
S_n is the accumulated squared l1 mass of normalized Gram--Schmidt modes.
The existing arithmetic atom-norm bound also gives S_n>=n(n+3)/4.
This is a relative estimate, not a sub-stretched upper bound for B or S.
No RH hypothesis or quantitative concentration provider is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open RiemannResearch.Analysis.FiniteHilbertGram
open ProjectionSchur

/-- Small atom norms force a growing coefficient mass for each normalized mode. -/
theorem residueModeCoefficientMass_sq_ge_half_stage (n : ℕ) :
    ((n+2:ℕ):ℝ)/2 ≤ residueModeCoefficientMass n ^2 := by
  have hs := residueModeScale_pos n
  have hc := modeCoefficient_diagonal_pos n
  have hi : inner ℝ (residueAtom n) (residueMode n) = residueModeScale n := by
    simpa using residueAtom_inner_mode n n le_rfl
  have hcs := real_inner_le_norm (residueAtom n) (residueMode n)
  rw [hi, residueMode_orthonormal.1 n, mul_one] at hcs
  have ha : ‖residueAtom n‖ ^ 2 ≤ 2 / ((n+2:ℕ):ℝ) :=
    normalizedResidue_norm_sq_le (n+2) (by omega)
  have hs2 := ((sq_le_sq₀ hs.le (norm_nonneg _)).mpr hcs).trans ha
  have hden : residueModeScale n ^2 * ((n+2:ℕ):ℝ) ≤ 2 :=
    (le_div_iff₀ (by positivity)).mp hs2
  have hmul : modeCoefficient (n+2) n ^2 * residueModeScale n ^2 = 1 := by
    rw [← mul_pow, modeCoefficient_mul_scale]; norm_num
  have hdiag : ((n+2:ℕ):ℝ)/2 ≤ modeCoefficient (n+2) n ^2 := by
    have hh := mul_le_mul_of_nonneg_left hden (sq_nonneg (modeCoefficient (n+2) n))
    have he : modeCoefficient (n+2) n ^2 * (residueModeScale n ^2 * ((n+2:ℕ):ℝ)) =
        ((n+2:ℕ):ℝ) := by rw [← mul_assoc, hmul, one_mul]
    rw [he] at hh
    linarith
  have hm : modeCoefficient (n+2) n ≤ residueModeCoefficientMass n := by
    rw [residueModeCoefficientMass]
    calc
      _ = |modeCoefficient (n+2) n| := (abs_of_pos hc).symm
      _ ≤ ∑ k : Fin (n+1), |modeCoefficient (k.val+2) n| := by
        simpa only [Fin.val_last] using
          Finset.single_le_sum (fun k _ => abs_nonneg (modeCoefficient (k.val+2) n))
            (Finset.mem_univ (Fin.last n))
  exact hdiag.trans ((sq_le_sq₀ hc.le (hc.le.trans hm)).mpr hm)

theorem schur_amplification_energy_ge_quadratic (n : ℕ) :
    (n:ℝ) * ((n:ℝ)+3) / 4 ≤
      ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := residueModeCoefficientMass_sq_ge_half_stage n
    push_cast at h ⊢
    nlinarith


/-- Split the Schur envelope into a finite part and a summable mode tail. -/
theorem projectedDualCoefficientMass_sq_le_split_schur
    (n d M : ℕ) (hMn : M ≤ n) :
    projectedDualCoefficientMass n d ^ 2 ≤
      2 * (∑ j ∈ Finset.range M,
        |modeCoefficient d j| * residueModeCoefficientMass j) ^ 2 +
      2 * ((∑' j : ℕ, modeCoefficient d j ^ 2) -
        ∑ j ∈ Finset.range M, modeCoefficient d j ^ 2) *
        ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2 := by
  let H : ℝ := ∑ j ∈ Finset.range M,
    |modeCoefficient d j| * residueModeCoefficientMass j
  let T : ℝ := ∑ j ∈ Finset.Ico M n,
    |modeCoefficient d j| * residueModeCoefficientMass j
  let R : ℝ := (∑' j : ℕ, modeCoefficient d j ^ 2) -
    ∑ j ∈ Finset.range M, modeCoefficient d j ^ 2
  let S : ℝ := ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2
  have hA (j : ℕ) : 0 ≤ residueModeCoefficientMass j :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hA j))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hA j))
  have hm := projectedDualCoefficientMass_le_accumulated_schur n d
  simp_rw [← residueModeCoefficientMass_eq_schur] at hm
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j => |modeCoefficient d j| * residueModeCoefficientMass j) hMn
  have hmass : projectedDualCoefficientMass n d ≤ H + T := by
    dsimp [H, T]
    rw [hsplit]
    exact hm
  have hm0 : 0 ≤ projectedDualCoefficientMass n d :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hm2 : projectedDualCoefficientMass n d ^ 2 ≤ (H + T) ^ 2 :=
    (sq_le_sq₀ hm0 (add_nonneg hH hT)).mpr hmass
  have hmn := Summable.sum_le_tsum (Finset.range n)
    (fun _ _ => sq_nonneg _) (modeCoefficient_sq_summable d)
  have hsplitm := Finset.sum_range_add_sum_Ico
    (fun j => modeCoefficient d j ^ 2) hMn
  have hmt : (∑ j ∈ Finset.Ico M n, modeCoefficient d j ^ 2) ≤ R := by
    dsimp [R]
    linarith
  have hmt0 : 0 ≤ ∑ j ∈ Finset.Ico M n, modeCoefficient d j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ R := hmt0.trans hmt
  have hsplita := Finset.sum_range_add_sum_Ico
    (fun j => residueModeCoefficientMass j ^ 2) hMn
  have hheadA : 0 ≤ ∑ j ∈ Finset.range M, residueModeCoefficientMass j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hat : (∑ j ∈ Finset.Ico M n, residueModeCoefficientMass j ^ 2) ≤ S := by
    dsimp [S]
    linarith
  have hat0 : 0 ≤ ∑ j ∈ Finset.Ico M n, residueModeCoefficientMass j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico M n)
    (fun j => |modeCoefficient d j|) residueModeCoefficientMass
  simp only [sq_abs] at hcs
  have hT2 : T ^ 2 ≤ R * S := hcs.trans (mul_le_mul hmt hat hat0 hR)
  change projectedDualCoefficientMass n d ^ 2 ≤ 2 * H ^ 2 + 2 * R * S
  nlinarith [sq_nonneg (H - T)]

/-- Bessel summability makes the squared mass negligible relative to the
complete amplification energy; it supplies no absolute growth rate. -/
theorem projectedDualCoefficientMass_sq_eventually_le_schur
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      projectedDualCoefficientMass n d ^ 2 ≤
        ε * ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2 := by
  let total : ℝ := ∑' j : ℕ, modeCoefficient d j ^ 2
  have hpartial : Tendsto (fun M : ℕ =>
      ∑ j ∈ Finset.range M, modeCoefficient d j ^ 2) atTop (𝓝 total) :=
    (modeCoefficient_sq_summable d).hasSum.tendsto_sum_nat
  have ht : Tendsto (fun M : ℕ => total -
      ∑ j ∈ Finset.range M, modeCoefficient d j ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := total)).sub hpartial
    rw [sub_self] at h
    exact h
  obtain ⟨M, hM⟩ := (ht.eventually_lt_const (show 0 < ε / 4 by positivity)).exists
  let H : ℝ := ∑ j ∈ Finset.range M,
    |modeCoefficient d j| * residueModeCoefficientMass j
  have hlarge : ∀ᶠ n : ℕ in atTop, 4 * H ^ 2 / ε ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlarge, eventually_ge_atTop M] with n hn hMn
  let S : ℝ := ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2
  let R : ℝ := (∑' j : ℕ, modeCoefficient d j ^ 2) -
    ∑ j ∈ Finset.range M, modeCoefficient d j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hlargeS : 4 * H ^ 2 / ε ≤ S :=
    hn.trans (schur_amplification_energy_ge_stage n)
  have hhead : 4 * H ^ 2 ≤ S * ε := (div_le_iff₀ hε).mp hlargeS
  have hR : R ≤ ε / 4 := hM.le
  have htail : R * S ≤ (ε / 4) * S := mul_le_mul_of_nonneg_right hR hS
  have hb := projectedDualCoefficientMass_sq_le_split_schur n d M hMn
  change projectedDualCoefficientMass n d ^ 2 ≤ 2 * H ^ 2 + 2 * R * S at hb
  change projectedDualCoefficientMass n d ^ 2 ≤ ε * S
  nlinarith

theorem projectedDualCoefficientMass_sq_isLittleO_schur (d : ℕ) :
    (fun n : ℕ => projectedDualCoefficientMass n d ^ 2) =o[atTop]
      (fun n => ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [projectedDualCoefficientMass_sq_eventually_le_schur d ε hε] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (projectedDualCoefficientMass n d)),
    Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ ∑ j ∈ Finset.range n, residueModeCoefficientMass j ^ 2 from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact hn

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
