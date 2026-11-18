import RiemannResearch.Analysis.GramLogarithmicDerivative
import RiemannResearch.Analysis.SchurMatrixDerivative
import Mathlib.Tactic.Abel
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.PosDef
import RiemannResearch.RH.ChebyshevEnergyCriterion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Dirichlet Gram matrices on a finite period

Source: C. Noack's CRT carry and zeta trace note (13 October 2026).
Hurwitz's progression formula is used entrywise (DLMF 25.11.1).
The normalized Gram has an explicit limit at the pole of zeta, namely
the uniform Gram of the period. The corresponding determinant ratio has
the uniform-period limit whenever its base determinant is nonzero.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.PeriodicDirichletGram

variable {D : ℕ} [NeZero D] {ι : Type*}

/-- Bilinear continuation of the Gram of fixed real periodic features. -/
def gram (φ : ZMod D → ι → ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  fun i j => ZMod.LFunction (fun a => ((φ a i * φ a j : ℝ) : ℂ)) s

def normalized (φ : ZMod D → ι → ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  (riemannZeta s)⁻¹ • gram φ s

def periodGram (φ : ZMod D → ι → ℝ) : Matrix ι ι ℂ :=
  fun i j => (∑ a : ZMod D, ((φ a i * φ a j : ℝ) : ℂ)) / (D : ℂ)

theorem gram_hurwitz (φ : ZMod D → ι → ℝ) (s : ℂ) (i j : ι) :
    gram φ s i j = (D : ℂ) ^ (-s) * ∑ a : ZMod D,
      ((φ a i * φ a j : ℝ) : ℂ) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) s := rfl

theorem gram_dirichlet (φ : ZMod D → ι → ℝ) {s : ℂ} (hs : 1 < s.re) (i j : ι) :
    gram φ s i j = LSeries (fun n : ℕ => ((φ n i * φ n j : ℝ) : ℂ)) s :=
  ZMod.LFunction_eq_LSeries _ hs

theorem gram_residue_one (φ : ZMod D → ι → ℝ) (i j : ι) :
    Tendsto (fun s => (s - 1) * gram φ s i j) (𝓝[≠] 1) (𝓝 (periodGram φ i j)) :=
  by simpa only [gram, periodGram, Finset.sum_div] using
       ZMod.LFunction_residue_one (fun a : ZMod D => ((φ a i * φ a j : ℝ) : ℂ))

private theorem zeta_residue :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  simpa [ZMod.LFunction_modOne_eq] using
    (ZMod.LFunction_residue_one (fun _ : ZMod 1 => (1 : ℂ)))

theorem normalized_tendsto_periodGram (φ : ZMod D → ι → ℝ) :
    Tendsto (normalized φ) (𝓝[≠] 1) (𝓝 (periodGram φ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (gram_residue_one φ i j).div zeta_residue one_ne_zero
  rw [div_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  change (s - 1) * gram φ s i j / ((s - 1) * riemannZeta s) =
    (riemannZeta s)⁻¹ * gram φ s i j
  rw [mul_div_mul_left _ _ hs']
  ring

/-- The literal log-weighted Dirichlet series is retained in the normalized derivative. -/
theorem normalized_entry_hasDerivAt (φ : ZMod D → ι → ℝ)
    {s : ℂ} (hs : 1 < s.re) (i j : ι) :
    HasDerivAt (fun u => normalized φ u i j)
      (-(deriv riemannZeta s / riemannZeta s) * normalized φ s i j -
        LSeries (LSeries.logMul (fun n : ℕ => ((φ n i * φ n j : ℝ) : ℂ))) s / riemannZeta s) s := by
  let F : ℕ → ℂ := fun n => ((φ n i * φ n j : ℝ) : ℂ)
  have ha : LSeries.abscissaOfAbsConv F ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun t ht =>
      ZMod.LSeriesSummable_of_one_lt_re (fun a => ((φ a i * φ a j : ℝ) : ℂ)) (by simpa using ht))
  have hd := LSeries_hasDerivAt (f := F) (s := s) (ha.trans_lt (by exact_mod_cast hs))
  have hnear : (fun u => gram φ u i j) =ᶠ[𝓝 s] LSeries F := by
    filter_upwards [Complex.continuous_re.continuousAt.tendsto.eventually (lt_mem_nhds hs)] with u hu
    exact gram_dirichlet φ hu i j
  have h₁ := hd.congr_of_eventuallyEq hnear
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hs1 : s ≠ 1 := fun e => by simp [e] at hs
  have h₂ := (differentiableAt_riemannZeta hs1).hasDerivAt
  have hq := h₁.div h₂ hz
  have he (u : ℂ) : normalized φ u i j = gram φ u i j / riemannZeta u := by
    simp [normalized, div_eq_mul_inv, mul_comm]
  simp_rw [he]
  change HasDerivAt ((fun u => gram φ u i j) / riemannZeta) _ s
  apply hq.congr_deriv
  dsimp [F]
  field_simp [hz]
  <;> ring

theorem gram_entry_meromorphic (φ : ZMod D → ι → ℝ) (i j : ι) :
    Meromorphic (fun s => gram φ s i j) := by
  intro s
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have hp : AnalyticAt ℂ (fun w : ℂ => (D : ℂ) ^ (-w)) s := by
    simp only [Complex.cpow_def_of_ne_zero hD]
    fun_prop
  have hH (a : ZMod D) : MeromorphicAt (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a)) s := by
    have h := (HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta (ZMod.toAddCircle a) 0).analyticAt s
    have hz := RiemannResearch.RH.ChebyshevMellin.riemannZeta_meromorphicAt_everywhere s
    convert h.meromorphicAt.add hz using 1
    funext u
    simp [HurwitzZeta.hurwitzZeta_zero]
  change MeromorphicAt (fun w => (D : ℂ) ^ (-w) * ∑ a : ZMod D,
    ((φ a i * φ a j : ℝ) : ℂ) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) w) s
  apply hp.meromorphicAt.mul
  have hm := MeromorphicAt.sum (s := (Finset.univ : Finset (ZMod D)))
    (fun a _ => ((analyticAt_const (v := ((φ a i * φ a j : ℝ) : ℂ)) :
      AnalyticAt ℂ (fun _ : ℂ => ((φ a i * φ a j : ℝ) : ℂ)) s).meromorphicAt).mul (hH a))
  have he : (∑ a : ZMod D, (fun _ : ℂ => ((φ a i * φ a j : ℝ) : ℂ)) *
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a)) =
      (fun w => ∑ a : ZMod D, ((φ a i * φ a j : ℝ) : ℂ) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) w) := by
    funext w
    simp only [Finset.sum_apply, Pi.mul_apply]
  rwa [he] at hm

section Determinants
variable [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gram_det_meromorphic (φ : ZMod D → ι → ℝ) : Meromorphic (fun u => (gram φ u).det) := by
  classical
  intro s
  simp only [Matrix.det_apply']
  apply MeromorphicAt.fun_sum
  intro σ _
  apply MeromorphicAt.fun_mul (analyticAt_const.meromorphicAt)
  apply MeromorphicAt.fun_prod
  intro i _
  exact gram_entry_meromorphic φ (σ i) i s

/-- A meromorphic continuation of the Schur determinant quotient. Local factors at zeros may cancel. -/
theorem dirichlet_ratio_meromorphic (base : ZMod D → ι → ℝ) (join : ZMod D → (ι ⊕ κ) → ℝ) :
    Meromorphic (fun u => (gram join u).det /
      (riemannZeta u ^ Fintype.card κ * (gram base u).det)) := by
  intro s
  have hz := RiemannResearch.RH.ChebyshevMellin.riemannZeta_meromorphicAt_everywhere s
  exact (gram_det_meromorphic join s).fun_div
    ((hz.fun_pow _).fun_mul (gram_det_meromorphic base s))

/-- Gram of the log-weighted Dirichlet series in the normalized measure. -/
def logMoment (φ : ZMod D → ι → ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  fun i j => LSeries (LSeries.logMul (fun n : ℕ => ((φ n i * φ n j : ℝ) : ℂ))) s / riemannZeta s

/-- The full derivative retains the weighted leverage trace. -/
theorem normalized_det_logDeriv (φ : ZMod D → ι → ℝ) {s : ℂ} (hs : 1 < s.re)
    (hdet : (normalized φ s).det ≠ 0) :
    deriv (fun u => (normalized φ u).det) s / (normalized φ s).det =
      (Fintype.card ι : ℂ) * (-(deriv riemannZeta s / riemannZeta s)) -
        ((normalized φ s)⁻¹ * logMoment φ s).trace := by
  let μ := -(deriv riemannZeta s / riemannZeta s)
  have h (i j : ι) : HasDerivAt (fun u => normalized φ u i j)
      ((μ • normalized φ s - logMoment φ s) i j) s := normalized_entry_hasDerivAt φ hs i j
  rw [GramLogarithmicDerivative.det_logDeriv h hdet, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  ring

private theorem det_differentiableAt (φ : ZMod D → ι → ℝ) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun u => (normalized φ u).det) s :=
  (GramLogarithmicDerivative.det_hasDerivAt
    (fun i j => normalized_entry_hasDerivAt φ hs i j)).differentiableAt

/-- The dimension difference and the entire join-minus-base leverage correction. -/
theorem joined_det_ratio_logDeriv (base : ZMod D → ι → ℝ) (join : ZMod D → (ι ⊕ κ) → ℝ)
    {s : ℂ} (hs : 1 < s.re) (hb : (normalized base s).det ≠ 0) (hj : (normalized join s).det ≠ 0) :
    let F := fun u => (normalized join u).det / (normalized base u).det
    deriv F s / F s =
      (Fintype.card κ : ℂ) * (-(deriv riemannZeta s / riemannZeta s)) -
      (((normalized join s)⁻¹ * logMoment join s).trace -
        ((normalized base s)⁻¹ * logMoment base s).trace) := by
  dsimp only
  change deriv ((fun u => (normalized join u).det) / (fun u => (normalized base u).det)) s / _ = _
  rw [deriv_div (det_differentiableAt join hs) (det_differentiableAt base hs) hb]
  calc
    _ = deriv (fun u => (normalized join u).det) s / (normalized join s).det -
        deriv (fun u => (normalized base u).det) s / (normalized base s).det := by
          field_simp [hb, hj]

    _ = _ := by
      rw [normalized_det_logDeriv join hs hj, normalized_det_logDeriv base hs hb, Fintype.card_sum, Nat.cast_add]
      ring

/-- The normalized determinant ratio of a joined family and its base. -/
theorem det_ratio (base : ZMod D → ι → ℝ) (join : ZMod D → (ι ⊕ κ) → ℝ)
    (s : ℂ) (hz : riemannZeta s ≠ 0) :
    (normalized join s).det / (normalized base s).det =
    (gram join s).det / ((riemannZeta s) ^ Fintype.card κ * (gram base s).det) := by
  simp only [normalized, Matrix.det_smul, Fintype.card_sum, pow_add, inv_pow]
  by_cases hb : (gram base s).det = 0
  · simp [hb]
  · field_simp [hz, hb]

private theorem normalized_det_tendsto (φ : ZMod D → ι → ℝ) :
    Tendsto (fun u => (normalized φ u).det) (𝓝[≠] 1) (𝓝 (periodGram φ).det) := by
  classical
  simp only [Matrix.det_apply']
  apply tendsto_finsetSum
  intro σ _
  apply Tendsto.const_mul
  apply tendsto_finsetProd
  intro j _
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (normalized_tendsto_periodGram φ) (σ j)) j

theorem det_ratio_tendsto_uniform_period (base : ZMod D → ι → ℝ) (join : ZMod D → (ι ⊕ κ) → ℝ)
    (hb : (periodGram base).det ≠ 0) :
    Tendsto (fun s => (normalized join s).det / (normalized base s).det) (𝓝[≠] 1)
      (𝓝 ((periodGram join).det / (periodGram base).det)) :=
  (normalized_det_tendsto join).div (normalized_det_tendsto base) hb

/-- The Schur complement of the normalized joined Gram, in its original columns. -/
def schur (join : ZMod D → (ι ⊕ κ) → ℝ) (s : ℂ) : Matrix κ κ ℂ :=
  let M := normalized join s
  M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂

/-- The log-weighted matrix evaluated on the fixed screened columns at the point s. -/
def screenedLogMoment (join : ZMod D → (ι ⊕ κ) → ℝ) (s : ℂ) : Matrix κ κ ℂ :=
  SchurMatrixDerivative.variation (normalized join s) (logMoment join s)

theorem schur_entry_hasDerivAt (join : ZMod D → (ι ⊕ κ) → ℝ) {s : ℂ} (hs : 1 < s.re)
    (hb : (normalized (fun a i => join a (.inl i)) s).det ≠ 0) (i j : κ) :
    HasDerivAt (fun u => schur join u i j)
      (((-(deriv riemannZeta s / riemannZeta s)) • schur join s - screenedLogMoment join s) i j) s := by
  let M := normalized join s
  let W := logMoment join s
  let μ := -(deriv riemannZeta s / riemannZeta s)
  let X := M.toBlocks₁₁⁻¹ * M.toBlocks₁₂
  let Y := M.toBlocks₂₁ * M.toBlocks₁₁⁻¹
  have hd (a b) : HasDerivAt (fun u => normalized join u a b) ((μ • M - W) a b) s :=
    normalized_entry_hasDerivAt join hs a b
  have h := SchurMatrixDerivative.schur_entries hd hb i j
  have hAX : M.toBlocks₁₁ * X = M.toBlocks₁₂ := by
    change M.toBlocks₁₁ * (M.toBlocks₁₁⁻¹ * M.toBlocks₁₂) = _
    have hbase : IsUnit M.toBlocks₁₁.det := isUnit_iff_ne_zero.mpr hb
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M.toBlocks₁₁ hbase, Matrix.one_mul]
  have he : SchurMatrixDerivative.variation M (μ • M - W) =
      μ • schur join s - screenedLogMoment join s := by
    change (μ • M.toBlocks₂₂ - W.toBlocks₂₂) - (μ • M.toBlocks₂₁ - W.toBlocks₂₁) * X -
      Y * ((μ • M.toBlocks₁₂ - W.toBlocks₁₂) - (μ • M.toBlocks₁₁ - W.toBlocks₁₁) * X) =
      μ • (M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂) -
      (W.toBlocks₂₂ - W.toBlocks₂₁ * X - Y * (W.toBlocks₁₂ - W.toBlocks₁₁ * X))
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hAX]
    have hc : μ • M.toBlocks₁₂ - W.toBlocks₁₂ - (μ • M.toBlocks₁₂ - W.toBlocks₁₁ * X) =
        -(W.toBlocks₁₂ - W.toBlocks₁₁ * X) := by abel
    rw [hc, Matrix.mul_neg, smul_sub]
    simp only [X, Y, Matrix.mul_assoc]
    abel
  exact h.congr_deriv (congrFun (congrFun he i) j)

/-- The single innovation trace agrees with the joined-minus-base formulation. -/
theorem schur_logDeriv_screened (join : ZMod D → (ι ⊕ κ) → ℝ) {s : ℂ} (hs : 1 < s.re)
    (hb : (normalized (fun a i => join a (.inl i)) s).det ≠ 0) (hΩ : (schur join s).det ≠ 0) :
    deriv (fun u => (schur join u).det) s / (schur join s).det =
      (Fintype.card κ : ℂ) * (-(deriv riemannZeta s / riemannZeta s)) -
      ((schur join s)⁻¹ * screenedLogMoment join s).trace := by
  rw [GramLogarithmicDerivative.det_logDeriv (schur_entry_hasDerivAt join hs hb) hΩ,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hΩ),
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  ring

theorem schur_det_eq_ratio (join : ZMod D → (ι ⊕ κ) → ℝ) (s : ℂ)
    (hb : (normalized (fun a i => join a (.inl i)) s).det ≠ 0) :
    (schur join s).det = (normalized join s).det /
      (normalized (fun a i => join a (.inl i)) s).det := by
  let M := normalized join s
  change M.toBlocks₁₁.det ≠ 0 at hb
  letI : Invertible M.toBlocks₁₁ :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb)
  have hm : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ := by
    ext i j
    cases i <;> cases j <;> rfl
  have h := congrArg Matrix.det hm
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at h
  change _ = M.det / M.toBlocks₁₁.det
  exact (eq_div_iff hb).mpr (by rw [mul_comm]; exact h.symm)

theorem schur_det_logDeriv (join : ZMod D → (ι ⊕ κ) → ℝ)
    {s : ℂ} (hs : 1 < s.re) (hb : (normalized (fun a i => join a (.inl i)) s).det ≠ 0)
    (hj : (normalized join s).det ≠ 0) :
    let base := fun a i => join a (.inl i)
    deriv (fun u => (schur join u).det) s / (schur join s).det =
      (Fintype.card κ : ℂ) * (-(deriv riemannZeta s / riemannZeta s)) -
      (((normalized join s)⁻¹ * logMoment join s).trace -
        ((normalized base s)⁻¹ * logMoment base s).trace) := by
  let base := fun a i => join a (.inl i)
  have he : (fun u => (schur join u).det) =ᶠ[𝓝 s]
      (fun u => (normalized join u).det / (normalized base u).det) := by
    filter_upwards [(det_differentiableAt base hs).continuousAt.eventually_ne hb] with u hu
    exact schur_det_eq_ratio join u hu
  rw [he.deriv_eq, schur_det_eq_ratio join s hb]
  exact joined_det_ratio_logDeriv base join hs hb hj

theorem schur_det_tendsto_uniform_period (join : ZMod D → (ι ⊕ κ) → ℝ)
    (hb : (periodGram (fun a i => join a (.inl i))).det ≠ 0) :
    Tendsto (fun s => (schur join s).det) (𝓝[≠] 1)
      (𝓝 ((periodGram join).det / (periodGram (fun a i => join a (.inl i))).det)) := by
  let base := fun a i => join a (.inl i)
  apply (det_ratio_tendsto_uniform_period base join hb).congr'
  filter_upwards [(normalized_det_tendsto base).eventually_ne hb] with s hs
  exact (schur_det_eq_ratio join s hs).symm

end Determinants
end RiemannResearch.Analysis.PeriodicDirichletGram
