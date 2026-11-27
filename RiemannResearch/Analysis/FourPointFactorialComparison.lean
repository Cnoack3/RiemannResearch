import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Removing two labels from a four-point counting test

For a long interval containing m occurrences, e is the reciprocal of its
unfolded length. Its normalized first, second and fourth falling factorials
are z, w and f below. The comparison uses the first and fourth statistics
to control the mean-square error of w as an approximation to one.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.FourPointComparison

def countOne (e : ℝ) (m : ℕ) : ℝ := e*m

def countTwo (e : ℝ) (m : ℕ) : ℝ :=
  countOne e m * (countOne e m-e)

def countFour (e : ℝ) (m : ℕ) : ℝ :=
  countTwo e m * (countOne e m-2*e) * (countOne e m-3*e)

/-- The polynomial counts ordered injective selections of four labels, even
when the interval contains fewer than four occurrences. -/
theorem countFour_eq_embedding_card {α : Type*} [Fintype α] [DecidableEq α] (e : ℝ) :
    countFour e (Fintype.card α) = e^4*(Fintype.card (Fin 4 ↪ α) : ℝ) := by
  rw [Fintype.card_embedding_eq,Fintype.card_fin]
  generalize Fintype.card α = m
  rcases m with _ | _ | _ | _ | m
  all_goals simp [countFour,countTwo,countOne,Nat.descFactorial_succ,
    Nat.descFactorial_zero] <;> ring_nf <;> simp

theorem countTwo_eq_embedding_card {α : Type*} [Fintype α] [DecidableEq α] (e : ℝ) :
    countTwo e (Fintype.card α) = e^2*(Fintype.card (Fin 2 ↪ α) : ℝ) := by
  rw [Fintype.card_embedding_eq,Fintype.card_fin]
  generalize Fintype.card α = m
  rcases m with _ | _ | m
  all_goals simp [countTwo,countOne,Nat.descFactorial_succ,Nat.descFactorial_zero] <;> ring

/-- An exact fourth-moment identity counts the ways that four indices agree. -/
theorem count_pow_four (m : ℕ) :
    (m:ℝ)^4 = countFour 1 m + 6*countTwo 1 m*((m:ℝ)-2) + 7*countTwo 1 m + m := by
  unfold countFour countTwo countOne
  ring

/-- A bounded local fourth factorial moment already bounds the square of
the local pair statistic, including the small counts where (m)₄ is zero. -/
theorem local_factorial_comparison (m : ℕ) :
    countFour 1 m ≤ (countTwo 1 m)^2 ∧ (countTwo 1 m)^2 ≤ 36+6*countFour 1 m := by
  rcases m with _ | _ | _ | _ | m
  all_goals unfold countFour countTwo countOne
  all_goals constructor <;> apply sub_nonneg.mp <;> push_cast <;> ring_nf <;> positivity

/-- Only the first and fourth falling factorials occur on the right. -/
theorem long_interval_pair_error (m : ℕ) {e : ℝ} (he : 0 ≤ e) (hs : 12*e ≤ 1) :
    (countTwo e m-1)^2 ≤
      (1+12*e)*countFour e m + (3+12*e) - (4-2*e)*countOne e m := by
  let z := countOne e m
  let w := countTwo e m
  let f := countFour e m
  have hz : 0 ≤ z := by dsimp [z,countOne]; positivity
  have hw0 : 0 ≤ w := by
    cases m with
    | zero => simp [w,countTwo,countOne]
    | succ m =>
      have h : 0 ≤ e*(m:ℝ) := by positivity
      dsimp [w,countTwo,countOne]
      push_cast
      nlinarith only [mul_nonneg (by positivity : 0 ≤ e*((m:ℝ)+1)) h]
  have hF : 0 ≤ f := by
    rcases m with _ | _ | _ | m
    all_goals simp [f,countFour,countTwo,countOne] <;> ring_nf <;> positivity
  have hsmall : z^4 ≤ f + 6*e*z^3 := by
    rcases m with _ | m
    · simp [z,f,countFour,countTwo,countOne]
    · have hze : e ≤ z := by
        dsimp [z,countOne]; push_cast; nlinarith [mul_nonneg he (Nat.cast_nonneg (α := ℝ) m)]
      have hpos : 0 ≤ (e^2*z)*(11*z-6*e) :=
        mul_nonneg (by positivity) (by linarith)
      change z^4 ≤ z*(z-e)*(z-2*e)*(z-3*e) + 6*e*z^3
      nlinarith only [hpos]
  have hc : z^3 ≤ 1+z^4 := by
    by_cases hz1 : z ≤ 1
    · linarith [pow_le_one₀ hz hz1 (n := 3),pow_nonneg hz 4]
    · have h := mul_le_mul_of_nonneg_left (le_of_not_ge hz1) (pow_nonneg hz 3)
      nlinarith only [h]
  have hraw : (1-6*e)*z^4 ≤ f+6*e := by
    nlinarith only [hsmall,mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ 6*e)]
  have hbig : z^4 ≤ (1+12*e)*f+12*e := by
    apply le_of_mul_le_mul_left (a := 1-6*e) _ (by linarith)
    have hx := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 6*e) (by linarith : 0 ≤ 1-12*e))
      (show 0 ≤ f+1 by linarith)
    nlinarith only [hraw,hx]
  have hwz : w ≤ z^2 := by
    change z*(z-e) ≤ z^2
    nlinarith only [mul_nonneg hz he]
  have hsq := pow_le_pow_left₀ hw0 hwz 2
  change (w-1)^2 ≤ (1+12*e)*f+(3+12*e)-(4-2*e)*z
  have hw : w = z^2-e*z := by dsimp [w,z,countTwo]; ring
  nlinarith only [hsq,hbig,hw,sq_nonneg (z-1)]

/-- Four distinct labels occur in P times the normalized falling pair count
when P tests two local labels and M counts labels in a disjoint interval.
The error estimate retains the signed first-moment correction. -/
theorem integrated_pair_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Ω → ℝ) (M : Ω → ℕ) {a e : ℝ}
    (ha : 0 ≤ a) (he : 0 ≤ e) (hs : 12*e ≤ 1)
    (hP : Integrable P μ) (hP₂ : Integrable (fun x => P x ^ 2) μ)
    (hPW : Integrable (fun x => P x * countTwo e (M x)) μ)
    (hF : Integrable (fun x => countFour e (M x)) μ)
    (hZ : Integrable (fun x => countOne e (M x)) μ) :
    2*a*|(∫ x, P x ∂μ) - ∫ x, P x*countTwo e (M x) ∂μ| ≤
      a^2*(∫ x, P x^2 ∂μ) + (1+12*e)*(∫ x, countFour e (M x) ∂μ) +
      (3+12*e) - (4-2*e)*(∫ x, countOne e (M x) ∂μ) := by
  let W (x : Ω) := countTwo e (M x)
  let F (x : Ω) := countFour e (M x)
  let Z (x : Ω) := countOne e (M x)
  let U (x : Ω) := a^2*P x^2+(1+12*e)*F x+(3+12*e)-(4-2*e)*Z x
  have hU : Integrable U μ := (((hP₂.const_mul (a^2)).add
    (hF.const_mul (1+12*e))).add (integrable_const _)).sub (hZ.const_mul (4-2*e))
  have hpoint (x : Ω) : 2*a*|P x-P x*W x| ≤ U x := by
    have h := long_interval_pair_error (M x) he hs
    change (W x-1)^2 ≤ (1+12*e)*F x+(3+12*e)-(4-2*e)*Z x at h
    rw [show P x-P x*W x = P x*(1-W x) by ring, abs_mul]
    have hy := sq_nonneg (a*|P x|-|1-W x|)
    rw [sub_sq, mul_pow, sq_abs, sq_abs] at hy
    dsimp only [U]
    nlinarith only [hy,h]
  have habs := abs_integral_le_integral_abs (μ := μ) (f := fun x => P x-P x*W x)
  have h := integral_mono (((hP.sub hPW).abs).const_mul (2*a)) hU hpoint
  rw [integral_const_mul] at h
  rw [← integral_sub hP hPW]
  apply (mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2*a)).trans
  apply h.trans_eq
  have h₁ : Integrable (fun x => a^2*P x^2) μ := hP₂.const_mul _
  have h₂ : Integrable (fun x => (1+12*e)*F x) μ := hF.const_mul _
  have h₃ : Integrable (fun _ : Ω => 3+12*e) μ := integrable_const _
  have h₄ : Integrable (fun x => (4-2*e)*Z x) μ := hZ.const_mul _
  have h₁₂ : Integrable (fun x => a^2*P x^2+(1+12*e)*F x) μ := h₁.add h₂
  have h₁₂₃ : Integrable (fun x => a^2*P x^2+(1+12*e)*F x+(3+12*e)) μ := h₁₂.add h₃
  dsimp only [U]
  rw [integral_sub h₁₂₃ h₄, integral_add h₁₂ h₃, integral_add h₁ h₂]
  simp [integral_const_mul,F,Z]

/-- The long intervals have increasing integer lengths n+12. -/
def inverseLength (n : ℕ) : ℝ := 1/((n:ℝ)+12)

theorem inverseLength_pos (n : ℕ) : 0 < inverseLength n := by unfold inverseLength; positivity

theorem twelve_mul_inverseLength_le (n : ℕ) : 12*inverseLength n ≤ 1 := by
  unfold inverseLength
  rw [mul_one_div,div_le_iff₀ (show (0:ℝ) < (n:ℝ)+12 by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem inverseLength_tendsto : Tendsto inverseLength atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n:ℝ)+12) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  unfold inverseLength
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp h

/-- Height tends to infinity first at each fixed length. The four-point input
is the mixed four-label test and the long-interval fourth factorial test.
The first-moment input is unit intensity in the long interval. -/
theorem pair_limit_of_four_tests {ι : Type*} {l : Filter ι}
    {P : ι → ℝ} {mixed four first : ℕ → ι → ℝ} {v f : ℕ → ℝ} {s C : ℝ}
    (hC : 0 ≤ C)
    (hcompare : ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∀ᶠ t in l,
      2*a*|P t-mixed n t| ≤ a^2*C + (1+12*inverseLength n)*four n t +
        (3+12*inverseLength n) - (4-2*inverseLength n)*first n t)
    (hfour : ∀ n, Tendsto (four n) l (𝓝 (f n))) (hf : ∀ n, f n ≤ 1)
    (hfirst : ∀ n, Tendsto (first n) l (𝓝 1))
    (hmixed : ∀ n, Tendsto (mixed n) l (𝓝 (v n))) (hv : Tendsto v atTop (𝓝 s)) :
    Tendsto P l (𝓝 s) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := ε/3
  have hd : 0 < d := by dsimp [d]; positivity
  let a := d/(C+1)
  have ha : 0 < a := div_pos hd (by linarith)
  have hac : a*(C+1) = d := div_mul_cancel₀ _ (by linarith)
  have hmul := congrArg (fun x : ℝ => a*x) hac
  have hgap : a^2*C < 2*a*d := by nlinarith only [hmul,mul_pos ha hd,sq_pos_of_pos ha]
  have hsmall : Tendsto (fun n => a^2*C+26*inverseLength n) atTop (𝓝 (a^2*C)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds (x := a^2*C)).add (inverseLength_tendsto.const_mul 26)
  obtain ⟨n,hn,hnv⟩ := ((hsmall.eventually (gt_mem_nhds hgap)).and
    (Metric.tendsto_nhds.mp hv d hd)).exists
  let e := inverseLength n
  have he : 0 ≤ e := (inverseLength_pos n).le
  have hlt : a^2*C+(1+12*e)*f n+(3+12*e)-(4-2*e)*1 < 2*a*d := by
    have h := mul_le_mul_of_nonneg_left (hf n) (by positivity : 0 ≤ 1+12*e)
    change a^2*C+26*e < 2*a*d at hn
    linarith
  have hbound := (((tendsto_const_nhds (x := a^2*C)).add
    ((hfour n).const_mul (1+12*e))).add_const (3+12*e)).sub ((hfirst n).const_mul (4-2*e))
  filter_upwards [hcompare n a ha, hbound.eventually (gt_mem_nhds hlt),
    Metric.tendsto_nhds.mp (hmixed n) d hd] with t ht hu hvn
  have hp : dist (P t) (mixed n t) < d := by
    rw [Real.dist_eq]
    exact (mul_lt_mul_iff_right₀ (show 0 < 2*a by positivity)).mp (ht.trans_lt hu)
  have htri := dist_triangle (P t) (mixed n t) s
  have htri' := dist_triangle (mixed n t) (v n) s
  change dist (v n) s < d at hnv
  dsimp only [d] at hp hvn hnv
  linarith

/-- Integrability for the five expectations in the two-label comparison. -/
structure CountTestIntegrability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Ω → ℝ) (M : Ω → ℕ) (e : ℝ) : Prop where
  localIntegrable : Integrable P μ
  localSquare : Integrable (fun x => P x^2) μ
  mixed : Integrable (fun x => P x*countTwo e (M x)) μ
  fourth : Integrable (fun x => countFour e (M x)) μ
  first : Integrable (fun x => countOne e (M x)) μ

private theorem reference_mixed_limit {s C : ℝ} {v : ℕ → ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ∀ a : ℝ, 0 < a → 2*a*|s-v n| ≤ a^2*C+26*inverseLength n) :
    Tendsto v atTop (𝓝 s) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let a := ε/(C+1)
  have ha : 0 < a := div_pos hε (by linarith)
  have heq : a*(C+1) = ε := div_mul_cancel₀ _ (by linarith)
  have hmul := congrArg (fun x : ℝ => a*x) heq
  have hgap : a^2*C < 2*a*ε := by nlinarith only [hmul,mul_pos ha hε,sq_pos_of_pos ha]
  have hsmall : Tendsto (fun n => a^2*C+26*inverseLength n) atTop (𝓝 (a^2*C)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds (x := a^2*C)).add (inverseLength_tendsto.const_mul 26)
  filter_upwards [hsmall.eventually (gt_mem_nhds hgap)] with n hn
  rw [Real.dist_eq,abs_sub_comm]
  exact (mul_lt_mul_iff_right₀ (show 0 < 2*a by positivity)).mp ((h n a ha).trans_lt hn)

/-- Compare two local pair statistics using only first-order intensity, pure
four-label expectations, and mixed four-label expectations. No convergence
of a pair or triple statistic is assumed. For the sine process the upper
bound on the normalized fourth factorial moment follows from Hadamard's
inequality for its unit-diagonal Gram kernel. -/
theorem pair_expectation_of_four_point_comparison
    {ι Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {l : Filter ι}
    (μ : ι → Measure Ω) [∀ t, IsProbabilityMeasure (μ t)]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (P : ι → Ω → ℝ) (M : ℕ → ι → Ω → ℕ) (Q : Ξ → ℝ) (N : ℕ → Ξ → ℕ)
    (hi : ∀ n t, CountTestIntegrability (μ t) (P t) (M n t) (inverseLength n))
    (hj : ∀ n, CountTestIntegrability ν Q (N n) (inverseLength n))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in l, (∫ x, P t x^2 ∂μ t) ≤ C)
    (hmean : ∀ n, Tendsto (fun t => ∫ x, countOne (inverseLength n) (M n t x) ∂μ t) l (𝓝 1))
    (hmean' : ∀ n, (∫ x, countOne (inverseLength n) (N n x) ∂ν) = 1)
    (hpure : ∀ n, Tendsto (fun t => ∫ x, countFour (inverseLength n) (M n t x) ∂μ t) l
      (𝓝 (∫ x, countFour (inverseLength n) (N n x) ∂ν)))
    (hpure' : ∀ n, (∫ x, countFour (inverseLength n) (N n x) ∂ν) ≤ 1)
    (hmix : ∀ n, Tendsto (fun t => ∫ x, P t x*countTwo (inverseLength n) (M n t x) ∂μ t) l
      (𝓝 (∫ x, Q x*countTwo (inverseLength n) (N n x) ∂ν))) :
    Tendsto (fun t => ∫ x, P t x ∂μ t) l (𝓝 (∫ x, Q x ∂ν)) := by
  obtain ⟨C,hC,hB⟩ := hbound
  refine pair_limit_of_four_tests hC ?_ hpure hpure' hmean hmix ?_
  · intro n a ha
    filter_upwards [hB] with t ht
    obtain ⟨h1,h2,h3,h4,h5⟩ := hi n t
    have hk := integrated_pair_comparison (μ t) (P t) (M n t) ha.le
      (inverseLength_pos n).le (twelve_mul_inverseLength_le n) h1 h2 h3 h4 h5
    linarith only [hk,mul_le_mul_of_nonneg_left ht (sq_nonneg a)]
  · apply reference_mixed_limit (C := ∫ x, Q x^2 ∂ν) (integral_nonneg fun _ => sq_nonneg _)
    intro n a ha
    obtain ⟨h1,h2,h3,h4,h5⟩ := hj n
    have hk := integrated_pair_comparison ν Q (N n) ha.le
      (inverseLength_pos n).le (twelve_mul_inverseLength_le n) h1 h2 h3 h4 h5
    rw [hmean' n] at hk
    have he := (inverseLength_pos n).le
    linarith only [hk,mul_le_mul_of_nonneg_left (hpure' n)
      (by positivity : 0 ≤ 1+12*inverseLength n)]

end RiemannResearch.Analysis.FourPointComparison
