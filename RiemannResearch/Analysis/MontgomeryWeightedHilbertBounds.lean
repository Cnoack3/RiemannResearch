import RiemannResearch.Analysis.DirichletMeanSquare
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Weighted Hilbert constants and integer logarithmic spacing

Preissmann's published general weighted bound is
π√(1+(2/3)√(6/5)). The literature statement is the existing predicate
`Zeta23.MVDiag preissmannConstant`. The general irregular-frequency optimum
is strictly larger than π by Rodgers (arXiv:2608.12315, 2026 preprint).
Preissmann, Enseign. Math. 30 (1984), 95–113, doi:10.5169/seals-53823. -/

noncomputable section
open Set MeasureTheory
namespace RiemannResearch.Analysis.DirichletMeanSquare
open ZeroOrdinate

/-- Preissmann's published upper bound on arbitrary irregular real frequencies. -/
def preissmannConstant : ℝ := Real.pi*Real.sqrt (1+(2/3:ℝ)*Real.sqrt (6/5:ℝ))

private theorem midpoint_lower_log {y : ℝ} (hy : 1 ≤ y) :
    2*(y-1)/(y+1) ≤ Real.log y := by
  let f := fun x : ℝ => Real.log x-2*(x-1)/(x+1)
  let f' := fun x : ℝ => (x-1)^2/(x*(x+1)^2)
  have hder {x : ℝ} (hx : 0 < x) : HasDerivAt f (f' x) x := by
    have hp : x+1 ≠ 0 := by linarith
    have h := (Real.hasDerivAt_log hx.ne').sub
      ((((hasDerivAt_id x).sub_const 1).const_mul 2).div ((hasDerivAt_id x).add_const 1) hp)
    convert h using 1 <;> first | rfl | (dsimp [f']; field_simp [hx.ne',hp]; ring)
  have hm : MonotoneOn f (Ici (1:ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (f' := f')
    · intro x hx
      exact (hder (zero_lt_one.trans_le hx)).continuousAt.continuousWithinAt
    · intro x hx
      have hxi : x ∈ Ici (1:ℝ) := interior_subset hx
      exact (hder (zero_lt_one.trans_le hxi)).hasDerivWithinAt
    · intro x hx
      have hxi : x ∈ Ici (1:ℝ) := interior_subset hx
      have hpos : 0 < x := zero_lt_one.trans_le hxi
      dsimp only [f']
      positivity
  have h := hm (by simp) (mem_Ici.mpr hy) hy
  have h1 : f 1=0 := by simp [f]
  rw [h1] at h
  exact sub_nonneg.mp h

private theorem lower_log_integer_step {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    (1 : ℝ)/((m:ℝ)+1/2) ≤ Real.log n-Real.log m := by
  have hp : 0 < (m:ℝ) := by exact_mod_cast hm
  have hsucc : (m:ℝ)+1 ≤ n := by exact_mod_cast hmn
  let q := ((m:ℝ)+1)/(m:ℝ)
  have hq : 1 ≤ q := (le_div_iff₀ hp).2 (by linarith)
  calc
    _ = 2*(q-1)/(q+1) := by
      dsimp [q]
      field_simp [hp.ne',show (m:ℝ)+1/2 ≠ 0 by positivity]
      ring
    _ ≤ Real.log q := midpoint_lower_log hq
    _ = Real.log ((m:ℝ)+1)-Real.log m := Real.log_div (by positivity) hp.ne'
    _ ≤ _ := sub_le_sub_right (Real.log_le_log (by positivity) hsucc) _

/-- Integer log frequencies have local gap at least 1/(n+1/2).
The addend 1/2 is asymptotically necessary for this rational bound,
by expansion of 1/log(1+1/n). -/
theorem midpoint_inv_le_abs_log_sub {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hne : n≠m) :
    (1 : ℝ)/((n:ℝ)+1/2) ≤ |Real.log n-Real.log m| := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_sub_comm]
    exact (lower_log_integer_step hn h).trans (le_abs_self _)
  · have hmn : (m:ℝ) ≤ n := by exact_mod_cast h.le
    have hmp : (0:ℝ) < m := by exact_mod_cast hm
    have hdiv : 1/((n:ℝ)+1/2) ≤ 1/((m:ℝ)+1/2) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
    exact hdiv.trans ((lower_log_integer_step hm h).trans (le_abs_self _))

/-- Closest possible full-integer logarithmic gap at frequency n. -/
def adjacentLogGap (n : ℕ) : ℝ := Real.log (1+1/(n:ℝ))

theorem adjacentLogGap_pos {n : ℕ} (hn : 0 < n) : 0 < adjacentLogGap n := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  have h : 0 < 1/(n:ℝ) := by positivity
  exact Real.log_pos (by linarith : 1 < 1+1/(n:ℝ))

private theorem adjacent_gap_le_ordered {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    adjacentLogGap m ≤ Real.log n-Real.log m := by
  have hp : 0 < (m:ℝ) := by exact_mod_cast hm
  have hmn' : (m:ℝ)+1 ≤ n := by exact_mod_cast hmn
  unfold adjacentLogGap
  rw [show 1+1/(m:ℝ)=((m:ℝ)+1)/m by field_simp [hp.ne'], Real.log_div (by positivity) hp.ne']
  exact sub_le_sub_right (Real.log_le_log (by positivity) hmn') _

theorem adjacentLogGap_le_abs_difference {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hne : n≠m) :
    adjacentLogGap n ≤ |Real.log n-Real.log m| := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_sub_comm]
    exact (adjacent_gap_le_ordered hn h).trans (le_abs_self _)
  · have hmn : (m:ℝ) ≤ n := by exact_mod_cast h.le
    have hmp : (0:ℝ) < m := by exact_mod_cast hm
    have hnp : (0:ℝ) < n := by exact_mod_cast hn
    have hdiv : (1:ℝ)/n ≤ (1:ℝ)/m := div_le_div_of_nonneg_left zero_le_one hmp hmn
    have hm' : adjacentLogGap n ≤ adjacentLogGap m := Real.log_le_log (by positivity)
      (show 1+(1:ℝ)/n ≤ 1+(1:ℝ)/m by linarith only [hdiv])
    exact hm'.trans ((adjacent_gap_le_ordered hm h).trans (le_abs_self _))

private theorem cubic_lower_log {y : ℝ} (hy : 1 ≤ y) :
    3*(y^2-1)/(y^2+4*y+1) ≤ Real.log y := by
  let f := fun x : ℝ => Real.log x-3*(x^2-1)/(x^2+4*x+1)
  let f' := fun x : ℝ => (x-1)^4/(x*(x^2+4*x+1)^2)
  have hd {x : ℝ} (hx : 0 < x) : HasDerivAt f (f' x) x := by
    have hp : x^2+4*x+1 ≠ 0 := by positivity
    have h := (Real.hasDerivAt_log hx.ne').sub
      (((((hasDerivAt_id x).pow 2).sub_const 1).const_mul 3).div
        ((((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).const_mul 4)).add_const 1) hp)
    convert h using 1 <;> first | rfl | (dsimp [f']; field_simp [hx.ne',hp]; ring)
  have hm : MonotoneOn f (Ici (1:ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (f' := f')
    · intro x hx
      exact (hd (zero_lt_one.trans_le hx)).continuousAt.continuousWithinAt
    · intro x hx
      have hxi : x ∈ Ici (1:ℝ) := interior_subset hx
      exact (hd (zero_lt_one.trans_le hxi)).hasDerivWithinAt
    · intro x hx
      have hxi : x ∈ Ici (1:ℝ) := interior_subset hx
      have hp : 0 < x := zero_lt_one.trans_le hxi
      dsimp only [f']
      positivity
  have h := hm (by simp) (mem_Ici.mpr hy) hy
  rw [show f 1=0 by simp [f]] at h
  exact sub_nonneg.mp h

/-- A second-order eligible weight below n+1/2. The coefficient 1/12
matches the reciprocal logarithm's asymptotic expansion. -/
theorem inv_adjacentLogGap_le_corrected_midpoint {n : ℕ} (hn : 0 < n) :
    1/adjacentLogGap n ≤ (n:ℝ)+1/2 - 1/(12*((n:ℝ)+1/2)) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  let q : ℝ := 1+1/(n:ℝ)
  have hq : 1 < q := by dsimp [q]; linarith [show 0 < 1/(n:ℝ) by positivity]
  have hnum : 0 < q^2-1 := by nlinarith only [hq,sq_nonneg (q-1)]
  have hden : 0 < q^2+4*q+1 := by nlinarith only [hq,sq_nonneg q]
  have h := cubic_lower_log hq.le
  calc
    _ ≤ 1/(3*(q^2-1)/(q^2+4*q+1)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) h
    _ = (q^2+4*q+1)/(3*(q^2-1)) := by rw [div_div_eq_mul_div,one_mul]
    _ = _ := by
      have he : q^2-1 = (2*(n:ℝ)+1)/(n:ℝ)^2 := by dsimp [q]; field_simp [hp.ne']; ring
      rw [he]
      dsimp only [q]
      field_simp [hp.ne',show (2*(n:ℝ)+1) ≠ 0 by positivity,show (n:ℝ)+1/2 ≠ 0 by positivity]
      ring

/-- Any weighted Hilbert input in the existing repository normalization
gives twice its constant for the two endpoints of the Dirichlet integral. -/
theorem abs_integral_norm_sq_sub_le_of_weightedHilbert {K : ℝ} (hK : Zeta23.MVDiag K)
    {ι : Type} [Fintype ι] (a : ι → ℂ) (ω δ : ι → ℝ)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) (A B : ℝ) :
    |(∫ t in A..B, ‖polynomial a ω t‖^2) - (B-A)*∑ i, ‖a i‖^2| ≤
      (2*K)*∑ i, ‖a i‖^2/δ i := by
  classical
  have he : (((∫ t in A..B, ‖polynomial a ω t‖^2) -
      (B-A)*∑ i, ‖a i‖^2 : ℝ) : ℂ) = offDiagonal a ω A B := by
    rw [Complex.ofReal_sub,integral_norm_sq_eq_diagonal_add]
    ring
  have hb (t : ℝ) : ‖endpointHilbert a ω t‖ ≤ K*∑ i, ‖a i‖^2/δ i := by
    have H := hK ι ω δ (fun i => a i*phase (ω i) t) hω hδ hsep
    simpa only [endpointHilbert,Complex.star_def,norm_mul,phase_norm,mul_one] using H
  have hn := congrArg norm he
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn,offDiagonal_eq_endpoints a ω hω,norm_div,Complex.norm_I,div_one]
  exact (norm_sub_le _ _).trans ((add_le_add (hb B) (hb A)).trans_eq (by ring))

/-- Integer-log specialization with the exact full-integer adjacent gap.
Removing frequencies may only increase the distance to the nearest neighbor. -/
theorem abs_integer_log_mean_square_sub_le_adjacent {K : ℝ} (hK : Zeta23.MVDiag K)
    {ι : Type} [Fintype ι] (a : ι → ℂ) (n : ι → ℕ)
    (hinj : Function.Injective n) (hn : ∀ i, 0 < n i) (A B : ℝ) :
    |(∫ t in A..B, ‖polynomial a (fun i => Real.log (n i)) t‖^2) -
      (B-A)*∑ i, ‖a i‖^2| ≤ (2*K)*∑ i, ‖a i‖^2/adjacentLogGap (n i) := by
  classical
  have hp (i : ι) : (0:ℝ) < n i := by exact_mod_cast hn i
  have hi : Function.Injective (fun i => Real.log (n i : ℝ)) := by
    intro i j hij
    apply hinj
    exact_mod_cast Real.log_injOn_pos (mem_Ioi.mpr (hp i)) (mem_Ioi.mpr (hp j)) hij
  exact abs_integral_norm_sq_sub_le_of_weightedHilbert hK a (fun i => Real.log (n i))
    (fun i => adjacentLogGap (n i)) hi (fun i => adjacentLogGap_pos (hn i))
    (fun i j hij => adjacentLogGap_le_abs_difference (hn i) (hn j) (fun h => hij (hinj h))) A B

end RiemannResearch.Analysis.DirichletMeanSquare
