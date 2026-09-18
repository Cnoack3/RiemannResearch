import RiemannResearch.RH.CRTExactSignedEnergy
import RiemannResearch.RH.ConditionalMeanHeadMinimum
/-!
# First-period control of exact signed CRT energy

Source: the CRT–Pareto research continuation, 2026-09-18.
This module uses the actual conditional Cesaro energy and its exact periodic
defect identity. For a mean-zero periodic sequence, a finite rational form
controls the complete energy with a uniform factor of 9/8. The final RH
reduction is conditional: no subpolynomial coefficient construction is proved.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.Pareto
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.Cesaro

def mKernel (t : ℝ) : ℝ := 2 / (t^2 * (t+1) * (t+2))

theorem mKernel_eq (t : ℝ) : mKernel t = lKernel t / t := by
  unfold mKernel lKernel
  rw [div_div]
  congr 1
  ring

theorem mKernel_pos {t : ℝ} (ht : 0 < t) : 0 < mKernel t := by
  unfold mKernel
  positivity

/-- The shifted scale respects all four denominator factors together. -/
theorem mKernel_scale_bound {r t n : ℝ} (hr : 0 < r) (hn : 1 ≤ n)
    (ht : n*(r+1) ≤ t+1) :
    mKernel t ≤ mKernel r / n^4 := by
  have hn0 : 0 < n := by linarith
  have htr : n*r ≤ t := by nlinarith
  have ht0 : 0 < t := lt_of_lt_of_le (mul_pos hn0 hr) htr
  have h1 : n^2*r*(r+1) ≤ t*(t+1) := by
    have h := mul_le_mul htr ht (by positivity : 0 ≤ n*(r+1)) ht0.le
    nlinarith only [h]
  have hs : (n*(r+1))^2 ≤ (t+1)^2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr ht
  have h2 : n^2*r*(r+2) ≤ t*(t+2) := by nlinarith
  have hd : n^4*(r^2*(r+1)*(r+2)) ≤ t^2*(t+1)*(t+2) := by
    have h := mul_le_mul h1 h2 (by positivity : 0 ≤ n^2*r*(r+2))
      (by positivity : 0 ≤ t*(t+1))
    nlinarith only [h]
  calc
    mKernel t ≤ 2 / (n^4*(r^2*(r+1)*(r+2))) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ = mKernel r / n^4 := by
      unfold mKernel
      rw [div_div]
      congr 1
      ring

/-- Elementary summable tail majorant; equality occurs at n=2. -/
theorem inverse_fourth_tail_bound {n : ℝ} (hn : 2 ≤ n) :
    1 / n^4 ≤ (1/8 : ℝ) * (1 / (n-1) - 1/n) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hpoly : 8*(n-1) ≤ n^3 := by
    have hh := mul_nonneg (show 0 ≤ n-2 by linarith)
      (show 0 ≤ n^2+2*n-4 by nlinarith)
    nlinarith only [hh]
  have hd : 8*n*(n-1) ≤ n^4 := by
    have h := mul_le_mul_of_nonneg_left hpoly hn0.le
    nlinarith only [h]
  calc
    1 / n^4 ≤ 1 / (8*n*(n-1)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ = _ := by field_simp; ring


/-- The progression tail is at most one eighth of its first atom when
the residue is separated from the conductor by at least one. -/
theorem progressionM_first_atom_bound {Q r : ℝ}
    (hr : 0 < r) (hQr : r+1 ≤ Q) :
    mKernel r ≤ progressionM Q r ∧
      progressionM Q r ≤ (9/8 : ℝ)*mKernel r := by
  have hQ : 0 < Q := by linarith
  have hs : Summable (fun k : ℕ => mKernel (Q*(k : ℝ)+r)) := by
    simpa only [mKernel_eq] using progressionM_summable hQ hr
  have hst := hs.comp_injective (fun _ _ h => Nat.add_right_cancel h :
    Function.Injective (fun k : ℕ => k+1))
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hwhole : (∑' k : ℕ, mKernel (Q*(k : ℝ)+r)) = progressionM Q r := by
    simp only [mKernel_eq, progressionM]
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, hwhole] at hsplit
  have hm := ((hasSum_weight_from 1 (by omega)).mul_left (mKernel r/8))
  have hb (k : ℕ) :
      mKernel (Q*((k+1 : ℕ) : ℝ)+r) ≤ (mKernel r/8)*weight (1+k) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have ht : ((k : ℝ)+2)*(r+1) ≤ Q*((k+1 : ℕ) : ℝ)+r+1 := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ Q-r-1 by linarith) (show 0 ≤ (k : ℝ)+1 by positivity)]
    have hscale := mKernel_scale_bound hr (show 1 ≤ (k : ℝ)+2 by linarith) ht
    have htail := mul_le_mul_of_nonneg_left
      (inverse_fourth_tail_bound (show 2 ≤ (k : ℝ)+2 by linarith)) (mKernel_pos hr).le
    have hw := weight_eq_sub (1+k) (by omega)
    have he : (mKernel r/8)*weight (1+k) =
        mKernel r*((1/8 : ℝ)*(1/((k : ℝ)+2-1)-1/((k : ℝ)+2))) := by
      rw [hw]
      push_cast
      ring
    rw [he]
    calc
      _ ≤ mKernel r/((k : ℝ)+2)^4 := hscale
      _ = mKernel r*(1/((k : ℝ)+2)^4) := by ring
      _ ≤ _ := htail
  have hupper : (∑' k : ℕ, mKernel (Q*((k+1 : ℕ) : ℝ)+r)) ≤ mKernel r/8 := by
    have h := hst.tsum_le_tsum hb hm.summable
    simpa only [hm.tsum_eq, Nat.cast_one, div_one, mul_one] using h
  have hnonneg : 0 ≤ ∑' k : ℕ, mKernel (Q*((k+1 : ℕ) : ℝ)+r) :=
    tsum_nonneg (fun k => (mKernel_pos (by positivity)).le)
  constructor <;> linarith

/-- A finite rational diagonal form on the signed cumulative coordinates. -/
def firstPeriodCore (Q : ℕ) (B : Fin Q → ℝ) : ℝ :=
  ∑ r : Fin Q, mKernel (r.val+1) * (B r)^2

theorem firstPeriodCore_enclosure (Q : ℕ)
    (B : Fin Q → ℝ) (hterminal : ∀ r : Fin Q, r.val+1=Q → B r=0) :
    firstPeriodCore Q B ≤ ∑ r : Fin Q, progressionM Q (r.val+1)*(B r)^2 ∧
      (∑ r : Fin Q, progressionM Q (r.val+1)*(B r)^2) ≤
        (9/8 : ℝ)*firstPeriodCore Q B := by
  have hb (r : Fin Q) :
      mKernel (r.val+1)*(B r)^2 ≤ progressionM Q (r.val+1)*(B r)^2 ∧
      progressionM Q (r.val+1)*(B r)^2 ≤ (9/8 : ℝ)*(mKernel (r.val+1)*(B r)^2) := by
    by_cases he : r.val+1=Q
    · rw [hterminal r he]
      norm_num
    · have hsep : (r.val : ℝ)+1+1 ≤ (Q : ℝ) := by
        exact_mod_cast (show r.val+1+1 ≤ Q by have := r.isLt; omega)
      have h := progressionM_first_atom_bound (by positivity : 0 < (r.val : ℝ)+1) hsep
      constructor
      · exact mul_le_mul_of_nonneg_right h.1 (sq_nonneg _)
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h.2 (sq_nonneg (B r))
  constructor
  · exact Finset.sum_le_sum (fun r _ => (hb r).1)
  · unfold firstPeriodCore
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => (hb r).2)

theorem periodDefect_terminal (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    periodDefect F Q Q = 0 := by
  unfold periodDefect periodMean
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  field_simp
  ring

def firstPeriodEnergy (F : ℕ → ℝ) (Q : ℕ) : ℝ :=
  firstPeriodCore Q (fun r => periodDefect F Q (r.val+1))

/-- The whole infinite energy is controlled by one actual period, with
a conductor-independent 9/8 factor and all signed combinations intact. -/
theorem zeroMean_firstPeriod_enclosure (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n+Q)=F n) (hm : periodMean F Q=0) :
    firstPeriodEnergy F Q ≤ conditionalMeanSquare F ∧
      conditionalMeanSquare F ≤ (9/8 : ℝ)*firstPeriodEnergy F Q := by
  have he := periodic_error_energy_identity F Q hQ hp 0
  simp only [hm, sub_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
    zero_add] at he
  have he' : conditionalMeanSquare F =
      ∑ r : Fin Q, progressionM Q (r.val+1)*(periodDefect F Q (r.val+1))^2 := by
    simpa only [conditionalMeanSquare, conditionalWeight, mixtureWeight] using he
  rw [he']
  apply firstPeriodCore_enclosure Q
  intro r hr
  rw [hr, periodDefect_terminal F Q hQ]

/-- The finite coordinate form is exactly the first period of the original
conditional energy, not a uniform CRT residue average. -/
theorem firstPeriodEnergy_eq_prefix (F : ℕ → ℝ) (Q : ℕ)
    (hm : periodMean F Q = 0) :
    firstPeriodEnergy F Q =
      ∑ r : Fin Q, conditionalWeight r.val * (cesaro F (r.val+1))^2 := by
  unfold firstPeriodEnergy firstPeriodCore
  apply Finset.sum_congr rfl
  intro r _
  rw [cesaro_from_defect F Q (r.val+1) (by omega), hm, zero_add]
  unfold mKernel conditionalWeight mixtureWeight
  push_cast
  have hr : (r.val : ℝ)+1 ≠ 0 := by positivity
  have hr2 : (r.val : ℝ)+1+1 ≠ 0 := by positivity
  have hr3 : (r.val : ℝ)+1+2 ≠ 0 := by positivity
  field_simp

/-- A finite-coordinate comparison gives a genuine 9/8-quasioptimal witness. -/
theorem energy_le_of_firstPeriod_le
    (F G : ℕ → ℝ) (Q P : ℕ) (hQ : 0 < Q) (hP : 0 < P)
    (hpF : ∀ n, F (n+Q)=F n) (hpG : ∀ n, G (n+P)=G n)
    (hmF : periodMean F Q=0) (hmG : periodMean G P=0)
    (hcore : firstPeriodEnergy F Q ≤ firstPeriodEnergy G P) :
    conditionalMeanSquare F ≤ (9/8 : ℝ)*conditionalMeanSquare G := by
  have hF := (zeroMean_firstPeriod_enclosure F Q hQ hpF hmF).2
  have hG := (zeroMean_firstPeriod_enclosure G P hP hpG hmG).1
  linarith

/-- The unresolved growth problem is unchanged by replacing the complete
energy with this finite rational coordinate form. -/
theorem firstPeriod_subpolynomial_iff
    (F : ℕ → ℕ → ℝ) (Q Y : ℕ → ℕ)
    (hQ : ∀ j, 0 < Q j) (hp : ∀ j n, F j (n+Q j)=F j n)
    (hm : ∀ j, periodMean (F j) (Q j)=0) :
    HasSubpolynomialEnergy Y (fun j => conditionalMeanSquare (F j)) ↔
      HasSubpolynomialEnergy Y (fun j => firstPeriodEnergy (F j) (Q j)) := by
  constructor
  · intro h ε hε
    obtain ⟨C,hC,j0,hbound⟩ := h ε hε
    refine ⟨C,hC,j0,?_⟩
    intro j hj
    exact (zeroMean_firstPeriod_enclosure (F j) (Q j) (hQ j) (hp j) (hm j)).1.trans
      (hbound j hj)
  · intro h ε hε
    obtain ⟨C,hC,j0,hbound⟩ := h ε hε
    refine ⟨(9/8 : ℝ)*C,by positivity,j0,?_⟩
    intro j hj
    have hb := (zeroMean_firstPeriod_enclosure (F j) (Q j) (hQ j) (hp j) (hm j)).2
    nlinarith [hbound j hj]

/-- Conditional research reduction. The finite signed arithmetic bound hcore
is open; this theorem does not construct the required legal coefficients. -/
theorem riemannHypothesis_of_subpolynomial_firstPeriod
    (F : ℕ → ℕ → ℝ) (Q Y : ℕ → ℕ)
    (hF : ∀ j, F j ∈ conditionalHeadClass (Y j))
    (hY : Filter.Tendsto Y Filter.atTop Filter.atTop)
    (hQ : ∀ j, 0 < Q j) (hp : ∀ j n, F j (n+Q j)=F j n)
    (hm : ∀ j, periodMean (F j) (Q j)=0)
    (hcore : HasSubpolynomialEnergy Y (fun j => firstPeriodEnergy (F j) (Q j))) :
    RiemannHypothesis := by
  have hactual := (firstPeriod_subpolynomial_iff F Q Y hQ hp hm).mpr hcore
  apply riemannHypothesis_of_subpolynomial_conditionalMean_heads
    (Set.Ici 1) (by intro a ha; exact ha) F Y
    (fun j => (hF j).1) (fun j => (hF j).2) hY
  intro ε hε
  obtain ⟨C,hC,j0,hbound⟩ := hactual ε hε
  refine ⟨C,hC.le,?_⟩
  filter_upwards [Filter.eventually_ge_atTop j0] with j hj
  exact hbound j hj

end RiemannResearch.RH.CRTBlock
