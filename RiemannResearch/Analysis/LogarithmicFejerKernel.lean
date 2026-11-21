import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Fractional Fejér kernels and finite autocorrelations on the unit circle

The measure is probability Haar measure on the circle of period one. The
kernel is unnormalized. Its constant coefficient is its width.
-/
noncomputable section
open Finset MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

namespace RiemannResearch.Analysis.FractionalFejer

abbrev Circle₁ := AddCircle (1 : ℝ)

def polynomial (I : Finset ℕ) (a : ℕ → ℝ) (t : Circle₁) : ℂ :=
  ∑ n ∈ I, (a n : ℂ) * fourier (n : ℤ) t

def dirichlet (m : ℕ) (t : Circle₁) : ℂ := ∑ j ∈ range m, fourier (j : ℤ) t

def kernel (H : ℕ) (r : ℝ) (t : Circle₁) : ℝ :=
  (1-r) * ‖dirichlet H t‖^2 + r * ‖dirichlet (H+1) t‖^2

def correlation (I : Finset ℕ) (a : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ I, if n+h ∈ I then a n * a (n+h) else 0

private theorem integral_mode (k : ℤ) :
    (∫ t : Circle₁, fourier k t ∂haarAddCircle) = if k = 0 then 1 else 0 := by
  classical
  have hc := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  by_cases hk : k = 0
  · subst k
    simp
  · simpa [fourierCoeff, Pi.single_eq_of_ne (Ne.symm hk), hk] using hc

private theorem integral_poly_mode (I : Finset ℕ) (a : ℕ → ℝ) (k : ℤ) :
    (∫ t : Circle₁, fourier k t * (polynomial I a t * conj (polynomial I a t))
      ∂haarAddCircle) =
      ∑ n ∈ I, ∑ m ∈ I, if k + n = m then (a n : ℂ) * a m else 0 := by
  classical
  have expand (t : Circle₁) :
      fourier k t * (polynomial I a t * conj (polynomial I a t)) =
        ∑ n ∈ I, ∑ m ∈ I, ((a n : ℂ) * a m) * fourier (k+n-m) t := by
    simp only [polynomial, map_sum, map_mul, Complex.conj_ofReal, sub_eq_add_neg,
      fourier_add, fourier_neg, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    ring
  simp_rw [expand]
  have hint (n m : ℕ) : Integrable (fun t : Circle₁ =>
      ((a n : ℂ)*a m)*fourier (k+(n:ℤ)-(m:ℤ)) t) haarAddCircle :=
    ((fourier (T := (1:ℝ)) (k+(n:ℤ)-(m:ℤ))).continuous.const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum I (fun n _ => integrable_finsetSum I (fun m _ => hint n m))]
  apply sum_congr rfl
  intro n _
  rw [integral_finsetSum I (fun m _ => hint n m)]
  apply sum_congr rfl
  intro m _
  rw [integral_const_mul, integral_mode]
  by_cases he : k + n = m <;> simp [he, sub_eq_zero]

private theorem positive_mode (I : Finset ℕ) (a : ℕ → ℝ) (h : ℕ) :
    (∫ t : Circle₁, fourier (h : ℤ) t * (polynomial I a t * conj (polynomial I a t))
      ∂haarAddCircle) = (correlation I a h : ℂ) := by
  rw [integral_poly_mode]
  simp only [correlation, Complex.ofReal_sum]
  apply sum_congr rfl
  intro n _
  have hm (m : ℕ) : ((h : ℤ) + n = m) ↔ n+h = m := by omega
  by_cases hn : n+h ∈ I <;> simp [hm, hn]

private theorem negative_mode (I : Finset ℕ) (a : ℕ → ℝ) (h : ℕ) :
    (∫ t : Circle₁, fourier (-(h : ℤ)) t * (polynomial I a t * conj (polynomial I a t))
      ∂haarAddCircle) = (correlation I a h : ℂ) := by
  rw [← positive_mode, integral_poly_mode, integral_poly_mode, sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  have he : (-(h : ℤ) + m = n) ↔ (h : ℤ) + n = m := by omega
  simp only [he, mul_comm]

private theorem range_correlation (m h : ℕ) :
    correlation (range m) (fun _ => 1) h = ((m-h : ℕ) : ℝ) := by
  classical
  have he : (range m).filter (fun n => n+h ∈ range m) = range (m-h) := by
    ext n
    simp only [mem_filter, mem_range]
    omega
  simp only [correlation, ← sum_filter, he, sum_const, card_range, nsmul_eq_mul, mul_one]

private theorem polynomial_one (m : ℕ) (t : Circle₁) :
    polynomial (range m) (fun _ => 1) t = dirichlet m t := by simp [polynomial, dirichlet]

private theorem coe_normsq (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.sq_norm]

private theorem integral_kernel_overlap (H : ℕ) (k : ℤ) (r : ℝ) :
    (∫ t : Circle₁, fourier k t * (kernel H r t : ℂ) ∂haarAddCircle) =
    (((1-r) * ((H-k.natAbs : ℕ) : ℝ) + r * ((H+1-k.natAbs : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hc (m : ℕ) : Continuous (dirichlet m) :=
    continuous_finsetSum _ fun n _ => (fourier (n : ℤ)).continuous
  have ht (m : ℕ) : Integrable (fun t : Circle₁ =>
      fourier k t * (dirichlet m t * conj (dirichlet m t))) haarAddCircle :=
    ((fourier k).continuous.mul ((hc m).mul (Complex.continuous_conj.comp (hc m)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi (m : ℕ) :
      (∫ t : Circle₁, fourier k t * (polynomial (range m) (fun _ => 1) t *
        conj (polynomial (range m) (fun _ => 1) t)) ∂haarAddCircle) =
          (correlation (range m) (fun _ => 1) k.natAbs : ℂ) := by
    cases k with
    | ofNat j => exact positive_mode (range m) (fun _ => 1) j
    | negSucc j => exact negative_mode (range m) (fun _ => 1) (j+1)
  simp only [polynomial_one, range_correlation] at hi
  have hex (t : Circle₁) : fourier k t * (kernel H r t : ℂ) =
      (1-(r:ℂ)) * (fourier k t * (dirichlet H t * conj (dirichlet H t))) +
        (r:ℂ) * (fourier k t *
          (dirichlet (H+1) t * conj (dirichlet (H+1) t))) := by
    simp only [kernel, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one, coe_normsq]
    ring
  simp_rw [hex]
  rw [integral_add ((ht H).const_mul _) ((ht (H+1)).const_mul _),
    integral_const_mul, integral_const_mul, hi, hi]
  push_cast
  ring

/-- Nonnegative Fourier modes, including the mass at index zero. -/
theorem integral_kernel_mode (H h : ℕ) (r : ℝ) :
    (∫ t : Circle₁, fourier (h : ℤ) t * (kernel H r t : ℂ) ∂haarAddCircle) =
    (((1-r) * ((H-h : ℕ) : ℝ) + r * ((H+1-h : ℕ) : ℝ) : ℝ) : ℂ) :=
  integral_kernel_overlap H (h : ℤ) r

theorem kernel_nonneg {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (H : ℕ) (t : Circle₁) :
    0 ≤ kernel H r t :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr hr') (sq_nonneg _)) (mul_nonneg hr (sq_nonneg _))

theorem kernel_at_zero (H : ℕ) (r : ℝ) :
    kernel H r 0 = (H+r)^2 + r*(1-r) := by
  have hv (m : ℕ) : dirichlet m 0 = (m:ℂ) := by simp [dirichlet]
  have hn (m : ℕ) : ‖dirichlet m 0‖ = (m:ℝ) := by rw [hv, Complex.norm_natCast]
  simp only [kernel, hn, Nat.cast_add, Nat.cast_one]
  ring

theorem overlap_coefficient {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (H h : ℕ) :
    (1-r) * ((H-h : ℕ) : ℝ) + r * ((H+1-h : ℕ) : ℝ) =
      max ((H:ℝ)+r-h) 0 := by
  by_cases hh : h ≤ H
  · have hle : (h:ℝ) ≤ H := by exact_mod_cast hh
    rw [Nat.cast_sub hh, Nat.cast_sub (by omega : h ≤ H+1), Nat.cast_add, Nat.cast_one,
      max_eq_left (by linarith)]
    ring
  · have he : H+1 ≤ h := by omega
    have he' : (H:ℝ)+1 ≤ h := by exact_mod_cast he
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le he, max_eq_right (by linarith)]
    simp

/-- The Fourier coefficient at every integer lag of the fractional-width kernel. -/
theorem integral_kernel_signed (H : ℕ) (k : ℤ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    (∫ t : Circle₁, fourier k t * (kernel H r t : ℂ) ∂haarAddCircle) =
      ((max ((H : ℝ) + r - k.natAbs) 0 : ℝ) : ℂ) := by
  rw [integral_kernel_overlap, overlap_coefficient hr hr']

private def pairedMode (h : ℕ) (t : Circle₁) : ℂ :=
  fourier (h:ℤ) t + fourier (-(h:ℤ)) t

private theorem dirichlet_step (m : ℕ) (t : Circle₁) :
    dirichlet (m+1) t * conj (dirichlet (m+1) t) =
    dirichlet m t * conj (dirichlet m t) + 1 + ∑ h ∈ Ioc 0 m, pairedMode h t := by
  have hlast : fourier (m:ℤ) t * conj (dirichlet m t) =
      ∑ h ∈ Ioc 0 m, fourier (h:ℤ) t := by
    simp only [dirichlet, map_sum, mul_sum, ← fourier_neg, ← fourier_add]
    apply sum_bij' (fun j _ => m-j) (fun h _ => m-h)
    · intro j hj
      simp only [mem_range] at hj
      simp only [mem_Ioc]
      omega
    · intro h hh
      simp only [mem_Ioc] at hh
      apply mem_range.mpr
      omega
    · intro j hj
      simp only [mem_range] at hj
      omega
    · intro h hh
      simp only [mem_Ioc] at hh
      omega
    · intro j hj
      have hj' := mem_range.mp hj
      congr 2
      omega
  have hconj := congrArg (starRingEnd ℂ) hlast
  simp only [map_mul, starRingEnd_self_apply, map_sum] at hconj
  have hone : fourier (m:ℤ) t * conj (fourier (m:ℤ) t) = 1 := by
    rw [← fourier_neg, ← fourier_add, add_neg_cancel, fourier_zero]
  have hs : dirichlet (m+1) t = dirichlet m t + fourier (m:ℤ) t := sum_range_succ _ _
  rw [hs, map_add]
  simp only [pairedMode, fourier_neg, sum_add_distrib]
  linear_combination hlast + hconj + hone

private theorem integer_expansion (m : ℕ) (t : Circle₁) :
    dirichlet m t * conj (dirichlet m t) =
      (m:ℂ) + ∑ h ∈ Ioc 0 m, ((m:ℂ)-h) * pairedMode h t := by
  induction m with
  | zero => simp [dirichlet]
  | succ m ih =>
    rw [dirichlet_step, ih, sum_Ioc_succ_top (Nat.zero_le m)]
    push_cast
    simp only [sub_self, zero_mul, add_zero]
    have hs : (∑ h ∈ Ioc 0 m, ((m:ℂ)+1-h) * pairedMode h t) =
        (∑ h ∈ Ioc 0 m, ((m:ℂ)-h) * pairedMode h t) + ∑ h ∈ Ioc 0 m, pairedMode h t := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro h _
      ring
    rw [hs]
    ring

private theorem kernel_expansion (H : ℕ) (r : ℝ) (t : Circle₁) :
    (kernel H r t : ℂ) = (H:ℂ)+r +
      ∑ h ∈ Ioc 0 H, ((H:ℂ)+r-h) * pairedMode h t := by
  simp only [kernel, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, coe_normsq, dirichlet_step, integer_expansion]
  have hs : (∑ h ∈ Ioc 0 H, ((H:ℂ)+r-h) * pairedMode h t) =
      (∑ h ∈ Ioc 0 H, ((H:ℂ)-h) * pairedMode h t) + (r:ℂ)* ∑ h ∈ Ioc 0 H, pairedMode h t := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    ring
  rw [hs]
  ring

/-- Real expansion of the fractional kernel into positive-lag cosine modes. -/
theorem kernel_cosine_expansion (H : ℕ) (r : ℝ) (t : Circle₁) :
    kernel H r t = (H : ℝ) + r +
      ∑ h ∈ Ioc 0 H, (2 * ((H : ℝ) + r - h)) * (fourier (h : ℤ) t).re := by
  have hs (s : Finset ℕ) (f : ℕ → ℂ) : (∑ h ∈ s, f h).re = ∑ h ∈ s, (f h).re := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih => simp [hb, Complex.add_re, ih]
  have hc (h : ℕ) : (((H : ℂ) + r - h) * pairedMode h t).re =
      (2 * ((H : ℝ) + r - h)) * (fourier (h : ℤ) t).re := by
    rw [pairedMode, fourier_neg]
    simp [Complex.mul_re] <;> ring
  have he := congrArg Complex.re (kernel_expansion H r t)
  rw [Complex.ofReal_re, Complex.add_re, Complex.add_re, hs] at he
  simp_rw [hc] at he
  simpa using he

def energy (H : ℕ) (r : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∫ t : Circle₁, kernel H r t * ‖polynomial I a t‖^2 ∂haarAddCircle

/-- Exact Haar integral with the diagonal and both signed copies of each positive lag. -/
theorem energy_eq (H : ℕ) (r : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) :
    energy H r I a = ((H:ℝ)+r) * ∑ n ∈ I, (a n)^2 +
      2 * ∑ h ∈ Ioc 0 H, ((H:ℝ)+r-h) * correlation I a h := by
  let P := fun t : Circle₁ => polynomial I a t * conj (polynomial I a t)
  have hp : Continuous P := by
    have hc : Continuous (polynomial I a) :=
      continuous_finsetSum _ fun n _ => (fourier (n:ℤ)).continuous.const_mul _
    exact hc.mul (Complex.continuous_conj.comp hc)
  have intMode (k : ℤ) : Integrable (fun t : Circle₁ => fourier k t * P t) haarAddCircle :=
    ((fourier k).continuous.mul hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have intPair (h : ℕ) : Integrable (fun t : Circle₁ => pairedMode h t * P t) haarAddCircle := by
    exact (((fourier (h:ℤ)).continuous.add (fourier (-(h:ℤ))).continuous).mul hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpair (h : ℕ) : (∫ t : Circle₁, pairedMode h t * P t ∂haarAddCircle) =
      2 * (correlation I a h : ℂ) := by
    simp only [pairedMode, add_mul, integral_add (intMode _) (intMode _)]
    change (∫ t : Circle₁, _ ∂haarAddCircle) + (∫ t : Circle₁, _ ∂haarAddCircle) = _
    rw [show (∫ t : Circle₁, fourier (h:ℤ) t * P t ∂haarAddCircle) = _ from positive_mode I a h,
      show (∫ t : Circle₁, fourier (-(h:ℤ)) t * P t ∂haarAddCircle) = _ from negative_mode I a h]
    ring
  have hdiag : (∫ t : Circle₁, P t ∂haarAddCircle) = (↑(∑ n ∈ I, (a n)^2) : ℂ) := by
    simpa [correlation, P, pow_two] using positive_mode I a 0
  have hs (t : Circle₁) : (↑(kernel H r t * ‖polynomial I a t‖^2) : ℂ) =
      ((H:ℂ)+r)*P t + ∑ h ∈ Ioc 0 H, ((H:ℂ)+r-h)*(pairedMode h t*P t) := by
    rw [Complex.ofReal_mul, coe_normsq, kernel_expansion, add_mul, sum_mul]
    simp only [P, mul_assoc]
  apply Complex.ofReal_injective
  unfold energy
  rw [← integral_complex_ofReal]
  simp_rw [hs]
  rw [integral_add ((hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _)
    (integrable_finsetSum _ (fun h _ => (intPair h).const_mul _)),
    integral_finsetSum _ (fun h _ => (intPair h).const_mul _), integral_const_mul, hdiag]
  simp_rw [integral_const_mul, hpair]
  push_cast
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  ring

end RiemannResearch.Analysis.FractionalFejer
