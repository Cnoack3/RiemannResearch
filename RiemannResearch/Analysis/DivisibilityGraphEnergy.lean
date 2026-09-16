import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Exact von-Mangoldt divisibility energy and its harmonic blind direction

The second diagonal sum is reindexed exactly as a harmonic von-Mangoldt sum.
Its logarithmic upper bound is proved from Chebyshev and divisor convolution.
No zero-ordinate asymptotic is assumed. All coefficients are complex.
-/

noncomputable section
open ArithmeticFunction
open scoped BigOperators

namespace RiemannResearch.Analysis.DivisibilityGraphEnergy

lemma scaled_edge_roots (b r k : ℝ) (hb : b ≠ 0) (hr : r ≠ 0) (z w : ℂ) :
    2 * k / r * (z * star w).re =
      k * ‖z‖ ^ 2 + k / r ^ 2 * ‖w‖ ^ 2 -
        k / (b ^ 2 * r ^ 2) * ‖((b * r : ℝ) : ℂ) * z - (b : ℂ) * w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp [hb, hr]
  ring

lemma scaled_edge (m d k : ℝ) (hm : 0 < m) (hd : 0 < d) (z w : ℂ) :
    2 * k / Real.sqrt d * (z * star w).re =
      k * ‖z‖ ^ 2 + k / d * ‖w‖ ^ 2 -
        k / (m * d) * ‖(Real.sqrt (m * d) : ℂ) * z - (Real.sqrt m : ℂ) * w‖ ^ 2 := by
  have h := scaled_edge_roots (Real.sqrt m) (Real.sqrt d) k
    (ne_of_gt (Real.sqrt_pos.mpr hm)) (ne_of_gt (Real.sqrt_pos.mpr hd)) z w
  simpa only [Real.sq_sqrt hm.le, Real.sq_sqrt hd.le, ← Real.sqrt_mul hm.le] using h

/-- The complete signed prime-power-ratio form in divisor coordinates. -/
def signedForm (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
    2 * vonMangoldt d / Real.sqrt d * (a n * star (a (n / d))).re

/-- The nonnegative graph energy, with exact weights. -/
def graphEnergy (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
    vonMangoldt d / (n : ℝ) *
      ‖(Real.sqrt n : ℂ) * a n - (Real.sqrt (n / d : ℕ) : ℂ) * a (n / d)‖ ^ 2

/-- The outgoing diagonal sum, before reindexing it as sum_n A(N/n)|a_n|^2. -/
def outgoingDiagonal (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
    vonMangoldt d / (d : ℝ) * ‖a (n / d)‖ ^ 2

lemma divisor_pos {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) : 0 < d := by
  have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
  by_contra h
  have hd0 : d = 0 := by omega
  subst d
  have hn0 : n = 0 := by simpa using hdn
  omega

lemma quotient_pos {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) : 0 < n / d :=
  Nat.div_pos (Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1) (divisor_pos hn hd)

/-- Exact signed decomposition. The first diagonal sum is log(n), proved by
Mathlib's actual von-Mangoldt divisor identity, not taken as an assumption. -/
theorem signed_decomposition (N : ℕ) (a : ℕ → ℂ) :
    signedForm N a =
      (∑ n ∈ Finset.Icc 1 N, Real.log n * ‖a n‖ ^ 2) +
        outgoingDiagonal N a - graphEnergy N a := by
  unfold signedForm outgoingDiagonal graphEnergy
  have hex (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (d : ℕ) (hd : d ∈ n.divisors) :
      2 * vonMangoldt d / Real.sqrt d * (a n * star (a (n / d))).re =
        vonMangoldt d * ‖a n‖ ^ 2 + vonMangoldt d / (d : ℝ) * ‖a (n / d)‖ ^ 2 -
          vonMangoldt d / (n : ℝ) *
            ‖(Real.sqrt n : ℂ) * a n - (Real.sqrt (n / d : ℕ) : ℂ) * a (n / d)‖ ^ 2 := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hmd : ((n / d : ℕ) : ℝ) * (d : ℝ) = n := by
      exact_mod_cast Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    have h := scaled_edge ((n / d : ℕ) : ℝ) d (vonMangoldt d)
      (by exact_mod_cast quotient_pos hnpos hd) (by exact_mod_cast divisor_pos hnpos hd)
      (a n) (a (n / d))
    simpa only [hmd] using h
  simp_rw [Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun d hd => hex n hn d hd))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, vonMangoldt_sum]

theorem graphEnergy_nonneg (N : ℕ) (a : ℕ → ℂ) : 0 ≤ graphEnergy N a := by
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)

lemma sqrt_cancel (n : ℕ) (hn : 0 < n) (c : ℂ) :
    (Real.sqrt n : ℂ) * (c / (Real.sqrt n : ℂ)) = c := by
  have hroot : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn : 0 < (n : ℝ)))
  field_simp

/-- The exact harmonic blind direction a_n = c/sqrt(n). -/
theorem harmonic_direction_zero (N : ℕ) (c : ℂ) :
    graphEnergy N (fun n => c / (Real.sqrt n : ℂ)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro d hd
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [sqrt_cancel n hnpos, sqrt_cancel (n / d) (quotient_pos hnpos hd)]
  simp

/-- The exact harmonic von-Mangoldt partial sum. -/
def mangoldtHarmonic (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, vonMangoldt d / (d : ℝ)

lemma positive_interval (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

lemma sum_mangoldt_floor (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N, Real.log n := by
  have h := sum_Ioc_mul_zeta_eq_sum vonMangoldt N
  simpa only [positive_interval, vonMangoldt_mul_zeta, log_apply] using h.symm

lemma ratio_le_nat_quotient_add_one (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (div_le_iff₀ hdreal).mpr
  have hdecomp : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.div_add_mod N d
  have hmod : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  nlinarith

lemma sum_log_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Real.log n) ≤ (N : ℝ) * Real.log N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log N := by
      apply Finset.sum_le_sum
      intro n hn
      exact Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
    _ = _ := by simp

lemma sum_mangoldt_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, vonMangoldt d) ≤ (Real.log 4 + 4) * N := by
  simpa [positive_interval, Chebyshev.psi] using
    (Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity))

/-- A sharp-leading-coefficient Mertens upper bound, derived from Mathlib's
Chebyshev bound and the exact divisor convolution, with no asymptotic premise. -/
theorem mangoldtHarmonic_le_log (N : ℕ) (hN : 0 < N) :
    mangoldtHarmonic N ≤ Real.log N + (Real.log 4 + 4) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbound : (N : ℝ) * mangoldtHarmonic N ≤
      (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N : ℝ) / d) := by
        unfold mangoldtHarmonic
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ ≤ ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * (((N / d : ℕ) : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left
          (ratio_le_nat_quotient_add_one N d (Finset.mem_Icc.mp hd).1) vonMangoldt_nonneg
      _ = (∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ)) +
          ∑ d ∈ Finset.Icc 1 N, vonMangoldt d := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib]
      _ ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by
        rw [sum_mangoldt_floor]
        exact add_le_add (sum_log_le N) (sum_mangoldt_le N)
      _ = _ := by ring
  nlinarith

/-- This exact graph energy cannot control coefficient mass, even on a fixed
nonempty support: the harmonic direction is nonzero but has zero energy. -/
theorem graph_not_coercive (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    ¬ ∀ a : ℕ → ℂ, c * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ graphEnergy N a := by
  intro h
  have hh := h (fun n => (1 : ℂ) / (Real.sqrt n : ℂ))
  rw [harmonic_direction_zero] at hh
  have hsum := Finset.single_le_sum (s := Finset.Icc 1 N)
    (f := fun n : ℕ => ‖(1 : ℂ) / (Real.sqrt n : ℂ)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩ : 1 ∈ Finset.Icc 1 N)
  norm_num at hsum hh
  nlinarith

/-- Exact change from divisor coordinates (n,d) to multiplicative coordinates (m,d). -/
lemma divisor_sum_reindex (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f (n / d) d) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / m), f m d := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun a _ => ⟨a.1 / a.2, a.2⟩)
  · intro a ha
    obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hnpos, hnle⟩ := Finset.mem_Icc.mp hn
    have hmpos := quotient_pos hnpos hd
    have hdpos := divisor_pos hnpos hd
    have hprod := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hmpos, (Nat.div_le_self _ _).trans hnle⟩,
      Finset.mem_Icc.mpr ⟨hdpos, ?_⟩⟩
    apply (Nat.le_div_iff_mul_le hmpos).mpr
    nlinarith
  · intro a ha b hb hab
    have hquot : a.1 / a.2 = b.1 / b.2 := congrArg Sigma.fst hab
    have hd' := congrArg (fun p : Σ _ : ℕ, ℕ => p.2) hab
    have hd : a.2 = b.2 := hd'
    have hprodA := Nat.div_mul_cancel (Nat.mem_divisors.mp (Finset.mem_sigma.mp ha).2).1
    have hprodB := Nat.div_mul_cancel (Nat.mem_divisors.mp (Finset.mem_sigma.mp hb).2).1
    have hn : a.1 = b.1 := by rw [← hprodA, ← hprodB, hquot, hd]
    exact Sigma.ext hn (heq_of_eq hd)
  · intro b hb
    obtain ⟨hm, hd⟩ := Finset.mem_sigma.mp hb
    obtain ⟨hmpos, hmle⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hdpos, hdle⟩ := Finset.mem_Icc.mp hd
    have hnpos : 0 < b.1 * b.2 := Nat.mul_pos hmpos hdpos
    have hnle : b.1 * b.2 ≤ N := by
      have h := (Nat.le_div_iff_mul_le hmpos).mp hdle
      simpa only [Nat.mul_comm] using h
    have hdvd : b.2 ∣ b.1 * b.2 := ⟨b.1, by ring⟩
    refine ⟨⟨b.1 * b.2, b.2⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, hnle⟩,
        Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt hnpos⟩⟩, ?_⟩
    apply Sigma.ext
    · exact Nat.mul_div_cancel _ hdpos
    · rfl
  · intro a ha
    rfl

/-- The outgoing diagonal really is the harmonic von-Mangoldt partial sum. -/
theorem outgoingDiagonal_reindexed (N : ℕ) (a : ℕ → ℂ) :
    outgoingDiagonal N a =
      ∑ m ∈ Finset.Icc 1 N, mangoldtHarmonic (N / m) * ‖a m‖ ^ 2 := by
  unfold outgoingDiagonal
  rw [divisor_sum_reindex N (fun m d => vonMangoldt d / (d : ℝ) * ‖a m‖ ^ 2)]
  simp only [mangoldtHarmonic, Finset.sum_mul]

/-- The exact logarithmic diagonal minus the positive graph energy. -/
theorem signed_decomposition_reindexed (N : ℕ) (a : ℕ → ℂ) :
    signedForm N a =
      (∑ n ∈ Finset.Icc 1 N, (Real.log n + mangoldtHarmonic (N / n)) * ‖a n‖ ^ 2) -
        graphEnergy N a := by
  rw [signed_decomposition, outgoingDiagonal_reindexed]
  simp only [add_mul, Finset.sum_add_distrib]

lemma diagonal_le_log (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    Real.log n + mangoldtHarmonic (N / n) ≤ Real.log N + (Real.log 4 + 4) := by
  obtain ⟨hnpos, hnle⟩ := Finset.mem_Icc.mp hn
  have hqpos : 0 < N / n := Nat.div_pos hnle hnpos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hqR : 0 < ((N / n : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hprod : (n : ℝ) * ((N / n : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.mul_div_le N n
  have hlog := Real.log_le_log (mul_pos hnR hqR) hprod
  rw [Real.log_mul hnR.ne' hqR.ne'] at hlog
  have hA := mangoldtHarmonic_le_log (N / n) hqpos
  linarith

/-- Unconditional logarithmic upper bound for the complete signed form. -/
theorem signedForm_upper_bound (N : ℕ) (a : ℕ → ℂ) :
    signedForm N a ≤ (Real.log N + (Real.log 4 + 4)) *
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rw [signed_decomposition_reindexed, Finset.mul_sum]
  apply le_trans (sub_le_self _ (graphEnergy_nonneg N a))
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_right (diagonal_le_log N n hn) (sq_nonneg _)

/-- An absolute bound is proved by comparison of whole quadratic forms, not by
removing the signed structure in the exact decomposition. -/
lemma signedForm_abs_le_norm_form (N : ℕ) (a : ℕ → ℂ) :
    |signedForm N a| ≤ signedForm N (fun n => (‖a n‖ : ℂ)) := by
  unfold signedForm
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro n hn
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro d hd
  have hw : 0 ≤ 2 * vonMangoldt d / Real.sqrt d := by positivity
  rw [abs_mul, abs_of_nonneg hw]
  have h := Complex.abs_re_le_norm (a n * star (a (n / d)))
  simp only [norm_mul, norm_star] at h
  have hb : (((‖a n‖ : ℝ) : ℂ) * star ((‖a (n / d)‖ : ℝ) : ℂ)).re =
      ‖a n‖ * ‖a (n / d)‖ := by simp
  rw [hb]
  exact mul_le_mul_of_nonneg_left h hw

/-- The logarithmic spectral-form bound, with an explicit absolute constant.
This is the signed prime-power quadratic form from the sampling expansion. -/
theorem signedForm_absolute_bound (N : ℕ) (a : ℕ → ℂ) :
    |signedForm N a| ≤ (Real.log N + (Real.log 4 + 4)) *
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := (signedForm_abs_le_norm_form N a).trans
    (signedForm_upper_bound N (fun n => (‖a n‖ : ℂ)))
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using h

end RiemannResearch.Analysis.DivisibilityGraphEnergy
