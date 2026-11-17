import RiemannResearch.RH.QRamanujanContrastGram
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import RiemannResearch.Analysis.FiniteProfileEnergy

/-!
# Finite Ramanujan--Plancherel identity, including conductor one
Source: user-provided audited Exact-Head Green Profiles, section 8.
We prove the arithmetic kernel identity from prime contrasts, for every
squarefree period, and obtain polarization, inversion, the exact missing
trivial-conductor energy, and a sharp support-dependent mass remainder.
No optimizer bound or asymptotic input enters these identities.
PDF: https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanFinitePlancherel
open RiemannResearch.RH.Pareto

def primeContrast (p k : ℕ) : ℝ := (if p ∣ k then (p : ℝ) else 0) - 1

theorem totient_prime_product (n : ℕ) (hn : Squarefree n) :
    (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn] at h
  have he : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    nlinarith [Nat.pos_of_ne_zero hn.ne_zero]
  rw [he, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

theorem conductor_kernel_product (P g h : ℕ) (hP : Squarefree P) :
    (∑ a ∈ P.divisors, ramanujanSum a g * ramanujanSum a h / (a.totient : ℝ)) =
      ∏ p ∈ P.primeFactors,
        (1 + primeContrast p g * primeContrast p h / ((p : ℝ) - 1)) := by
  let f : ℕ → ℝ := fun p => primeContrast p g * primeContrast p h / ((p : ℝ) - 1)
  have he := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors f).prodPrimeFactors_one_add_of_squarefree hP
  calc
    _ = ∑ a ∈ P.divisors, (ArithmeticFunction.prodPrimeFactors f) a := by
      apply Finset.sum_congr rfl
      intro a ha
      have hs : Squarefree a := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha) hP
      rw [ramanujanSum_prime_contrasts a g hs, ramanujanSum_prime_contrasts a h hs,
        totient_prime_product a hs, ArithmeticFunction.prodPrimeFactors_apply hs.ne_zero]
      simp only [f, primeContrast, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    _ = _ := by
      rw [← he]
      apply Finset.prod_congr rfl
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      simp [ArithmeticFunction.prodPrimeFactors_apply hpr.ne_zero, hpr.primeFactors, f]

theorem squarefree_prime_factors_ext (P g h : ℕ) (hP : Squarefree P)
    (hg : g ∣ P) (hh : h ∣ P)
    (he : ∀ p ∈ P.primeFactors, (p ∣ g ↔ p ∣ h)) : g = h := by
  have hs : g.primeFactors = h.primeFactors := by
    rw [← Nat.primeFactors_filter_dvd_of_dvd hP.ne_zero hg,
      ← Nat.primeFactors_filter_dvd_of_dvd hP.ne_zero hh]
    ext p
    simp only [Finset.mem_filter]
    exact and_congr_right fun hp => he p hp
  rw [← Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hg hP),
    ← Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd hh hP), hs]

theorem conductor_kernel_off_diagonal (P g h : ℕ) (hP : Squarefree P)
    (hg : g ∣ P) (hh : h ∣ P) (hne : g ≠ h) :
    (∑ a ∈ P.divisors, ramanujanSum a g * ramanujanSum a h / (a.totient : ℝ)) = 0 := by
  rw [conductor_kernel_product P g h hP, Finset.prod_eq_zero_iff]
  have hm : ∃ p ∈ P.primeFactors, ¬(p ∣ g ↔ p ∣ h) := by
    by_contra! hn
    exact hne (squarefree_prime_factors_ext P g h hP hg hh hn)
  obtain ⟨p,hp,hm⟩ := hm
  refine ⟨p,hp,?_⟩
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have := Nat.prime_of_mem_primeFactors hp
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast this.one_lt))
  unfold primeContrast
  by_cases hpg : p ∣ g
  · by_cases hph : p ∣ h
    · exact (hm (iff_of_true hpg hph)).elim
    · simp only [hpg,hph,if_true,if_false,zero_sub]
      field_simp [hp1]
      <;> ring
  · by_cases hph : p ∣ h
    · simp only [hpg,hph,if_true,if_false,zero_sub]
      field_simp [hp1]
      <;> ring
    · exact (hm (iff_of_false hpg hph)).elim

theorem conductor_kernel_diagonal (P g : ℕ) (hP : Squarefree P) (hg : g ∣ P) :
    (∑ a ∈ P.divisors, ramanujanSum a g ^ 2 / (a.totient : ℝ)) =
      (P : ℝ) / P.totient * g.totient := by
  simp_rw [pow_two]
  rw [conductor_kernel_product P g g hP]
  have hp1 (p : ℕ) (hp : p ∈ P.primeFactors) : (p : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt))
  calc
    _ = ∏ p ∈ P.primeFactors,
        ((p : ℝ) / ((p : ℝ) - 1) * (if p ∣ g then (p : ℝ) - 1 else 1)) := by
      apply Finset.prod_congr rfl
      intro p hp
      unfold primeContrast
      by_cases h : p ∣ g <;> simp only [h, if_true, if_false] <;>
        field_simp [hp1 p hp] <;> ring
    _ = (∏ p ∈ P.primeFactors, (p : ℝ)) /
        (∏ p ∈ P.primeFactors, ((p : ℝ) - 1)) *
        (∏ p ∈ g.primeFactors, ((p : ℝ) - 1)) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      congr 1
      rw [← Finset.prod_filter, Nat.primeFactors_filter_dvd_of_dvd hP.ne_zero hg]
    _ = _ := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hP,
        ← totient_prime_product P hP, ← totient_prime_product g (Squarefree.squarefree_of_dvd hg hP)]


theorem conductor_kernel (P g h : ℕ) (hP : Squarefree P)
    (hg : g ∣ P) (hh : h ∣ P) :
    (∑ a ∈ P.divisors, ramanujanSum a g * ramanujanSum a h / (a.totient : ℝ)) =
      if g = h then (P : ℝ) / P.totient * g.totient else 0 := by
  by_cases he : g = h
  · subst h
    simpa only [if_true, pow_two] using conductor_kernel_diagonal P g hP hg
  · simpa [he] using conductor_kernel_off_diagonal P g h hP hg hh he

def transform (P : ℕ) (W : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ g ∈ P.divisors, W g * ramanujanSum a g

theorem transform_one (P : ℕ) (W : ℕ → ℝ) :
    transform P W 1 = ∑ g ∈ P.divisors, W g := by
  simp [transform, ramanujanSum]

theorem polarized_plancherel (P : ℕ) (hP : Squarefree P) (W V : ℕ → ℝ) :
    (∑ a ∈ P.divisors, transform P W a * transform P V a / (a.totient : ℝ)) =
      (P : ℝ) / P.totient * ∑ g ∈ P.divisors, (g.totient : ℝ) * W g * V g := by
  calc
    _ = ∑ a ∈ P.divisors, ∑ g ∈ P.divisors, ∑ h ∈ P.divisors,
        W g * V h * (ramanujanSum a g * ramanujanSum a h / (a.totient : ℝ)) := by
      unfold transform
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = ∑ g ∈ P.divisors, ∑ h ∈ P.divisors, W g * V h *
        (∑ a ∈ P.divisors, ramanujanSum a g * ramanujanSum a h / (a.totient : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ g ∈ P.divisors, W g * V g * ((P : ℝ) / P.totient * g.totient) := by
      apply Finset.sum_congr rfl
      intro g hg
      calc
        _ = ∑ h ∈ P.divisors, W g * V h *
            (if g = h then (P : ℝ) / P.totient * g.totient else 0) := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [conductor_kernel P g h hP (Nat.dvd_of_mem_divisors hg)
            (Nat.dvd_of_mem_divisors hh)]
        _ = _ := by simp [hg]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring

theorem corrected_plancherel (P : ℕ) (hP : Squarefree P) (W : ℕ → ℝ) :
    (∑ a ∈ P.divisors, transform P W a ^ 2 / (a.totient : ℝ)) =
      (P : ℝ) / P.totient * ∑ g ∈ P.divisors, (g.totient : ℝ) * W g ^ 2 := by
  simpa only [pow_two, mul_assoc] using polarized_plancherel P hP W W

theorem nontrivial_conductor_energy (P : ℕ) (hP : Squarefree P) (W : ℕ → ℝ) :
    (∑ a ∈ P.divisors.erase 1, transform P W a ^ 2 / (a.totient : ℝ)) =
      (P : ℝ) / P.totient * ∑ g ∈ P.divisors, (g.totient : ℝ) * W g ^ 2 -
        (∑ g ∈ P.divisors, W g) ^ 2 := by
  have h1 := Finset.sum_erase_add P.divisors
    (fun a => transform P W a ^ 2 / (a.totient : ℝ))
    (Nat.one_mem_divisors.mpr hP.ne_zero)
  rw [corrected_plancherel P hP W, transform_one] at h1
  norm_num at h1
  linarith

theorem omitted_conductor_identity_iff (P : ℕ) (hP : Squarefree P) (W : ℕ → ℝ) :
    ((∑ a ∈ P.divisors.erase 1, transform P W a ^ 2 / (a.totient : ℝ)) =
      (P : ℝ) / P.totient * ∑ g ∈ P.divisors, (g.totient : ℝ) * W g ^ 2) ↔
        ∑ g ∈ P.divisors, W g = 0 := by
  rw [nontrivial_conductor_energy P hP W]
  constructor
  · intro h
    nlinarith [sq_nonneg (∑ g ∈ P.divisors, W g)]
  · intro h
    rw [h]
    ring

theorem transform_inverse (P g : ℕ) (hP : Squarefree P) (hg : g ∈ P.divisors)
    (W : ℕ → ℝ) :
    W g = (P.totient : ℝ) / ((P : ℝ) * g.totient) *
      ∑ a ∈ P.divisors, ramanujanSum a g * transform P W a / (a.totient : ℝ) := by
  have hs : (∑ a ∈ P.divisors, ramanujanSum a g * transform P W a /
      (a.totient : ℝ)) = W g * ((P : ℝ) / P.totient * g.totient) := by
    unfold transform
    simp_rw [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    calc
      _ = ∑ h ∈ P.divisors, W h * ∑ a ∈ P.divisors,
          ramanujanSum a g * ramanujanSum a h / (a.totient : ℝ) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by
        have he (h : ℕ) (hh : h ∈ P.divisors) :=
          conductor_kernel P g h hP (Nat.dvd_of_mem_divisors hg) (Nat.dvd_of_mem_divisors hh)
        calc
          _ = ∑ h ∈ P.divisors, W h *
              (if g = h then (P : ℝ) / P.totient * g.totient else 0) := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [he h hh]
          _ = _ := by simp [hg]
  rw [hs]
  have hp0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne_zero
  have ht0 : (P.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hP.ne_zero)).ne'
  have hg0 : (g.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hg)).ne'
  field_simp


/-- Exact weighted mass remainder on any retained gcd support. It exposes
precisely the deviation from the extremizer W(g) proportional to 1/phi(g). -/
theorem weighted_mass_remainder (D : Finset ℕ)
    (hD : ∀ g ∈ D, 0 < g) (W : ℕ → ℝ) :
    (∑ g ∈ D, (g.totient : ℝ) * W g ^ 2) *
      (∑ g ∈ D, 1 / (g.totient : ℝ)) - (∑ g ∈ D, W g) ^ 2 =
        (∑ g ∈ D, ∑ h ∈ D, (g.totient : ℝ) * h.totient *
          (W g / (h.totient : ℝ) - W h / (g.totient : ℝ)) ^ 2) / 2 := by
  have hn (g : ℕ) (hg : g ∈ D) : (g.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (hD g hg)).ne'
  have hE : RiemannResearch.Analysis.FiniteProfileEnergy.energy D
      (fun g => (g.totient : ℝ)) (fun g => 1 / (g.totient : ℝ)) =
        ∑ g ∈ D, 1 / (g.totient : ℝ) := by
    apply Finset.sum_congr rfl
    intro g hg
    field_simp [hn g hg]
  have hM : RiemannResearch.Analysis.FiniteProfileEnergy.pairing D
      (fun g => (g.totient : ℝ)) W (fun g => 1 / (g.totient : ℝ)) =
        ∑ g ∈ D, W g := by
    apply Finset.sum_congr rfl
    intro g hg
    field_simp [hn g hg]
  have h := RiemannResearch.Analysis.FiniteProfileEnergy.gram_identity D
    (fun g => (g.totient : ℝ)) W (fun g => 1 / (g.totient : ℝ))
  rw [hE,hM] at h
  simpa only [RiemannResearch.Analysis.FiniteProfileEnergy.energy,
    div_eq_mul_inv, one_mul] using h

theorem weighted_mass_sq_le (D : Finset ℕ)
    (hD : ∀ g ∈ D, 0 < g) (W : ℕ → ℝ) :
    (∑ g ∈ D, W g)^2 ≤
      (∑ g ∈ D, 1/(g.totient : ℝ)) *
        (∑ g ∈ D, (g.totient : ℝ) * W g^2) := by
  have he := weighted_mass_remainder D hD W
  have hn : 0 ≤ ∑ g ∈ D, ∑ h ∈ D, (g.totient : ℝ) * h.totient *
      (W g / (h.totient : ℝ) - W h / (g.totient : ℝ)) ^ 2 := by
    apply Finset.sum_nonneg
    intro g hg
    apply Finset.sum_nonneg
    intro h hh
    positivity
  nlinarith

end RiemannResearch.RH.Pareto.RamanujanFinitePlancherel
