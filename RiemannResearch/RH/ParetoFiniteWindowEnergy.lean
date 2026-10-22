import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import RiemannResearch.RH.RawMobiusFiniteWindowEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complete Pareto finite-window and signed-pair identities

Source: Christian Noack's user-supplied Green--Pareto--Schur continuation,
6 October 2026, Sections 22 and 24. The source supports the statements and the signed-square proof strategy.

The complete farther physical tail is retained. The ordered off-diagonal
quantity is half the sum of every ordered unequal pair. It equals the usual
strict upper-triangle sum when the kernel is symmetric, but that extra
identification is not needed for the complete square decomposition.

The repository already proves rawMobius_energy_three_regions,
rawMobiusFarEnergy_le and rawMobius_energy_le_square_window for the raw
family. The generic exact-head norm bounds below extend that existing
architecture to the crossing-balanced family; they do not claim the raw
localization as a new result. The numerical atom is the existing actual
ArithmeticCumulative.residueFraction, not a replacement kernel.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.FiniteWindow

/-- The actual physical Pareto squared energy on the finite window. -/
def windowEnergy (n : ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico n (n * n), positiveWeight j * (e j)^2

/-- The complete physical squared energy at and beyond the square cutoff. -/
def farEnergy (n : ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, positiveWeight (k + n * n) * (e (k + n * n))^2

def windowMass (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico n (n * n), positiveWeight j

private theorem positiveWeight_recip_diff (j : ℕ) (hj : 0 < j) :
    positiveWeight j = 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  unfold positiveWeight
  field_simp [hjR, hj1]
  ring

private theorem shifted_weight_partial (a b : ℕ) (ha : 0 < a) :
    (∑ i ∈ Finset.range b, positiveWeight (a + i)) =
      1 / (a : ℝ) - 1 / ((a : ℝ) + (b : ℝ)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih,
      positiveWeight_recip_diff (a + b) (by omega)]
    push_cast
    ring

/-- The exact sum of all weights in the finite window, including both cutoffs. -/
theorem windowMass_eq (n : ℕ) (hn : 0 < n) :
    windowMass n = 1 / (n : ℝ) - 1 / (n : ℝ)^2 := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hbij :
      (∑ i ∈ Finset.range (n * n - n), positiveWeight (n + i)) =
        ∑ j ∈ Finset.Ico n (n * n), positiveWeight j := by
    refine Finset.sum_bij (fun i _ => n + i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Ico]
      omega
    · intro i hi k hk h
      omega
    · intro j hj
      have hh := Finset.mem_Ico.mp hj
      refine ⟨j - n, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro i hi
      rfl
  unfold windowMass
  rw [← hbij, shifted_weight_partial n (n * n - n) hn]
  have hcast :
      (n : ℝ) + ((n * n - n : ℕ) : ℝ) = (n : ℝ)^2 := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hnn, Nat.cast_mul]
    ring
  rw [hcast]

theorem windowMass_nonneg (n : ℕ) : 0 ≤ windowMass n := by
  exact Finset.sum_nonneg (fun j _ => positiveWeight_nonneg j)

theorem windowEnergy_nonneg (n : ℕ) (e : ℕ → ℝ) :
    0 ≤ windowEnergy n e := by
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (positiveWeight_nonneg j) (sq_nonneg (e j)))

theorem farEnergy_nonneg (n : ℕ) (e : ℕ → ℝ) :
    0 ≤ farEnergy n e := by
  exact tsum_nonneg (fun k =>
    mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))

/-- The elementary global residual bound controls the entire farther tail. -/
theorem farEnergy_le_one (n : ℕ) (hn : 0 < n)
    (e : ℕ → ℝ) (he : ∀ j, |e j| ≤ (n : ℝ)) :
    farEnergy n e ≤ 1 := by
  have hs0 : Summable (fun j : ℕ => positiveWeight j * (e j)^2) := by
    simpa only [pow_two] using
      (weighted_summable_of_bounded (bounded_product he he))
  have hs := (summable_nat_add_iff (n * n)).mpr hs0
  have hw := (summable_nat_add_iff (n * n)).mpr positiveWeight_summable
  have hb (k : ℕ) :
      positiveWeight (k + n * n) * (e (k + n * n))^2 ≤
        positiveWeight (k + n * n) * (n : ℝ)^2 := by
    apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
    have hh := abs_le.mp (he (k + n * n))
    have hp :
        0 ≤ ((n : ℝ) - e (k + n * n)) *
          ((n : ℝ) + e (k + n * n)) :=
      mul_nonneg (by linarith [hh.2]) (by linarith [hh.1])
    nlinarith [hp]
  unfold farEnergy
  calc
    _ ≤ ∑' k : ℕ, positiveWeight (k + n * n) * (n : ℝ)^2 :=
      hs.tsum_le_tsum hb (hw.mul_right _)
    _ = (1 / ((n * n : ℕ) : ℝ)) * (n : ℝ)^2 := by
      rw [tsum_mul_right,
        positiveWeight_tail_tsum (n * n) (Nat.mul_pos hn hn)]
    _ = 1 := by
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      push_cast
      field_simp

/-- Genuine Hilbert norm decomposition, with a proved vanishing initial head. -/
theorem norm_sq_eq_window_add_far (f : ThresholdHilbert) (n : ℕ)
    (hhead : ∀ j < n, hilbertSequence f j = 0) :
    ‖f‖^2 = windowEnergy n (hilbertSequence f) +
      farEnergy n (hilbertSequence f) := by
  have hs := hilbertSequence_square_summable f
  have hh :
      (∑ j ∈ Finset.range n,
        positiveWeight j * (hilbertSequence f j)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hhead j (Finset.mem_range.mp hj)]
    simp
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hw :
      (∑ j ∈ Finset.Ico n (n * n),
        positiveWeight j * (hilbertSequence f j)^2) =
      ∑ j ∈ Finset.range (n * n),
        positiveWeight j * (hilbertSequence f j)^2 := by
    rw [Finset.sum_Ico_eq_sub _ hnn, hh, sub_zero]
  unfold windowEnergy farEnergy
  rw [hw, hilbert_norm_weighted_sq]
  exact (hs.sum_add_tsum_nat_add (n * n)).symm

/-- The finite certificate bounds the actual full residual norm from both sides. -/
theorem norm_sq_window_bounds (f : ThresholdHilbert) (n : ℕ) (hn : 0 < n)
    (hhead : ∀ j < n, hilbertSequence f j = 0)
    (habs : ∀ j, |hilbertSequence f j| ≤ (n : ℝ)) :
    windowEnergy n (hilbertSequence f) ≤ ‖f‖^2 ∧
      ‖f‖^2 ≤ windowEnergy n (hilbertSequence f) + 1 := by
  rw [norm_sq_eq_window_add_far f n hhead]
  constructor
  · linarith [farEnergy_nonneg n (hilbertSequence f)]
  · linarith [farEnergy_le_one n hn (hilbertSequence f) habs]

/-! The following finite kernel core retains the complete signed square. -/

theorem kernel_quadratic_eq_weighted_square (s J : Finset ℕ)
    (a w : ℕ → ℝ) (g : ℕ → ℕ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, a d * a e *
      (∑ j ∈ J, w j * g d j * g e j)) =
      ∑ j ∈ J, w j * (∑ d ∈ s, a d * g d j)^2 := by
  classical
  calc
    _ = ∑ d ∈ s, ∑ e ∈ s, ∑ j ∈ J,
        w j * (a d * g d j) * (a e * g e j) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ d ∈ s, ∑ j ∈ J, ∑ e ∈ s,
        w j * (a d * g d j) * (a e * g e j) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ j ∈ J, ∑ d ∈ s, ∑ e ∈ s,
        w j * (a d * g d j) * (a e * g e j) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_two, Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring

/-- Every unequal signed interaction is included, with no symmetry premise. -/
theorem complete_signed_pair_split (s : Finset ℕ) (a : ℕ → ℝ)
    (K : ℕ → ℕ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, a d * a e * K d e) =
      (∑ d ∈ s, (a d)^2 * K d d) +
      2 * ((1 / 2 : ℝ) * ∑ d ∈ s, ∑ e ∈ s.erase d,
        a d * a e * K d e) := by
  classical
  calc
    _ = ∑ d ∈ s, ((a d)^2 * K d d +
        ∑ e ∈ s.erase d, a d * a e * K d e) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_erase_add s (fun e => a d * a e * K d e) hd]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib]
      ring

/-! A literal numerical residue atom specializes the diagonal bound. -/

abbrev modularAtom (d j : ℕ) : ℝ :=
  ArithmeticCumulative.residueFraction d j

theorem modularAtom_nonneg (d j : ℕ) : 0 ≤ modularAtom d j := by
  unfold modularAtom ArithmeticCumulative.residueFraction
  positivity

theorem modularAtom_le_one (d j : ℕ) (hd : 0 < d) :
    modularAtom d j ≤ 1 := by
  have hh := residueFraction_abs_le_one d j
    (Nat.succ_le_of_lt hd)
  exact (le_abs_self _).trans hh

/-- The numerical residue is the physical sequence of the existing Hilbert atom. -/
theorem modularAtom_eq_hilbertSequence (d j : ℕ) (hd : 1 ≤ d) :
    modularAtom d j =
      hilbertSequence (normalizedResidueHilbert d hd) j := by
  exact (congrFun (normalizedResidueHilbert_sequence d hd) j).symm

def modularWindowKernel (n d e : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico n (n * n),
    positiveWeight j * modularAtom d j * modularAtom e j

theorem modularWindowKernel_nonneg (n d e : ℕ) :
    0 ≤ modularWindowKernel n d e := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (positiveWeight_nonneg j) (modularAtom_nonneg d j))
    (modularAtom_nonneg e j)

theorem modularWindowKernel_diag_le_mass (n d : ℕ) (hd : 0 < d) :
    modularWindowKernel n d d ≤ windowMass n := by
  unfold modularWindowKernel windowMass
  apply Finset.sum_le_sum
  intro j hj
  have hg0 := modularAtom_nonneg d j
  have hg1 := modularAtom_le_one d j hd
  have hsq : (modularAtom d j)^2 ≤ 1 := by
    nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg1)]
  have h := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg j)
  nlinarith [h]

def modularDiagonal (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Ico 2 (n + 1), (a d)^2 * modularWindowKernel n d d

def modularQuadratic (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Ico 2 (n + 1), ∑ e ∈ Finset.Ico 2 (n + 1),
    a d * a e * modularWindowKernel n d e

def modularSignedPair (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ d ∈ Finset.Ico 2 (n + 1),
    ∑ e ∈ (Finset.Ico 2 (n + 1)).erase d,
      a d * a e * modularWindowKernel n d e

theorem modularQuadratic_eq_weighted_square (n : ℕ) (a : ℕ → ℝ) :
    modularQuadratic n a =
      ∑ j ∈ Finset.Ico n (n * n),
        positiveWeight j *
          (∑ d ∈ Finset.Ico 2 (n + 1), a d * modularAtom d j)^2 := by
  exact kernel_quadratic_eq_weighted_square
    (Finset.Ico 2 (n + 1)) (Finset.Ico n (n * n)) a positiveWeight modularAtom

theorem modularQuadratic_nonneg (n : ℕ) (a : ℕ → ℝ) :
    0 ≤ modularQuadratic n a := by
  rw [modularQuadratic_eq_weighted_square]
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (positiveWeight_nonneg j) (sq_nonneg _))

theorem modularQuadratic_eq_diagonal_add_pair (n : ℕ) (a : ℕ → ℝ) :
    modularQuadratic n a = modularDiagonal n a + 2 * modularSignedPair n a := by
  exact complete_signed_pair_split
    (Finset.Ico 2 (n + 1)) a (modularWindowKernel n)

theorem modularDiagonal_nonneg (n : ℕ) (a : ℕ → ℝ) :
    0 ≤ modularDiagonal n a := by
  exact Finset.sum_nonneg (fun d _ =>
    mul_nonneg (sq_nonneg _) (modularWindowKernel_nonneg n d d))

/-- The actual modular diagonal is uniformly bounded before any cancellation. -/
theorem modularDiagonal_le_count_mass (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ d ∈ Finset.Ico 2 (n + 1), |a d| ≤ 1) :
    modularDiagonal n a ≤ ((n - 1 : ℕ) : ℝ) * windowMass n := by
  have hcount : (Finset.Ico 2 (n + 1)).card = n - 1 := by
    simp
  unfold modularDiagonal
  calc
    _ ≤ ∑ _d ∈ Finset.Ico 2 (n + 1), windowMass n := by
      apply Finset.sum_le_sum
      intro d hd
      have hdd : 0 < d := by
        have hh := Finset.mem_Ico.mp hd
        omega
      have haa := abs_le.mp (ha d hd)
      have hsq : (a d)^2 ≤ 1 := by
        have hp : 0 ≤ (1 - a d) * (1 + a d) :=
          mul_nonneg (by linarith [haa.2]) (by linarith [haa.1])
        nlinarith [hp]
      calc
        _ ≤ 1 * modularWindowKernel n d d :=
          mul_le_mul_of_nonneg_right hsq (modularWindowKernel_nonneg n d d)
        _ = modularWindowKernel n d d := one_mul _
        _ ≤ windowMass n := modularWindowKernel_diag_le_mass n d hdd
    _ = _ := by simp [hcount]

theorem count_mass_lt_one (n : ℕ) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℝ) * windowMass n < 1 := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hnR
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [windowMass_eq n (by omega), hcast]
  have hform :
      ((n : ℝ) - 1) * (1 / (n : ℝ) - 1 / (n : ℝ)^2) =
        ((n : ℝ) - 1)^2 / (n : ℝ)^2 := by
    field_simp [hnne]
  rw [hform]
  apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ)^2)).2
  nlinarith

theorem modularDiagonal_lt_one (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ d ∈ Finset.Ico 2 (n + 1), |a d| ≤ 1) :
    modularDiagonal n a < 1 :=
  lt_of_le_of_lt (modularDiagonal_le_count_mass n a ha) (count_mass_lt_one n hn)

/-- Positivity of the complete square controls only the lower signed-pair side. -/
theorem modularSignedPair_ge_neg_half (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ d ∈ Finset.Ico 2 (n + 1), |a d| ≤ 1) :
    -(1 / 2 : ℝ) ≤ modularSignedPair n a := by
  have hpos := modularQuadratic_nonneg n a
  have hsplit := modularQuadratic_eq_diagonal_add_pair n a
  have hdiag := modularDiagonal_lt_one n hn a ha
  nlinarith

theorem residual_square_le_twice_trial (n : ℕ) (u : ℕ → ℝ) :
    windowEnergy n (fun j => 1 - u j) ≤
      2 * windowEnergy n u + 2 * windowMass n := by
  unfold windowEnergy windowMass
  calc
    _ ≤ ∑ j ∈ Finset.Ico n (n * n),
        (2 * (positiveWeight j * (u j)^2) + 2 * positiveWeight j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hsq : (1 - u j)^2 ≤ 2 * (u j)^2 + 2 := by
        nlinarith [sq_nonneg (u j + 1)]
      have hh := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg j)
      nlinarith [hh]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem trial_square_le_twice_residual (n : ℕ) (u : ℕ → ℝ) :
    windowEnergy n u ≤
      2 * windowEnergy n (fun j => 1 - u j) + 2 * windowMass n := by
  unfold windowEnergy windowMass
  calc
    _ ≤ ∑ j ∈ Finset.Ico n (n * n),
        (2 * (positiveWeight j * (1 - u j)^2) + 2 * positiveWeight j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hsq : (u j)^2 ≤ 2 * (1 - u j)^2 + 2 := by
        nlinarith [sq_nonneg (u j - 2)]
      have hh := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg j)
      nlinarith [hh]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- With the actual window mass at most one, logarithmic budgets differ by
only an absolute multiplicative constant. -/
theorem residual_one_add_le_three_trial (n : ℕ) (u : ℕ → ℝ)
    (hm : windowMass n ≤ 1) :
    1 + windowEnergy n (fun j => 1 - u j) ≤
      3 * (1 + windowEnergy n u) := by
  have hh := residual_square_le_twice_trial n u
  have hp := windowEnergy_nonneg n u
  nlinarith

theorem trial_one_add_le_three_residual (n : ℕ) (u : ℕ → ℝ)
    (hm : windowMass n ≤ 1) :
    1 + windowEnergy n u ≤
      3 * (1 + windowEnergy n (fun j => 1 - u j)) := by
  have hh := trial_square_le_twice_residual n u
  have hp := windowEnergy_nonneg n (fun j => 1 - u j)
  nlinarith

/-- The complete signed-pair identity and the already bounded diagonal
give the one-sided residual growth envelope used in Section 24. -/
theorem residual_one_add_le_five_positivePair
    (C B I X m : ℝ) (hCB : C ≤ 2 * B + 2 * m)
    (hB : B = I + 2 * X) (hI : I ≤ 1) (hm : m ≤ 1) :
    1 + C ≤ 5 * (1 + max X 0) := by
  have hx := le_max_left X 0
  have hx0 := le_max_right X 0
  nlinarith



theorem windowMass_le_one (n : ℕ) (hn : 2 ≤ n) : windowMass n ≤ 1 := by
  have hc : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n - 1 by omega)
  have hm := windowMass_nonneg n
  have hp : windowMass n ≤ ((n - 1 : ℕ) : ℝ) * windowMass n := by nlinarith
  exact hp.trans (count_mass_lt_one n hn).le

/-- Exact residual/trial comparison; the complete signed linear term remains. -/
theorem residual_window_exact (n : ℕ) (u : ℕ → ℝ) :
    windowEnergy n (fun j => 1-u j) = windowEnergy n u + windowMass n -
      2 * ∑ j ∈ Finset.Ico n (n*n), positiveWeight j * u j := by
  unfold windowEnergy windowMass
  calc
    _ = ∑ j ∈ Finset.Ico n (n*n), (positiveWeight j * (u j)^2 +
        positiveWeight j - 2*(positiveWeight j*u j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]


theorem window_linear_sq_le (n : ℕ) (u : ℕ → ℝ) :
    (∑ j ∈ Finset.Ico n (n*n), positiveWeight j * u j)^2 ≤
      windowEnergy n u * windowMass n := by
  unfold windowEnergy windowMass
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Ico n (n*n)) ?_ ?_ ?_
  · intro j hj
    exact mul_nonneg (positiveWeight_nonneg j) (sq_nonneg _)
  · intro j hj
    exact positiveWeight_nonneg j
  · intro j hj
    exact le_of_eq (by ring)

theorem sqrt_residual_le_sqrt_trial_add (n : ℕ) (u : ℕ → ℝ) :
    Real.sqrt (windowEnergy n (fun j => 1-u j)) ≤
      Real.sqrt (windowEnergy n u) + Real.sqrt (windowMass n) := by
  let B := windowEnergy n u
  let C := windowEnergy n (fun j => 1-u j)
  let m := windowMass n
  let D := ∑ j ∈ Finset.Ico n (n*n), positiveWeight j * u j
  have hB : 0 ≤ B := windowEnergy_nonneg n u
  have hC : 0 ≤ C := windowEnergy_nonneg n (fun j => 1-u j)
  have hm : 0 ≤ m := windowMass_nonneg n
  have heq : C = B + m - 2*D := residual_window_exact n u
  have hDsq : D^2 ≤ (Real.sqrt B * Real.sqrt m)^2 := by
    simpa only [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hm] using
      (window_linear_sq_le n u)
  have hDabs : |D| ≤ Real.sqrt B * Real.sqrt m :=
    abs_le_of_sq_le_sq hDsq (mul_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg m))
  have hDlow := (abs_le.mp hDabs).1
  have hsq : (Real.sqrt C)^2 ≤ (Real.sqrt B + Real.sqrt m)^2 := by
    rw [Real.sq_sqrt hC]
    nlinarith [Real.sq_sqrt hB, Real.sq_sqrt hm]
  exact le_of_sq_le_sq hsq
    (add_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg m))

/-- The sharp physical L² comparison of complete finite trial and residual windows. -/
theorem abs_sqrt_residual_sub_sqrt_trial_le (n : ℕ) (u : ℕ → ℝ) :
    |Real.sqrt (windowEnergy n (fun j => 1-u j)) -
      Real.sqrt (windowEnergy n u)| ≤ Real.sqrt (windowMass n) := by
  have hforward := sqrt_residual_le_sqrt_trial_add n u
  have hreverse := sqrt_residual_le_sqrt_trial_add n (fun j => 1-u j)
  have hinvol : (fun j => 1-(1-u j)) = u := by funext j; ring
  rw [hinvol] at hreverse
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem farEnergy_le_sq_of_tail_bound (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) (A : ℝ)
    (htail : ∀ j, n * n ≤ j → |hilbertSequence f j| ≤ A * (n : ℝ)) :
    farEnergy n (hilbertSequence f) ≤ A^2 := by
  have hs := (summable_nat_add_iff (n * n)).mpr
    (hilbertSequence_square_summable f)
  have hw := (summable_nat_add_iff (n * n)).mpr positiveWeight_summable
  have hb (k : ℕ) :
      positiveWeight (k + n * n) * (hilbertSequence f (k + n * n))^2 ≤
        positiveWeight (k + n * n) * (A * (n : ℝ))^2 := by
    apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
    have hh := abs_le.mp (htail (k + n * n) (by omega))
    have hp :
        0 ≤ (A * (n : ℝ) - hilbertSequence f (k + n * n)) *
          (A * (n : ℝ) + hilbertSequence f (k + n * n)) :=
      mul_nonneg (by linarith [hh.2]) (by linarith [hh.1])
    nlinarith [hp]
  unfold farEnergy
  calc
    _ ≤ ∑' k : ℕ, positiveWeight (k + n * n) * (A * (n : ℝ))^2 :=
      hs.tsum_le_tsum hb (hw.mul_right _)
    _ = (1 / ((n * n : ℕ) : ℝ)) * (A * (n : ℝ))^2 := by
      rw [tsum_mul_right,
        positiveWeight_tail_tsum (n * n) (Nat.mul_pos hn hn)]
    _ = A^2 := by
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      push_cast
      field_simp


end RiemannResearch.RH.Pareto.FiniteWindow
