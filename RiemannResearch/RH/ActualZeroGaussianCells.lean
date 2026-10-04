import RiemannResearch.Analysis.GaussianCellGeometry
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Complete marked Gaussian matrices for actual zeta-zero copies

Every actual zero in (T,2T] has one index for each analytic multiplicity copy.
Different zeros with equal imaginary parts are retained. The unconditional
bound is by the actual square occupancy budget. Its eventual O(M) estimate is
the separate Tsang input and is deliberately an explicit hypothesis below.
-/
noncomputable section
open Complex Zeta23
open scoped BigOperators Classical ComplexConjugate

namespace RiemannResearch.RH.ActualZeroGaussianCells
open RiemannResearch.Analysis
open GaussianCellGeometry

/-- Occurrences in the positive-height dyadic shell, including all multiplicity copies. -/
abbrev ShellCopies (T : ℝ) :=
  {c : ActualZeroOrdinate.Copies (2 * T) // T < c.1.val.im}

/-- The actual ordinate attached to a copy; this map need not be injective. -/
def ordinate {T : ℝ} (c : ShellCopies T) : ℝ := c.val.1.val.im

/-- A marked phase of the actual ordinate. -/
def mark {T : ℝ} (u : ℝ) (c : ShellCopies T) : ℂ :=
  Complex.exp (Complex.I * (u * ordinate c : ℝ))

theorem mark_norm {T : ℝ} (u : ℝ) (c : ShellCopies T) : ‖mark u c‖ = 1 := by
  rw [mark, Complex.norm_exp]
  simp

/-- The phase retains the one-sided mark and the separate frequency centre. -/
theorem marked_phase_identity {T : ℝ} (u v : ℝ) (i j : ShellCopies T) :
    mark (u + v) i * conj (mark v j) =
      Complex.exp (Complex.I *
        (u * ordinate i + v * (ordinate i - ordinate j) : ℝ)) := by
  unfold mark
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- The complete finite Gaussian matrix, including its full self-copy diagonal. -/
def markedPair (T scale u v : ℝ) : ℂ :=
  ∑ i : ShellCopies T, ∑ j : ShellCopies T,
    (Real.exp (-Real.pi ^ 2 * (scale * ordinate i - scale * ordinate j) ^ 2) : ℂ) *
      mark (u + v) i * conj (mark v j)

/-- The actual microscopic cells occupied by the copies. -/
def cells (T scale : ℝ) : Finset ℤ :=
  Finset.univ.image (fun i : ShellCopies T => Int.floor (scale * ordinate i))

/-- Cell occupancy counts all occurrences, rather than distinct heights. -/
def cellOccupancy (T scale : ℝ) (a : ℤ) : ℝ :=
  occupancy (Finset.univ : Finset (ShellCopies T))
    (fun i => Int.floor (scale * ordinate i)) a

/-- The actual cluster-square budget; its uniform normalized bound is not assumed implicitly. -/
def squareBudget (T scale : ℝ) : ℝ := ∑ a ∈ cells T scale, cellOccupancy T scale a ^ 2

/-- An unconditional actual marked zero-copy Gaussian matrix bound. -/
theorem markedPair_norm_le (T scale u v : ℝ) :
    ‖markedPair T scale u v‖ ≤ 6 * squareBudget T scale := by
  have hc : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  exact marked_gaussian_pair_norm_le (Finset.univ : Finset (ShellCopies T))
    (fun i => scale * ordinate i) (mark (u + v)) (mark v) hc
    (fun i _ => (mark_norm (u + v) i).le) (fun i _ => (mark_norm v i).le)

/-- Normalization keeps the unresolved actual cluster-square budget visible. -/
theorem normalized_markedPair_norm_le (T scale u v : ℝ) :
    ‖markedPair T scale u v / (Fintype.card (ShellCopies T) : ℂ)‖ ≤
      6 * squareBudget T scale / (Fintype.card (ShellCopies T) : ℝ) := by
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (markedPair_norm_le T scale u v) (Nat.cast_nonneg _)

/-- Conditional uniform normalization consumer. The only number-theoretic
input is the displayed actual square-budget bound; it remains unproved here. -/
theorem normalized_markedPair_norm_le_of_squareBudget (T scale u v C : ℝ)
    (hM : 0 < Fintype.card (ShellCopies T))
    (hbudget : squareBudget T scale ≤ C * (Fintype.card (ShellCopies T) : ℝ)) :
    ‖markedPair T scale u v / (Fintype.card (ShellCopies T) : ℂ)‖ ≤ 6 * C := by
  have hMR : 0 < (Fintype.card (ShellCopies T) : ℝ) := by exact_mod_cast hM
  calc
    _ ≤ 6 * squareBudget T scale / (Fintype.card (ShellCopies T) : ℝ) :=
      normalized_markedPair_norm_le T scale u v
    _ ≤ (6 * (C * (Fintype.card (ShellCopies T) : ℝ))) /
        (Fintype.card (ShellCopies T) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (by norm_num)) hMR.le
    _ = _ := by field_simp


open RiemannResearch.Analysis

/-- The actual distinct zero points supporting the complete shell copies. -/
def shellCutoff (T : ℝ) : Finset ℂ :=
  (ActualZeroOrdinate.cutoff (2 * T)).filter (fun ρ => T < ρ.im)

private def shellCopiesEquiv (T : ℝ) : ShellCopies T ≃
    ((ρ : {z : ℂ // z ∈ shellCutoff T}) × Fin (zeroMult ρ.val)) where
  toFun c := ⟨⟨c.val.1.val, by
    exact Finset.mem_filter.mpr ⟨c.val.1.property, c.property⟩⟩, c.val.2⟩
  invFun c := ⟨⟨⟨c.1.val, (Finset.mem_filter.mp c.1.property).1⟩, c.2⟩,
    (Finset.mem_filter.mp c.1.property).2⟩
  left_inv := by rintro ⟨⟨⟨ρ, hρ⟩, k⟩, hT⟩; rfl
  right_inv := by rintro ⟨⟨ρ, hρ⟩, k⟩; rfl

/-- Copy cardinal counts every analytic multiplicity, including equal heights. -/
theorem card_shellCopies_eq_sum (T : ℝ) :
    Fintype.card (ShellCopies T) = ∑ ρ ∈ shellCutoff T, zeroMult ρ := by
  rw [Fintype.card_congr (shellCopiesEquiv T)]
  simp [Fintype.card_sigma, Finset.sum_attach]

private theorem shellCutoff_eq_zero_window {T : ℝ} (hT : 0 ≤ T) :
    shellCutoff T = (zerosIn_finite T (2 * T)).toFinset := by
  ext ρ
  simp only [shellCutoff, Finset.mem_filter, ActualZeroOrdinate.mem_cutoff,
    Set.Finite.mem_toFinset, zerosIn]
  constructor
  · rintro ⟨⟨hz, h0, h2⟩, hρT⟩
    exact ⟨hz, hρT, h2⟩
  · rintro ⟨hz, hρT, h2⟩
    exact ⟨⟨hz, lt_of_le_of_lt hT hρT, h2⟩, hρT⟩

/-- The actual scalar normalization agrees exactly with N(T,2T]. -/
theorem card_shellCopies_eq_Ncount {T : ℝ} (hT : 0 ≤ T) :
    Fintype.card (ShellCopies T) = Ncount T (2 * T) := by
  rw [card_shellCopies_eq_sum, Ncount,
    finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite T (2 * T)),
    ← shellCutoff_eq_zero_window hT]


end RiemannResearch.RH.ActualZeroGaussianCells
