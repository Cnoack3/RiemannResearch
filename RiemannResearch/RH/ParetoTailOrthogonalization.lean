import RiemannResearch.RH.ParetoRepairCovariance

/-!
# Tail orthogonalization preserves arithmetic head constraints

Source: repair of the covariance suggestion in the user-provided
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §8.

The finite covariance calculation can use reverse orthogonal elimination
in place of the false normalized Bessel claim. This module supplies its full-Pareto
one-step construction. Earlier coordinates are preserved by subtracting only
directions whose heads vanish beyond the current anchor. A nonzero anchor
gives a strictly positive pivot, so the recursion cannot divide by zero.

All norm identities retain the full infinite covariance and its exact Schur
term. These results do not prove that the binary repair span is dense; its
previously proved composite invariant remains an obstruction.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Eliminate the full covariance of `f` against one later direction `g`. -/
def tailOrthogonalize (f g : ℕ → ℝ) (k : ℕ) : ℝ :=
  f k - (paretoInner f g / paretoInner g g) * g k

theorem tailOrthogonalize_bounded {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) :
    ∀ k, |tailOrthogonalize f g k| ≤
      C + |paretoInner f g / paretoInner g g| * D :=
  bounded_sub hf (bounded_const_mul hg _)

/-- The complete squared norm dominates each actual positive-coordinate mass. -/
theorem paretoInner_coordinate_square_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (k : ℕ) :
    positiveWeight k * (f k)^2 ≤ paretoInner f f := by
  have hs := weighted_summable_of_bounded (bounded_product hf hf)
  have h := hs.sum_le_tsum ({k} : Finset ℕ)
    (fun j _ => mul_nonneg (positiveWeight_nonneg j) (mul_self_nonneg _))
  simpa only [Finset.sum_singleton, paretoInner, pow_two] using h

/-- A preserved nonzero arithmetic anchor certifies a nondegenerate Gram pivot. -/
theorem paretoInner_pos_of_anchor {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (p : ℕ) (hp : 0 < p) (hfp : f p ≠ 0) :
    0 < paretoInner f f := by
  have hw : 0 < positiveWeight p := by
    unfold positiveWeight
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  exact lt_of_lt_of_le (mul_pos hw (sq_pos_of_ne_zero hfp))
    (paretoInner_coordinate_square_le hf p)

/-- Later directions have zero values on the entire earlier head, including its
new anchor. Elimination therefore preserves that head exactly. -/
theorem tailOrthogonalize_preserves_head (f g : ℕ → ℝ) (p : ℕ)
    (hghead : ∀ k ≤ p, g k = 0) :
    ∀ k ≤ p, tailOrthogonalize f g k = f k := by
  intro k hk
  simp [tailOrthogonalize, hghead k hk]

theorem tailOrthogonalize_orthogonal {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hgg : paretoInner g g ≠ 0) :
    paretoInner (tailOrthogonalize f g) g = 0 := by
  unfold tailOrthogonalize
  rw [paretoInner_sub_left hf (bounded_const_mul hg _) hg,
    paretoInner_const_mul_left hg hg, div_mul_cancel₀ _ hgg, sub_self]

/-- Elimination against a direction orthogonal to `h` preserves an already
achieved orthogonality to `h`. This is the induction step for reverse Gram--Schmidt. -/
theorem tailOrthogonalize_preserves_orthogonal {f g h : ℕ → ℝ} {C D E : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D) (hh : ∀ k, |h k| ≤ E)
    (hfh : paretoInner f h = 0) (hgh : paretoInner g h = 0) :
    paretoInner (tailOrthogonalize f g) h = 0 := by
  unfold tailOrthogonalize
  rw [paretoInner_sub_left hf (bounded_const_mul hg _) hh,
    paretoInner_const_mul_left hg hh, hfh, hgh]
  ring

/-- Exact full-Pareto Schur identity. No covariance or tail is discarded. -/
theorem tailOrthogonalize_norm {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hgg : paretoInner g g ≠ 0) :
    paretoInner (tailOrthogonalize f g) (tailOrthogonalize f g) =
      paretoInner f f - (paretoInner f g)^2 / paretoInner g g := by
  unfold tailOrthogonalize
  have h := paretoInner_optimal_scalar_gain hf hg hgg
    (paretoInner f g / paretoInner g g)
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] using h

theorem tailOrthogonalize_energy_split {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hgg : paretoInner g g ≠ 0) :
    paretoInner f f =
      paretoInner (tailOrthogonalize f g) (tailOrthogonalize f g) +
        (paretoInner f g)^2 / paretoInner g g := by
  rw [tailOrthogonalize_norm hf hg hgg]
  ring

theorem tailOrthogonalize_norm_le {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hgg : paretoInner g g ≠ 0) :
    paretoInner (tailOrthogonalize f g) (tailOrthogonalize f g) ≤
      paretoInner f f := by
  rw [tailOrthogonalize_norm hf hg hgg]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (paretoInner_self_nonneg g))

/-- Unit anchors give an explicit lower bound on every reverse Gram pivot. -/
theorem tailOrthogonalize_anchor_lower {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (p : ℕ) (hfp : f p = -1) (hgp : g p = 0) :
    positiveWeight p ≤
      paretoInner (tailOrthogonalize f g) (tailOrthogonalize f g) := by
  have h := paretoInner_coordinate_square_le (tailOrthogonalize_bounded hf hg) p
  simpa [tailOrthogonalize, hfp, hgp] using h

theorem tailOrthogonalize_mean_zero {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hfm : paretoMean f = 0) (hgm : paretoMean g = 0) :
    paretoMean (tailOrthogonalize f g) = 0 := by
  rw [← paretoInner_one_right]
  exact tailOrthogonalize_preserves_orthogonal hf hg
    (show ∀ k : ℕ, |(1 : ℝ)| ≤ 1 by intro k; norm_num)
    (by simpa only [paretoInner_one_right] using hfm)
    (by simpa only [paretoInner_one_right] using hgm)

/-- Every Möbius defect changes by its exact scalar covariance coefficient. -/
theorem tailOrthogonalize_mobiusDifference (f g : ℕ → ℝ) (m : ℕ) :
    mobiusDifference m (tailOrthogonalize f g) =
      mobiusDifference m f - (paretoInner f g / paretoInner g g) *
        mobiusDifference m g := by
  unfold tailOrthogonalize
  rw [mobiusDifference_sub_fn, mobiusDifference_const_mul_fn]

theorem mobiusDifference_zero_of_head (g : ℕ → ℝ) (p : ℕ)
    (hp : 0 < p) (hghead : ∀ k ≤ p, g k = 0) : mobiusDifference p g = 0 := by
  unfold mobiusDifference
  apply Finset.sum_eq_zero
  intro d hd
  have hdle : d ≤ p := Nat.le_of_dvd hp (Nat.dvd_of_mem_divisors hd)
  rw [hghead d hdle, hghead (d-1) (by omega)]
  ring

theorem tailOrthogonalize_preserves_defect (f g : ℕ → ℝ) (p : ℕ)
    (hp : 0 < p) (hghead : ∀ k ≤ p, g k = 0) :
    mobiusDifference p (tailOrthogonalize f g) = mobiusDifference p f := by
  rw [tailOrthogonalize_mobiusDifference,
    mobiusDifference_zero_of_head g p hp hghead, mul_zero, sub_zero]

/-- The exact triangular coefficient transformation retains the original vector. -/
theorem tailOrthogonalize_reconstruct (f g : ℕ → ℝ) (a b : ℝ) (k : ℕ) :
    a * f k + b * g k = a * tailOrthogonalize f g k +
      (b + a * (paretoInner f g / paretoInner g g)) * g k := by
  unfold tailOrthogonalize
  ring

/-- Orthogonal changes of generators preserve the already proved binary
arithmetic obstruction; they cannot create approximation density by themselves. -/
theorem tailOrthogonalize_binary_invariant (f g : ℕ → ℝ) (p : ℕ)
    (hf : binaryRepairInvariant p f = 0) (hg : binaryRepairInvariant p g = 0) :
    binaryRepairInvariant p (tailOrthogonalize f g) = 0 := by
  unfold binaryRepairInvariant at hf hg ⊢
  rw [tailOrthogonalize_mobiusDifference, tailOrthogonalize_mobiusDifference]
  calc
    _ = (mobiusDifference (2*p) f + 2 * mobiusDifference p f) -
        (paretoInner f g / paretoInner g g) *
          (mobiusDifference (2*p) g + 2 * mobiusDifference p g) := by ring
    _ = 0 := by rw [hf, hg]; ring

/-- The new binary repair has the exact unit anchor regardless of the scale gap. -/
theorem arithmeticRepair_binary_anchor (p E : ℕ) (hp : 0 < p) (hpE : p < E) :
    arithmeticRepair 2 p E p = -1 := by
  rw [arithmeticRepair_eq_floor 2 p E p hp]
  simp [Nat.div_eq_of_lt hpE, Nat.div_self hp, residue]

/-- Tail elimination specializes to actual repairs: its old head is zero, its
new value is `-1`, its new defect is `-1`, and its pivot stays strictly positive. -/
theorem arithmeticRepair_tail_elimination {g : ℕ → ℝ} {D : ℝ}
    (hg : ∀ k, |g k| ≤ D) (p E : ℕ) (hp : 1 < p) (hpE : p < E)
    (hghead : ∀ k ≤ p, g k = 0) :
    (∀ k < p, tailOrthogonalize (arithmeticRepair 2 p E) g k = 0) ∧
    tailOrthogonalize (arithmeticRepair 2 p E) g p = -1 ∧
    mobiusDifference p (tailOrthogonalize (arithmeticRepair 2 p E) g) = -1 ∧
    0 < paretoInner (tailOrthogonalize (arithmeticRepair 2 p E) g)
      (tailOrthogonalize (arithmeticRepair 2 p E) g) := by
  have hf : ∀ k, |arithmeticRepair 2 p E k| ≤
      |(p : ℝ)⁻¹| * ((E : ℝ)*2 + (p : ℝ)*2) := by
    intro k
    rw [arithmeticRepair_eq_scaleRepair]
    exact scaleRepair_abs_le (fun j => residue_abs_le 2 j (by norm_num)) p E k
  have hanchor : tailOrthogonalize (arithmeticRepair 2 p E) g p = -1 := by
    rw [tailOrthogonalize_preserves_head _ _ p hghead p le_rfl]
    exact arithmeticRepair_binary_anchor p E (by omega) hpE
  refine ⟨?_, hanchor, ?_, ?_⟩
  · intro k hk
    rw [tailOrthogonalize_preserves_head _ _ p hghead k hk.le]
    exact arithmeticRepair_head_zero 2 p E k (by norm_num) hpE.le hk
  · rw [tailOrthogonalize_preserves_defect _ _ p (by omega) hghead]
    exact arithmeticRepair_new_defect 2 p E hp (by omega) (by omega) (by omega)
  · exact paretoInner_pos_of_anchor (tailOrthogonalize_bounded hf hg) p (by omega)
      (by rw [hanchor]; norm_num)

end
end RiemannResearch.RH.Pareto
