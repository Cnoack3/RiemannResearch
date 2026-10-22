import RiemannResearch.RH.DilationWaveletAlgebra

/-!
# The actual bounded primitive of the binary dilation wavelet

Source: user-provided argument `analytic_wavelet_foothold.md`, §4.
The primitive is evaluated on integer endpoints; its forward difference
is the original binary wavelet at every integer. No variation bound is
assumed in these declarations.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def binaryWaveletPrimitiveNat (m k : ℕ) : ℕ :=
  let r := k % (4*m)
  if r < m then 0 else if r < 2*m then r-m else if r < 3*m then 3*m-r else 0

def binaryWaveletPrimitive (m k : ℕ) : ℝ := binaryWaveletPrimitiveNat m k

theorem binaryWaveletPrimitive_bounds (m : ℕ) (_hm : 0 < m) (k : ℕ) :
    0 ≤ binaryWaveletPrimitive m k ∧ binaryWaveletPrimitive m k ≤ m := by
  constructor
  · exact Nat.cast_nonneg _
  · have h : binaryWaveletPrimitiveNat m k ≤ m := by
      dsimp only [binaryWaveletPrimitiveNat]
      split_ifs <;> omega
    unfold binaryWaveletPrimitive
    exact_mod_cast h

@[simp] theorem binaryWaveletPrimitive_zero (m : ℕ) :
    binaryWaveletPrimitive m 0 = 0 := by
  by_cases hm : m = 0
  · simp [hm, binaryWaveletPrimitive, binaryWaveletPrimitiveNat]
  · have hp : 0 < m := Nat.pos_of_ne_zero hm
    simp [binaryWaveletPrimitive, binaryWaveletPrimitiveNat, hp]

theorem dilationWaveletSequence_two_pullback (m k : ℕ) :
    dilationWaveletSequence 2 m k = dilationWaveletSequence 2 1 (k/m) := by
  simp [dilationWaveletSequence, digitSequence, Nat.div_div_eq_div_mul,
    Nat.mul_comm m 2]

private theorem binaryWavelet_mod_period (m : ℕ) (hm : 0 < m) (k : ℕ) :
    dilationWaveletSequence 2 m k = dilationWaveletSequence 2 m (k%(4*m)) := by
  have he1 : k = k%(4*m) + m*(4*(k/(4*m))) := by
    calc
      k = k%(4*m) + (4*m)*(k/(4*m)) := (Nat.mod_add_div _ _).symm
      _ = _ := by ring
  have he2 : k = k%(4*m) + (2*m)*(2*(k/(4*m))) := by
    calc
      k = k%(4*m) + (4*m)*(k/(4*m)) := (Nat.mod_add_div _ _).symm
      _ = _ := by ring
  have h1 : k/m%2 = (k%(4*m))/m%2 := by
    conv_lhs => rw [he1]
    rw [Nat.add_mul_div_left _ _ hm]
    simp [Nat.add_mod, Nat.mul_mod]
  have h2 : k/(2*m)%2 = (k%(4*m))/(2*m)%2 := by
    conv_lhs => rw [he2]
    rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2*m)]
    simp [Nat.add_mod]
  simp only [dilationWaveletSequence, Pi.sub_apply, digitSequence, h1, h2]

private theorem binaryWavelet_on_period (m r : ℕ) (_hm : 0 < m) (hr : r < 4*m) :
    dilationWaveletSequence 2 m r =
      if r < m then 0 else if r < 2*m then 1 else if r < 3*m then -1 else 0 := by
  by_cases h1 : r < m
  · have hd1 : r/m = 0 := Nat.div_eq_of_lt h1
    have hd2 : r/(2*m) = 0 := Nat.div_eq_of_lt (by omega)
    simp [dilationWaveletSequence, digitSequence, h1, hd1, hd2]
  · by_cases h2 : r < 2*m
    · have hd1 : r/m = 1 := by apply Nat.div_eq_of_lt_le <;> omega
      have hd2 : r/(2*m) = 0 := Nat.div_eq_of_lt h2
      simp [dilationWaveletSequence, digitSequence, h1, h2, hd1, hd2]
    · by_cases h3 : r < 3*m
      · have hd1 : r/m = 2 := by apply Nat.div_eq_of_lt_le <;> omega
        have hd2 : r/(2*m) = 1 := by apply Nat.div_eq_of_lt_le <;> omega
        simp [dilationWaveletSequence, digitSequence, h1, h2, h3, hd1, hd2]
      · have hd1 : r/m = 3 := by apply Nat.div_eq_of_lt_le <;> omega
        have hd2 : r/(2*m) = 1 := by apply Nat.div_eq_of_lt_le <;> omega
        simp [dilationWaveletSequence, digitSequence, h1, h2, h3, hd1, hd2]

theorem binaryWaveletPrimitive_step (m : ℕ) (hm : 0 < m) (k : ℕ) :
    binaryWaveletPrimitive m (k+1) - binaryWaveletPrimitive m k =
      dilationWaveletSequence 2 m k := by
  let r := k%(4*m)
  have hr : r < 4*m := Nat.mod_lt _ (by omega)
  have hmod : (k+1)%(4*m) = (r+1)%(4*m) := by
    simp only [r, Nat.add_mod, Nat.mod_mod]
  rw [binaryWavelet_mod_period m hm k, binaryWavelet_on_period m r hm hr]
  by_cases hlast : r+1 = 4*m
  · have hstep : (binaryWaveletPrimitiveNat m (k+1) : ℤ) -
        (binaryWaveletPrimitiveNat m k : ℤ) = 0 := by
      unfold binaryWaveletPrimitiveNat
      rw [hmod, hlast, Nat.mod_self]
      change (↑(if 0 < m then 0 else if 0 < 2*m then 0-m else
        if 0 < 3*m then 3*m-0 else 0) : ℤ) -
        ↑(if r < m then 0 else if r < 2*m then r-m else
          if r < 3*m then 3*m-r else 0) = 0
      split_ifs <;> omega
    have hv : (if r < m then 0 else if r < 2*m then 1 else
        if r < 3*m then -1 else (0 : ℝ)) = 0 := by
      have h1 : ¬ r < m := by omega
      have h2 : ¬ r < 2*m := by omega
      have h3 : ¬ r < 3*m := by omega
      simp only [if_neg h1, if_neg h2, if_neg h3]
    rw [hv]
    unfold binaryWaveletPrimitive
    exact_mod_cast hstep
  · have hr1 : r+1 < 4*m := by omega
    have hstep : (binaryWaveletPrimitiveNat m (k+1) : ℤ) -
        (binaryWaveletPrimitiveNat m k : ℤ) =
        if r < m then 0 else if r < 2*m then 1 else if r < 3*m then -1 else 0 := by
      unfold binaryWaveletPrimitiveNat
      rw [hmod, Nat.mod_eq_of_lt hr1]
      change (↑(if r+1 < m then 0 else if r+1 < 2*m then r+1-m else
        if r+1 < 3*m then 3*m-(r+1) else 0) : ℤ) -
        ↑(if r < m then 0 else if r < 2*m then r-m else
          if r < 3*m then 3*m-r else 0) = _
      split_ifs <;> omega
    unfold binaryWaveletPrimitive
    have hR := congrArg (fun z : ℤ => (z : ℝ)) hstep
    push_cast at hR
    exact hR

/-- The explicit triangle is exactly the prefix sum of the original wavelet. -/
theorem binaryWaveletPrimitive_eq_sum (m : ℕ) (hm : 0 < m) (N : ℕ) :
    binaryWaveletPrimitive m N =
      ∑ k ∈ Finset.range N, dilationWaveletSequence 2 m k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h := binaryWaveletPrimitive_step m hm N
    linarith

end
end RiemannResearch.RH.Pareto
