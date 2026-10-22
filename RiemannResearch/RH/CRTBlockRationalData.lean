/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Kernel-computed rational data for the CRT block {5,7}

All statements are finite rational computations checked by the kernel. The
connection to real Cesaro energies is made in `CRTBlockSymmetryCertificate`.
There is no floating-point or native-decide certificate.
-/
namespace RiemannResearch.RH.CRTBlock.Certificate
open scoped BigOperators

def residueMeanQ (d t : ℕ) : ℚ :=
  (((t / d : ℕ) : ℚ) * ((d : ℚ) - 1) / 2 +
    ((t % d : ℕ) : ℚ) * (((t % d : ℕ) : ℚ) + 1) / (2 * (d : ℚ))) / (t : ℚ)

def mixtureQ (t : ℕ) : ℚ := 2 / (((t : ℚ) + 1) * ((t : ℚ) + 2))

def baseQ (t : ℕ) : ℚ :=
  residueMeanQ 2 t + residueMeanQ 3 t - residueMeanQ 6 t +
    (5 * residueMeanQ 5 t + 7 * residueMeanQ 7 t - 35 * residueMeanQ 35 t) / 3

def directionQ (t : ℕ) : ℚ :=
  -5 * residueMeanQ 5 t - 7 * residueMeanQ 7 t + 70 * residueMeanQ 35 t

def candidateQ (t : ℕ) : ℚ :=
  residueMeanQ 2 t + residueMeanQ 3 t - residueMeanQ 6 t +
    (31 / 6) * residueMeanQ 5 t - (14 / 3) * residueMeanQ 7 t -
      (7 / 6) * residueMeanQ 35 t

def prefixAux (u v : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | M + 1 => prefixAux u v M + mixtureQ (M+1) * u (M+1) * v (M+1)

def prefixQ (u v : ℕ → ℚ) : ℚ := prefixAux u v 100

theorem prefixAux_eq_sum (u v : ℕ → ℚ) (M : ℕ) :
    prefixAux u v M = ∑ k ∈ Finset.range M, mixtureQ (k+1) * u (k+1) * v (k+1) := by
  induction M with
  | zero => simp [prefixAux]
  | succ M ih => simp only [prefixAux, Finset.sum_range_succ, ih]

def aa : ℚ := prefixQ baseQ baseQ
def bb : ℚ := prefixQ baseQ directionQ
def cc : ℚ := prefixQ directionQ directionQ
def ee : ℚ := prefixQ candidateQ candidateQ

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem finite_rational_certificates :
    0 < cc ∧ (4 / 5 : ℚ) < aa - bb^2 / cc ∧ ee < (69 / 100 : ℚ) ∧
      candidateQ 210 = -(1 / 3 : ℚ) ∧
      ∀ r : Fin 210, |(r.val : ℚ) * (candidateQ r.val + 1 / 3)| ≤ (25 / 3 : ℚ) := by
  decide +kernel

end RiemannResearch.RH.CRTBlock.Certificate
