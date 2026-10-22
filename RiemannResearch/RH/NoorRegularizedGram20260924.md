# Exact arithmetic matrices for finite shifted lifts

**Date:** September 24, 2026
**Foundation:** commit 7bdd872844c1a6c3589d1df0ef4d35e05ffe6bca.
**Status:** Exact finite inverse-matrix minimizers and the shifted arithmetic Gram kernel are proved. The divided-energy rate remains open. No unconditional proof of RH is claimed.

## 1. Actual finite arithmetic problem

At stage \(N\), index the residue generators by \(d=2,\ldots,N+1\), and put
\[
u_d=Tg_d,\quad U_N=\operatorname{span}\{u_2,\ldots,u_{N+1}\},
\quad a_N=T(\mathbf1-P_{V_N}\mathbf1),\quad E_N=\|a_N\|^2.
\]
Here \(T\) is the existing real linear isometric Hardy-coordinate equivalence,
\(S\) is the unilateral right shift, and \(D=I-S\).
All inner products below are the complete infinite Hilbert inner products.

Define
\[
G_N(d,e)=\langle u_d,u_e\rangle,\qquad
K_N(d,e)=\langle Du_d,Du_e\rangle,\qquad
h_N(d)=\langle Du_d,a_N\rangle,\qquad
A_N(t)=K_N+t^2G_N.
\]
For \(t>0\), the verified positive-definiteness theorem supplies
\[
x_N(t)=A_N(t)^{-1}h_N,\qquad
v_N(t)=\sum_{d=2}^{N+1}x_N(t)_d u_d.
\]
These are **lift coefficients**, distinct from the coefficients of the
original unshifted projection.

The actual finite normal equations are proved:
\[
\langle Dv_N(t)-a_N,Dw\rangle+t^2\langle v_N(t),w\rangle=0
\qquad(w\in U_N).
\]
Consequently,
\[
\boxed{
J_N(t)=\|Dv_N(t)-a_N\|^2+t^2\|v_N(t)\|^2
      =E_N-h_N^{\mathsf T}A_N(t)^{-1}h_N.
}
\]
The lift is the unique minimizer in \(U_N\). Matrix invertibility and
the normal equations are discharged from the proved independence of the
actual residue family and \(t>0\). The empty stage \(N=0\) is included.

This is an explicit mathematical specification by finite matrix inversion.
Lean definitions remain noncomputable over the reals; no numerical algorithm,
effective cutoff, or uniform conditioning estimate is asserted.

## 2. Exact shifted arithmetic Gram kernel

Let
\[
Z_2=\sum_{n=1}^{\infty}\frac1{n^2}.
\]
The Lean sum starts at zero, with its zeroth term zero by totalized division.
For positive integers \(k,l\), the existing logarithmic vectors satisfy
\[
L_k(0)=0,\qquad
L_k(n)=\begin{cases}k/n,&k\mid n,\ n\ge1,\\0,&\text{otherwise.}\end{cases}
\]
Their product is supported on multiples of \(L=\operatorname{lcm}(k,l)\).
Reindexing the convergent inner-product sum proves the new identity
\[
\langle L_k,L_l\rangle=\frac{kl}{L^2}Z_2.
\]
At \(n=Lm\) the product is exactly \(kl/(L^2m^2)\).

The existing arithmetic decomposition is
\[
d\,Du_d=-(\log d)e_0+L_1-L_d.
\]
Each \(L_k\) is orthogonal to \(e_0\). Expanding every signed cross term gives
the newly verified formula
\[
\boxed{
K_N(d,e)=
\frac{\log d\,\log e+
 Z_2\left(1-\frac1d-\frac1e+
                 \frac{de}{\operatorname{lcm}(d,e)^2}\right)}
 {de}.
}
\]
It holds for every \(d,e\ge2\). There is no omitted tail or error term.
The unshifted \(G_N\) remains the actual Pareto Gram matrix, and \(h_N\)
still uses the actual projection residual. Neither is replaced with
uniform CRT weights.

## 3. Canonical unconditional convergence

For every prescribed positive schedule \(t_N\to0\), the explicit lifts satisfy
\[
\|Dv_N(t_N)-a_N\|^2+t_N^2\|v_N(t_N)\|^2\longrightarrow0.
\]
This named theorem follows from exact attainment and the previously
verified all-cutoff unscaled convergence theorem.

The earlier existential selection of minimizers is therefore replaced by a
canonical coefficient formula. This does not provide a rate relative to \(t_N\).

## 4. Precise remaining arithmetic estimate

Set \(\Gamma_N(t)=h_N^{\mathsf T}(K_N+t^2G_N)^{-1}h_N\).
The prior shifted-lift obstruction gives the new finite matrix bound
\[
\boxed{\Gamma_N(t)\le\frac{E_N}{1+t}\qquad(t>0).}
\]
This is the existing rate obstruction in exact matrix form.

The remaining target is a cofinal \(N_j\to\infty\) and positive \(t_j\to0\) with
\[
\boxed{
\frac{E_{N_j}-
 h_{N_j}^{\mathsf T}(K_{N_j}+t_j^2G_{N_j})^{-1}h_{N_j}}{t_j}
 \longrightarrow0.
}
\]
The theorem `riemannHypothesis_of_inverseGram_gap` proves that this
condition implies Mathlib's `RiemannHypothesis`. Its explicit `hrate`
hypothesis remains unproved.

Finite invertibility, positivity, uniqueness, the lcm kernel, and
unscaled convergence do not establish this cancellation rate. The lower bound
\[
\frac{E_N}{1+t}\le\frac{E_N-\Gamma_N(t)}t
\]
still applies. Since \(E_N\to\|r\|_P^2\), a nonzero limiting residual
obstructs vanishing divided energy along every positive vanishing schedule
and cofinal cutoffs. Choosing parameters using unscaled convergence alone
does not close the gap.

The next substantive arithmetic step is to control the actual source
through the growing inverse of \(K_N+t^2G_N\) accurately enough to prove
the boxed limit. The lcm formula now supplies the shifted kernel exactly;
the actual unshifted Gram and source alignment must still be controlled.

## 5. Lean interfaces and verification

New modules:

- `RiemannResearch/Analysis/ShiftedLiftGram.lean`
- `RiemannResearch/Analysis/NoorLogarithmGram.lean`
- `RiemannResearch/RH/NoorRegularizedGram.lean`

General namespace `RiemannResearch.Analysis.ShiftedLift`:
`regularizedGram_posDef`, `regularizedCoefficients_normal`,
`regularizedInf_eq_inverseGram`.

Logarithmic namespace `RiemannResearch.Analysis.Noor`: `logVector_inner`.

Arithmetic namespace `RiemannResearch.RH.Pareto.Noor`:

- `shiftedResidue_inner`, `finiteShiftedGram_entry`
- `finiteLiftFamily_linearIndependent`, `finiteRegularizedGram_posDef`
- `finiteMinimum_eq_inverseGram`
- `finiteMinimizer_mem`, `finiteMinimizer_normal`, `finiteMinimizer_energy`
- `finiteMinimizer_unique`, `finiteMinimizer_energy_tendsto_zero`
- `finiteInverseGain_le`
- `riemannHypothesis_of_inverseGram_gap`

Import `RiemannResearch.RH.NoorRegularizedGram` for the complete application.

The complete candidate group passed with exit code 0 and no warnings.
Axiom inspection of the exact kernel, inverse-Gram identity, canonical
convergence, uniqueness, gain bound, and RH reduction reports only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`,
project-local axiom, or unsafe declaration is introduced.
This axiom report does not discharge the explicit `hrate` hypothesis.

Provenance: these are elementary deductions from the user's handoff and the
inspected repository modules. The existing density input is attributed in
`NoorShiftedResidueDensity` to S. Waleed Noor, “A Hardy space analysis of the
Baez-Duarte criterion for the RH,” Theorem 9,
https://arxiv.org/abs/1809.09577. That source supports the earlier density
input, not the open rate. No mathematical novelty is claimed.
