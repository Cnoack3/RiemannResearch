# Canonical full-Pareto projection and Schur recursion

Source: the user's full-Pareto projection formulas, 22 September 2026.
The formulas below concern the complete infinite norm.

Let
\[
H=\left\{f:\mathbb N_{\ge1}\to\mathbb R:
 \sum_{k=1}^{\infty}\frac{f(k)^2}{k(k+1)}<\infty\right\},
\qquad
\langle f,h\rangle_P=\sum_{k=1}^{\infty}\frac{f(k)h(k)}{k(k+1)}.
\]
Set \(g_d(k)=(k\bmod d)/d\), for \(d\ge2\), and
\[
V_N=\operatorname{span}\{g_2,\ldots,g_N\},\quad
G_N(d,e)=\langle g_d,g_e\rangle_P,\quad
b_{N,d}=\langle\mathbf1,g_d\rangle_P=\frac{\log d}{d}.
\]
Here \(V_N\) is a subspace; \(P_{V_N}\) is its orthogonal projection.

The generators are linearly independent, so \(G_N\) is positive definite.
Define \(c_N=G_N^{-1}b_N\) and \(F_N=\sum_{d=2}^N c_{N,d}g_d\).
Then
\[
F_N=P_{V_N}\mathbf1,\qquad
Q_N=b_N^TG_N^{-1}b_N=\|F_N\|_P^2,\qquad
\|\mathbf1-F_N\|_P^2=1-Q_N.
\]
For every vector \(x\),
\[
\left\|\mathbf1-\sum_{d=2}^N x_dg_d\right\|_P^2
=1-Q_N+
 \left\|\sum_{d=2}^N(x_d-c_{N,d})g_d\right\|_P^2.
\]
The last term is nonnegative and vanishes exactly when \(x=c_N\).
Thus these coefficients are the unique minimizer.

## Exact Gram entries

For \(L=\operatorname{lcm}(d,e)\),
\[
G_N(d,e)=\frac1{deL}
 \sum_{r=1}^{L-1}(r\bmod d)(r\bmod e)
 \left[\psi\!\left(\frac{r+1}{L}\right)
       -\psi\!\left(\frac rL\right)\right].
\]
This exact formula is already proved in
`ResidueGramDigamma.lean` as
`normalizedResidueHilbert_inner_digamma`.
Lean uses the real part of `Complex.digamma` at positive real arguments.
Its sum uses representatives \(1,\ldots,L\); the final term is zero,
so it is the same formula as the displayed \(1,\ldots,L-1\) sum.

## Exact adjoining-generator recursion

For \(N\ge3\), put
\[
a_N=(\langle g_d,g_N\rangle_P)_{2\le d<N},\quad
\gamma_N=\|g_N\|_P^2,\quad \beta_N=\frac{\log N}{N},
\quad z_N=G_{N-1}^{-1}a_N.
\]
Define
\[
v_N=g_N-\sum_{d=2}^{N-1}(z_N)_dg_d,\quad
\sigma_N=\gamma_N-a_N^Tz_N=\|v_N\|_P^2>0,
\quad
\eta_N=\beta_N-a_N^Tc_{N-1}=\langle v_N,\mathbf1\rangle_P.
\]
Then
\[
F_N=F_{N-1}+\frac{\eta_N}{\sigma_N}v_N,
\quad
c_{N,N}=\frac{\eta_N}{\sigma_N},
\quad
c_{N,d}=c_{N-1,d}-(z_N)_d\frac{\eta_N}{\sigma_N}
\quad(2\le d<N),
\]
and
\[
Q_N=Q_{N-1}+\frac{\eta_N^2}{\sigma_N}.
\]

The Lean proof identifies \(v_N\) with the positive scale of the
corresponding normalized Gram--Schmidt mode. Orthogonality then gives
the projection and energy recursions, and the continuous biorthogonal
coefficient functionals give the coefficient recursions.

## Möbius decomposition

For \(\mu_N=(\mu(2),\ldots,\mu(N))^T\),
\[
c_N=-\mu_N+G_N^{-1}(b_N+G_N\mu_N).
\]
This is already proved in `ResidueGramMobiusCorrection.lean` as
`canonical_mobius_decomposition`. The more general
`canonical_decomposition` works for every reference vector.
This algebraic identity does not assert that its correction tends to zero.

## Lean declarations and indexing

Import `RiemannResearch.RH.ResidueProjectionSchur`.
The new namespace is
`RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur`.
The existing inverse-Gram definitions live in the sibling namespace
`GramMobiusCorrection`.

| Manuscript quantity | Lean expression |
|---|---|
| \(g_d\) | `residueAtom (d - 2)`, for \(d\ge2\) |
| \(V_N\) | `finiteSpace (N - 1)` |
| \(G_N,b_N,c_N\) | `fullGram (N - 1)`, `source (N - 1)`, `canonicalVector (N - 1)` |
| \(F_N,Q_N\) | `projection (N - 1)`, `captured (N - 1)` |
| \(a_N,z_N,v_N\) | `coupling (N - 2)`, `eliminated (N - 2)`, `innovation (N - 2)` |
| \(\sigma_N,\eta_N\) | `schurSigma (N - 2)`, `schurEta (N - 2)` |

- `canonical_completion`, `canonical_minimizes`, `canonical_unique`:
  complete infinite-norm minimization and uniqueness.
- `error_eq_one_sub_captured`, `captured_eq_norm_sq`: exact error and captured energy.
- `sigma_eq_gram_schur`, `eta_eq_gram_schur`, `sigma_pos`: exact Schur data and strict positivity.
- `projection_schur_step`: projection recursion.
- `canonicalVector_schur_new`, `canonicalVector_schur_old`: inverse-Gram coefficient recursions.
- `captured_schur_step`: captured-energy recursion.
- `canonicalVector_one`, `projection_one`, `captured_one`, `energy_one`:
  the exact \(N=2\) values \(c_{2,2}=2\), \(F_2=2g_2\),
  \(Q_2=\log2\), and error squared \(1-\log2\).

## Numerical table

The following are rounded approximations. They were independently checked
with 90-digit `mpmath.digamma` arithmetic and a separate Decimal/Bernoulli
calculation. They are not claimed as Lean-certified decimal enclosures.

| \(N\) | \((c_{N,2},\ldots,c_{N,N})\) | Squared error |
|---|---|---|
| 2 | \((2)\) | 0.306852819440055 |
| 3 | \((1.156761354152,\ 1.374504779326)\) | 0.095747783927754 |
| 4 | \((0.863557838300,\ 1.061174769177,\ 0.710254401874)\) | 0.065951694215570 |
| 5 | \((0.863484830738,\ 0.867808283396,\ 0.298051940786,\ 0.755941136085)\) | 0.036319017938187 |

All new theorems are finite-stage identities. No convergence-to-zero or RH
hypothesis is needed for them, and no unconditional RH conclusion is asserted.
