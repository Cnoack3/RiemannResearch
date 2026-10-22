# Canonical Q/P affine minima and optimizer stability — 15 October 2026

Source: continuation of the user's `QCanonicalCofinalGramResearch20261015.md`.
The proof uses exact finite Gram completion, the actual Q/P physical-sequence
equivalence, and the existing unconditional normalized-energy provider.
No novelty claim is made.

## The actual finite minimization problem

Write \(z=\zeta(2)\), \(P(k)=1/[k(k+1)]\), and \(Q(k)=1/(zk^2)\).
For positive physical coordinates, \(g_d(k)=(k\bmod d)/d\).
The canonical approximant includes its complete boundary term:
\[
 S_N=\sum_{d=1}^{N}\frac{\mu(d)}d,\qquad
 F_N=-\sum_{d=1}^{N}\mu(d)g_d+(N+1)S_Ng_{N+1},\qquad r_N=1-F_N.
\]

For \(1\le N\le M\), consider
\[
 \mathcal A_{N,M}=
 \left\{\sum_{k=N}^{M}a_kr_k:\ \sum_{k=N}^{M}a_k=1\right\}.
\]
Every such residual vanishes at physical coordinates \(1,\ldots,N\).
Let \(x_P,x_Q\) minimize its complete P and Q energies respectively.
Each symbol denotes the same physical sequence under either encoding.

The residual families are linearly independent. The existing
`canonicalWindowResidual_linearIndependent` transfers through
`toPareto`, proving `windowFamily_linearIndependent`.
In particular, with
\[
 G_Q(i,j)=\langle r_{N+i},r_{N+j}\rangle_Q,
\]
the all-ones source represents the affine coefficient-sum constraint.
The actual normal vector, normalized minimizing coefficients, and energy are
\[
 u_Q=G_Q^{-1}\mathbf1,\qquad
 a_Q=\frac{u_Q}{\mathbf1^{\mathsf T}u_Q},\qquad
 D_Q=\|x_Q\|_Q^2=
   \bigl(\mathbf1^{\mathsf T}G_Q^{-1}\mathbf1\bigr)^{-1}.
\]
`normalQ` and `normalQ_normal` construct the inverse normal solution;
`normalQ_mass_pos` proves its positive mass.
`optimalResidual_completion` retains the exact complete remainder for
every affine competitor. `optimalResidual_minimum_iff` proves uniqueness
of the actual coefficients. No invertibility or stationarity provider is assumed.

The existing P normal solution is `canonicalWindowNormal`.
`paretoOptimalResidual` reencodes its minimizing physical residual with Q weights.

## Exact identities

Put \(e=x_Q-x_P\), \(D_P=\|x_P\|_P^2\), and
\[
 R(f)=z\|f\|_Q^2-\|f\|_P^2
     =\sum_{k\ge1}\frac{|f(k)|^2}{k^2(k+1)}.
\]
The two complete Pythagorean identities are
\[
 \|x_Q\|_P^2=\|x_P\|_P^2+\|e\|_P^2,\qquad
 \|x_P\|_Q^2=\|x_Q\|_Q^2+\|e\|_Q^2.
\]
Retaining the change-of-measure correction for all three vectors gives
\[
 \boxed{R(x_P)=R(x_Q)+2\|e\|_P^2+R(e).}
\]
The exact minimum-energy gap is
\[
 \boxed{zD_Q-D_P=R(x_Q)+\|e\|_P^2.}
\]
The generic declarations are `pareto_completion`, `q_completion`,
`correction_balance`, and `minimum_energy_gap_identity` in
`QParetoAffineMinimum`. The canonical specialization is
`QCanonicalWindowMinimum.optimizer_correction_balance`.

## Stronger displacement bound

The exact completions and the polarized correction identity imply
\[
 R(e,x_P)=-\|e\|_P^2-R(e).
\]
The existing reciprocal mixed estimate therefore yields
\[
 (\|e\|_P^2+R(e))^2
 \le \frac{\|e\|_P^2R(x_P)}{N+1}.
\]
Positivity, including the zero-displacement case, gives
\[
 \boxed{\|e\|_P^2\le\frac{R(x_P)}{N+1}
                    \le\frac{D_P}{(N+1)^2}.}
\]
These are `displacement_sq_le_correction` and
`displacement_sq_le_pareto_energy`.
No coefficient norm bound is assumed. The generic result allows any
nonempty finite family with the stated normal equations and common zero head.
The canonical application constructs both normal solutions.

## Unconditional bounds uniform in the upper cutoff

The single residual \(r_N\) is an admissible affine competitor, so
\[
 D_P(N,M)\le\|r_N\|_P^2.
\]
Write \(\delta_N=\|r_N\|_P^2/(N+1)\).
The existing checked PNT-based provider proves \(\delta_N\to0\).
Simultaneously for every \(M\ge N\ge1\),
\[
 \boxed{
 0\le zD_Q(N,M)-D_P(N,M)
 \le R(x_P)\le\delta_N,\qquad
 \|x_Q-x_P\|_P^2\le\frac{\delta_N}{N+1}.
 }
\]
The exact correction balance also gives \(R(x_Q)\le\delta_N\).
For two independently selected windows,
\[
 |R(x_Q(N,M),x_Q(K,L))|^2\le\delta_N\delta_K.
\]
Here the signed mixed correction is exactly
\(z\langle f,g\rangle_Q-\langle f,g\rangle_P\).

Consequently, for arbitrary \(N_j\to\infty\) and \(M_j\ge N_j\),
\[
 zD_Q(N_j,M_j)-D_P(N_j,M_j)\to0,\qquad
 x_Q(N_j,M_j)-x_P(N_j,M_j)\to0
\]
strongly in both Q and P. The quantitative bound also implies
\((N_j+1)\|x_Q-x_P\|_P^2\to0\).
The dimension \(M_j-N_j+1\) may grow without restriction.

The canonical declarations are `paretoOptimalResidual_energy_le`,
`paretoOptimalResidual_correction_le`, `optimalResidual_correction_le`,
`optimized_gram_correction_sq_le`, `optimized_energy_gap_bounds`,
`optimizer_displacement_sq_le`,
`cofinal_optimized_energy_gap_tendsto_zero`, and
`cofinal_optimizer_displacement_tendsto_zero`.
The last theorem directly proves Q strong convergence; the checked
`tendsto_toPareto_iff` equivalence supplies the P conclusion.
The scaled squared-displacement limit is an immediate consequence of the
displayed quantitative inequality and \(\delta_N\to0\).

No bounded-l1, bounded-l2, or bounded-full-energy hypothesis is used.
No convergence of the raw coefficient arrays is asserted.

## Precise RH consumer and remaining arithmetic obligation

`riemannHypothesis_of_bounded_optimized_energy` proves the conditional implication
\[
 \left[
  M(j)\ge j+1,\quad
  \sup_j D_Q(j+1,M(j))<\infty
 \right]\Longrightarrow\mathrm{RH}.
\]
The proof supplies the actual P minimizing legal candidates, complete
energies, membership in the closed legal residue span, and exact growing heads.
The new minimum comparison supplies the P-energy bound. The existing
exact-head Mellin/closure consumer gives RH.

The inverse-Gram form is `riemannHypothesis_of_normalQ_mass_lower`:
\[
 \boxed{
 \left[
 \exists c>0,\ \forall j,\quad
 c\le\mathbf1^{\mathsf T}G_Q(j+1,M(j))^{-1}\mathbf1
 \right]\Longrightarrow\mathrm{RH},
 \qquad M(j)\ge j+1.
 }
\]
The same positive constant must work for every growing head.
Finite positivity of each normal mass is already proved; this uniform
lower bound remains **Open**.

The new metric results control the difference of the two optimized energies.
They do not bound their common leading energy or prove RH.
The canonical application treats the full legal family. The generic
comparison also applies to restricted squarefree families when its explicit
finite-family hypotheses are supplied.

## Files and verification

- `RiemannResearch/RH/QParetoAffineMinimum.lean`
- `RiemannResearch/RH/QCanonicalWindowMinimum.lean`
- Both modules are exported by `RiemannResearch.lean`.

There are 31 theorem declarations and five definitions.

The initial general-module server check succeeded in job
`job_cR_33NeaUU2-AGjC7JI2lpLy6YHgV7HS` (287.337 seconds).
The final assembled source and eight representative axiom checks passed in
job `job_MOdupcShnV99JTvNGZa5gYrzfSo6x92C` (709.860 seconds, exit code 0).
Every audited declaration reported only `propext`, `Classical.choice`, and
`Quot.sound`. The printed inverse-Gram RH theorem retains the common positive
lower bound explicitly as its substantive arithmetic hypothesis.

The final project checkpoint performs the aggregate/export validation and
publication gate after these module checks. Its terminal job and published
commit are reported with the completed delivery.
