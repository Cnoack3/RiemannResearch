# Actual physical source limits and the complete signed correction

Date: 2026-10-08 UTC. Continuation of `PhysicalArithmeticObservations20261008.md`.

The actual primorial physical sources satisfy, unconditionally,

\[
 A_n\longrightarrow0,\qquad B_n\longrightarrow-2\pi,\qquad
 T_n\longrightarrow0,\qquad
 \frac{(2\pi+B_n)^2}{-A_n}\longrightarrow0.
\]

These discharge the previously open actual source-limit providers. The scalar
projection charge is also identified with the actual inverse-Gram projection.
Its limit is

\[
 Q_n\longrightarrow \frac{4\pi}{-C_\infty}.
\]

The charge limit exists but remains unidentified. **This does not prove
`C_infinity = -4*pi` or RH.** The RH-to-squarefree analytic approximation
provider remains a separate formalization task.

## 1. The actual physical system

Use the Pareto Hilbert norm

\[
 \|f\|_P^2=\sum_{k\ge1}\frac{|f(k)|^2}{k(k+1)}.
\]

For a legal conductor `q>1`, let the unnormalized Ramanujan packet be

\[
 \tau_q(k)=\sum_{d\mid q}\mu(q/d)(k\bmod d).
\]

For a finite legal packet set `s` containing an odd prime, set

\[
 \Gamma_s(q,r)=\langle\tau_q,\tau_r\rangle_P,\quad
 \lambda_q=\Lambda(q),\quad\varphi_q=\phi(q).
\]

The complete physical Gram identity, established earlier, is

\[
 \Gamma_s=\pi F_s+
 \tfrac12(\lambda\varphi^{\mathsf T}+\varphi\lambda^{\mathsf T}).
\]

The actual core is nonsingular, while the actual Gram is positive definite.
Define

\[
 A_s=\lambda^{\mathsf T}F_s^{-1}\lambda<0,\quad
 B_s=\lambda^{\mathsf T}F_s^{-1}\varphi,\quad
 C_s=\varphi^{\mathsf T}F_s^{-1}\varphi<0,
\]

\[
 D_s=2\pi+B_s,\quad T_s=A_sC_s-D_s^2>0,
 \quad\alpha_s=-A_s>0,\quad\gamma_s=-C_s>0.
\]

All these are actual full-tail physical quantities. The ordinary period mean
of a synthesis with coefficients `c` is `phi^T c / 2`; its Pareto pairing
with one is `lambda^T c`. These two means are distinct.

## 2. Complete finite projection and ordinary-mean dual

Put `v=F_s^{-1} lambda`, `w=F_s^{-1} phi`. The new module
`PhysicalSourceProjection.lean` proves the explicit normal equations

\[
 \widehat c_s=\frac2{T_s}(A_sw-D_sv),
 \qquad \Gamma_s\widehat c_s=\lambda,
\]

\[
 y_s=\frac2{T_s}(C_sv-D_sw),
 \qquad \Gamma_sy_s=\varphi.
\]

No supplied inverse or normal-equation hypothesis is used. In particular,
`projection_eq_actual_gramSolve` identifies `c_hat` with the existing Gram
solve obtained from actual packet independence. Consequently,

\[
 Q_s=\lambda^{\mathsf T}\Gamma_s^{-1}\lambda
     =\frac{4\pi\alpha_s}{T_s},\qquad 0<Q_s\le1.
\]

For **every** coefficient vector `c`, the complete error is

\[
 E_s(c)=1-Q_s+
 (c-\widehat c_s)^{\mathsf T}\Gamma_s(c-\widehat c_s).
\]

The final square has not been dropped. It identifies the physical optimum
and implies the key control `4*pi*alpha_s <= T_s`.

The ordinary-mean dual gives

\[
 \varphi^{\mathsf T}\Gamma_s^{-1}\varphi
 =\frac{4\pi\gamma_s}{T_s},
 \qquad
 (\varphi^{\mathsf T}c)^2
 \le\frac{4\pi\gamma_s}{T_s}\,c^{\mathsf T}\Gamma_sc.
\]

The previously proved ordinary mean-one optimum `E_s^0=1+4*pi/C_s`
and the unconstrained projection have the exact difference

\[
 E_s^0-(1-Q_s)=\frac{4\pi D_s^2}{\gamma_sT_s}.
\]

This keeps the full source square with its genuine finite denominators.

## 3. Large prime packets force the source determinant to zero

For a prime `p` in `s`, `tau_p(k)=k mod p`. The existing covariance-corrected
complete atom norm, rather than a uniform residue replacement, proves

\[
 \|\tau_p\|_P^2<\frac{4p}{3},\qquad\phi(p)=p-1.
\]

Apply the ordinary-mean dual inequality to the single prime packet. It gives

\[
 (p-1)^2\le\frac{4\pi\gamma_s}{T_s}\|\tau_p\|_P^2,
\]

and therefore the actual finite estimates

\[
 0<T_s<\frac{16\pi\gamma_s p}{3(p-1)^2}
          \le\frac{64\pi\gamma_s}{3p}.
\]

The complete covariance identity is retained in its owning module; its
checked upper bound is used only at this final estimation step.

For the primorial chain

\[
 L_n=\operatorname{primorial}(n+3),\qquad
 s_n=\{q>1:q\mid L_n\},
\]

every fixed prime eventually belongs to `s_n`. Conductor-six monotonicity
gives `gamma_n <= 8*sqrt(3)` at every stage. Euclid's unbounded primes and
the displayed inverse-prime bound now force `T_n -> 0`. The more general
checked theorem needs only legal packet sets with odd primes, a uniform
charge bound, and eventual inclusion of every prime; nesting is unnecessary
for this particular determinant limit.

Since `0<alpha_n <= T_n/(4*pi)`, this proves `A_n -> 0`. Finally,

\[
 0\le D_n^2<\alpha_n\gamma_n
 \le8\sqrt3\,\alpha_n\longrightarrow0,
\]

so `B_n -> -2*pi`. These limits use no RH hypothesis, zeta-zero assumption,
small-damping estimate, Dirichlet-sum estimate or proposed optimizer-tail saving.

## 4. The normalized signed square also vanishes

The actual charge converges unconditionally to `C_infinity`. The earlier
complete signed Schur coupling can now use the actual providers proved above,
rather than unproved `A` and `B` limit assumptions. For each stage it yields

\[
 \boxed{\quad
 0\le R_n:=\frac{D_n^2}{\alpha_n}
 \le C_\infty-C_n.
 \quad}
\]

The right side tends to zero. Thus the stronger ratio limit `R_n -> 0`
follows; it is not inferred merely from `A_n -> 0` and `D_n -> 0`.

The exact corrected-charge identity is

\[
 \gamma_n-R_n=\frac{4\pi}{Q_n}.
\]

It now proves

\[
 \gamma_n-R_n\longrightarrow-C_\infty,\qquad
 Q_n\longrightarrow\frac{4\pi}{-C_\infty}.
\]

The complete signed correction is quantitatively controlled by the **remaining
charge gap**, which is distinct from the gap to the RH endpoint.

## 5. Verification and independent computational checks

Two new modules contain **38 theorems and 6 definitions**. Their complete
bodies pass one coherent Lean check. A compact transitive audit checks every
one of the 44 public declarations and rejects any axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. The manifest records exact source hashes,
verification job and result. Publication additionally validates actual module
imports and affected project dependents through the standard checkpoint.

Wolfram independently checked both two-source normal equations and pairings,
returning zero for each symbolic difference. It also evaluated the original
complete double-divisor cotangent core at three stages:

| L | A_L | C_L | Q_L | D_L^2/(-A_L) |
|---:|---:|---:|---:|---:|
| 6 | -2.354968536 | -13.856406461 | 0.921706746 | 0.222600840 |
| 30 | -0.455285435 | -13.055771335 | 0.962516175 | 0.0000212763 |
| 210 | -0.064897153 | -12.894343208 | 0.974566027 | 0.0000186980 |

These are numerical checks, not formal certificates or proofs of a limit.
The calculations are not used by any Lean theorem.

Principal checked declarations:

- `PhysicalSourceProjection.projection_error_decomposition`
- `PhysicalSourceProjection.projectionCharge_eq_actual_inverse_gram`
- `PhysicalSourceProjection.meanOne_projection_error_gap`
- `PhysicalSourceLimits.determinant_prime_bound`
- `PhysicalSourceLimits.primorial_logarithmicCharge_tendsto_zero`
- `PhysicalSourceLimits.primorial_mixedCharge_tendsto_neg_two_pi`
- `PhysicalSourceLimits.primorial_signedCorrection_le_charge_gap`
- `PhysicalSourceLimits.primorial_signedCorrection_tendsto_zero`
- `PhysicalSourceLimits.primorial_projectionCharge_tendsto`
- `PhysicalSourceLimits.exists_primorial_complete_source_limits`

## 6. What remains and the next research target

The earlier improved interval remains valid:

\[
 -\frac{43200}{797\sqrt3+1224\cot(\pi/5)+648\cot(2\pi/5)}
 \le C_\infty\le-4\pi.
\]

This advance removes the actual source-limit realization obligation and the
previously missing physical projection identification. It still does not
force the interval's upper endpoint.

1. **Open arithmetic target:** prove `C_infinity=-4*pi`, or equivalently
   construct actual mean-one squarefree stage packets with arbitrarily small
   complete error. The existing checked implication then yields RH.
2. **Open analytic formalization:** prove `RiemannHypothesis ->
   SquarefreeCenteredApproximation` in Lean. Bagchi's squarefree argument
   supplies a paper strategy, but its RH-controlled Dirichlet partial-sum
   estimate, Mellin domination and small-damping step are not discharged here.
3. Focus further unconditional work on the actual accumulated totient-source
   Schur gains. From conductor six, endpoint saturation requires their total
   gain to equal `8*sqrt(3)-4*pi`. Source limits and vanishing `R_n` now serve
   as established inputs, rather than additional research assumptions.

The unrelated minimum-transcendence corollary still retains its explicit
pi-transcendence premise. The invalid coarse stretched-scale optimizer-tail
estimate remains excluded.

Sources: user-directed recovery continuation; the repository's exact physical
core, covariance and signed Schur providers. For the remaining analytic reverse
strategy, Bhaskar Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis*, [arXiv:math/0607733](https://arxiv.org/abs/math/0607733),
Theorem 2, Lemma 3 and Remark 4. That paper is a source for the unfinished
analytic strategy, not an assumed theorem in the new unconditional proofs.
