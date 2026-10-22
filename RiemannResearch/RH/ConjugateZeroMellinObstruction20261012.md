# Exact conjugate-zero obstruction in the physical Pareto space

Date: 2026-10-12.

The Riemann Hypothesis is not proved here. The result is a stronger,
fully analytic obstruction to legal approximation, with an exact nonnegative
remainder and no assumed Mellin, continuation, or boundedness provider.

## Statement

Use the actual Hilbert space
\[
\|f\|_P^2=\sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)},
\qquad g_d(n)=\frac{n\bmod d}{d},\quad d\ge2.
\]
Let \(f\) be in the closure of the real linear span of these atoms.
Suppose \(\rho=\beta+i\gamma\) is an actual zeta zero with
\(\beta>1/2\) and \(\gamma\ne0\). Set
\[
a=2\beta-1,\qquad R=\beta^2+\gamma^2,\qquad
q=\frac aR,\qquad B=2q-q^2.
\]
Then
\[
\boxed{\|1-f\|_P^2\ge 2q-q^2>q>0.}
\]
The old single-zero bound was \(\|1-f\|_P^2\ge q\).

More precisely, put
\[
c=\frac a{2R}
  +i\frac{a\,[a(\beta-1)+2\gamma^2]}{2\gamma R},
\qquad
K(x)=c\,x^{-\rho}+\overline c\,x^{-\overline\rho}.
\]
The exact identity is
\[
\boxed{
\|1-f\|_P^2
=B+\int_1^\infty
\left|\frac{1-f(\lfloor x\rfloor)}x-\overline{K(x)}\right|^2dx.
}
\]
The kernel \(K\) is real on the positive axis, so the conjugation in the
remainder may equivalently be omitted. The formal statement retains it
to match the general complex completed-square identity.

Every complete tail and signed Gram cross term is retained.

## Proof

1. The physical step embedding \(U_f(x)=f(\lfloor x\rfloor)/x\) satisfies
   \(\int_1^\infty|U_f(x)|^2dx=\|f\|_P^2\).

2. The actual continuous Mellin functional is
   \(M(f,s)=\int_1^\infty U_f(x)x^{-s}dx\).
   The previously proved atom signature and its continuity give
   \(M(1-f,\rho)=1/\rho\) for the stated actual zero.
   Reality of \(f\) gives
   \(M(1-f,\overline\rho)=\overline{M(1-f,\rho)}
   =1/\overline\rho\). No separate conjugate-zero hypothesis is needed.

3. Direct evaluation of an absolutely convergent integral gives
   \[
   \int_1^\infty x^{-s}\overline{x^{-t}}dx
   =\frac1{s+\overline t-1},
   \qquad \Re s,\Re t>\frac12.
   \]
   Hence, for unrestricted \(c,d\in\mathbb C\),
   \[
   \int_1^\infty|c x^{-s}+d x^{-t}|^2dx
   =\frac{|c|^2}{2\Re s-1}
    +\frac{|d|^2}{2\Re t-1}
    +2\Re\frac{c\overline d}{s+\overline t-1}.
   \]
   In particular, the signed cross term is included exactly.

4. For the displayed coefficient, exact algebra proves both
   \[
   \frac c\rho+\frac{\overline c}{\overline\rho}=B,
   \qquad \int_1^\infty|K(x)|^2dx=B.
   \]

5. Expand the squared norm of \(U_{1-f}-\overline K\), integrate all
   three terms, and use the two exact signatures. The remainder is
   \(\|1-f\|_P^2+B-2B=\|1-f\|_P^2-B\).
   Its nonnegativity proves the bound.

6. Since \(R-a=(\beta-1)^2+\gamma^2>0\), one has \(0<q<1\).
   Therefore \(B-q=q(1-q)>0\).

The kernel calculation also gives an unrestricted exact two-zero variational
identity, implemented as `normalizedResidue_error_twoZero_identity`.
For any actual zeros \(s,t\) in the continuity half-plane, with
\(s,t\ne1\), its lower bound is
\[
\begin{aligned}
\|1-f\|_P^2\ge
&\;2\Re\left(\frac cs+\frac dt\right)
 -\frac{|c|^2}{2\Re s-1}
 -\frac{|d|^2}{2\Re t-1}\\
&\;-2\Re\frac{c\overline d}{s+\overline t-1}.
\end{aligned}
\]
The exact equality adds the squared integral remainder.

## Lean result and scope

The two new modules contain twenty declarations, including seventeen
theorems:

- `RiemannResearch/RH/ParetoMellinTwoKernel.lean`
- `RiemannResearch/RH/ParetoMellinZeroPairObstruction.lean`

Decisive declarations, in namespace `RiemannResearch.RH.Pareto`:

- `normalizedResidue_error_zeroPair_identity`
- `normalizedResidue_error_zeroPair_lower_bound`
- `zeta_ne_zero_of_error_lt_zeroPairCharge`
- `normalizedResidue_error_twoZero_identity`
- `normalizedResidue_error_twoZero_lower_bound`

The coherent server development check
`job_hUW7HoyY-_Bt6Ba8i7ZVT1dAT5bwJmlC` succeeded with exit code 0 and
`verified: true`. The axiom output for the decisive identities and
certificate is exactly `propext`, `Classical.choice`, and `Quot.sound`.
It contains no `sorryAx` or added project research axiom.
The final publication checkpoint separately validates the persisted modules
and any integrated source before pushing.

The conclusions assume only the stated actual zero, actual legal-closure
membership, and ordinary parameter conditions. None assumes RH.

## Finite Wolfram checks

Wolfram symbolically checked
\[
v^*G^{-1}v=2q-q^2,\quad
v=\begin{pmatrix}1/\rho\\1/\overline\rho\end{pmatrix},\quad
G=\begin{pmatrix}
1/a&1/(a+2i\gamma)\\
1/(a-2i\gamma)&1/a
\end{pmatrix}.
\]
Lean independently verified the corresponding coefficient, target, energy,
and infinite integral identities.

The numerical examples below are synthetic parameters, not asserted zeta
zeros:

| \(\beta\) | \(\gamma\) | Single charge \(q\) | Pair charge \(2q-q^2\) |
|---:|---:|---:|---:|
| 0.75 | 14 | 0.00254372019 | 0.00508096987 |
| 0.60 | 100 | 0.0000199992800 | 0.0000399981601 |
| 0.90 | 10 | 0.00793572066 | 0.0158084657 |

## Remaining RH obligation

The new zero-free certificate proves that a legal witness satisfying
\(\|1-f\|_P^2<B(s)\) rules out a zero at that nonreal point \(s\).

It does not supply the needed witnesses uniformly at increasing heights.
In the existing approximation program, the decisive open mathematics
remains proving that the actual legal optimizer errors tend to zero
(or proving the equivalent target-specific arithmetic convergence estimate).
The positive remainder identity sharpens what an off-line zero would force;
it does not establish the vanishing of those errors.

## Provenance

The Mellin/Hardy-space obstruction strategy and finite product charge are
classical. This is a direct formal specialization to the project's physical
Pareto model, with explicit two-kernel coefficients and complete remainders.

- [J.-F. Burnol, A note on Nyman's equivalent formulation of the Riemann Hypothesis,
  arXiv:math/9910055](https://arxiv.org/abs/math/9910055), Theorem 1.2 and Section 2.
- [B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis, arXiv:math/0607733](https://arxiv.org/abs/math/0607733),
  Theorem 1 and Remark 4, for the discrete criterion and squarefree context.
