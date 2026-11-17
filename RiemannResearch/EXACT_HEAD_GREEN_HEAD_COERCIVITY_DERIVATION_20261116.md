# The centered-probe head already measures square-root Mobius cancellation

Date: 16 November 2026.

**Status:** paper derivation, not a Lean-checked asymptotic theorem. The exact
head lower bound used below is formalized in `RH/ExactHeadMomentHeadObstruction.lean`.
Formalizing the uniform asymptotic comparisons is a new, separate obligation.
No uniform centered-probe bound, Mertens bound, or RH conclusion is established.

## Claim and consequence

Write

\[
 m(x)=\sum_{d\le x}\frac{\mu(d)}d,\qquad
 z(x)=\frac{M(x)}x,\qquad M(x)=\sum_{d\le x}\mu(d),\qquad
 H_x=\sum_{r\le x}\frac{\psi_x(r)^2}{r(r+1)}.
\]

The derivation gives absolute constants `0<c_*<=C_*` and `x_0` such that

\[
 c_* x\bigl(m(x)^2+z(x)^2\bigr)
 \le H_x\le C_*x\bigl(m(x)^2+z(x)^2\bigr)\qquad(x\ge x_0).
\]

Consequently a **global eventual** bounded centered-probe energy would force
`M(x)=O(sqrt(x))` and `m(x)=O(x^(-1/2))`. A bound only on a cofinal set forces
these estimates only on that same set. These are logically different targets.
This does not refute the cofinal R5 proposal, and it does not prove either bound.
It does show why removing upper-span components need not make uniform R5 easy.

## Arithmetic input

Put `c=6/pi^2=1/zeta(2)`. Use only the classical unconditional estimate

\[
 Q(y)=\sum_{d\le y}\mu(d)^2=cy+O(\sqrt y).
\]

A primary source recording this estimate and its elementary square-divisor
identity is J. Pawlewicz, *Counting Square-Free Numbers* (2011), introduction
and Theorem 1, [author manuscript](https://arxiv.org/abs/1107.4890).
This source supports the counting input, not the new probe conclusion.
Partial summation gives, uniformly for real `y>=2`,

\[
 W(y)=\sum_{d\le y}\frac{\mu(d)^2}{d}=c\log y+O(1),\qquad
 B(y)=\sum_{d\le y}d\mu(d)^2=\frac c2 y^2+O(y^{3/2}).
\]

Define two elementary floor sums

\[
 F_0(r)=\sum_{d\le r}\mu(d)^2\lfloor r/d\rfloor,
 \qquad F_1(r)=\sum_{d\le r}d\mu(d)^2\lfloor r/d\rfloor.
\]

Then `F_0(r)=rW(r)+O(Q(r))=cr log r+O(r)`. Also, by exchanging finite sums,

\[
 F_1(r)=\sum_{k\le r} B(r/k)
 =\frac c2 r^2\sum_{k\le r}k^{-2}
    +O\!\left(r^{3/2}\sum_{k\le r}k^{-3/2}\right)
 =\frac12r^2+O(r^{3/2}).
\]

The coefficient `1/2` is essential: `c*zeta(2)=1`.

## The probe is a two-dimensional observer

Let `(a_0,a_1)` be the squarefree-weighted affine fit to the Mobius vector.
With the handoff's `W,V,U,Delta`, its normal equations give exactly

\[
 a_0=\frac{Um-Vz}{\Delta},\qquad
 a_1=\frac{Wz-Vm}{\Delta},\qquad \Delta=WU-V^2.
\]

Here `V=Q(x)/x=c+O(x^(-1/2))` and
`U=B(x)/x^2=c/2+O(x^(-1/2))`. Thus

\[
 ca_0\log x=m-2z+O((|m|+|z|)/\log x),\qquad
 a_1=2z/c+O((|m|+|z|)/\log x).
\]

These error estimates are **linear and uniform in the two actual moments**;
no cancellation bound for either moment is used.
The affine-dual definition and `mu(d)^3=mu(d)` show, for `r<=x`,

\[
 \psi_x(r)=a_0F_0(r)+(a_1/x)F_1(r).
\]

For `t=r/x` in `[1/2,1]`, the preceding arithmetic estimates therefore yield

\[
 \frac{\psi_x(r)}r
 =m+(t/c-2)z+O((|m|+|z|)/\log x),
\]

uniformly throughout this half of the head.

## Positive limiting matrix

After dividing the energy of this half-head by x, its quadratic-form matrix
converges to

\[
 G=\int_{1/2}^1
 \begin{pmatrix}1\\t/c-2\end{pmatrix}
 \begin{pmatrix}1&t/c-2\end{pmatrix}dt.
\]

The Riemann sum has an additional factor `r/(r+1)=1+O(1/x)` on this interval,
which does not affect the limit. Exactly,

\[
 G=\begin{pmatrix}
 1/2&-1+\pi^2/16\\
 -1+\pi^2/16&2-\pi^2/4+7\pi^4/864
 \end{pmatrix},\qquad
 \det G=\pi^4/6912>0.
\]

Its trace is positive, so its smallest eigenvalue is positive. Equivalently,
the two real functions `1` and `t/c-2` are linearly independent on the interval.
Matrix convergence then gives a fixed positive lower bound for all large x.
This proves the displayed lower comparison with `x(m^2+z^2)`.

For the upper comparison on the **entire** head, use
`F_0(r)<=C r log(2r)`, `F_1(r)<=C r^2`,
`|a_0|<=C(|m|+|z|)/log x`, and `|a_1|<=C(|m|+|z|)`.
They give `|psi_x(r)|/r<=C(|m|+|z|)` for every `1<=r<=x`.
Summing `psi_x(r)^2/[r(r+1)]` gives the required upper bound.

## Formalization acceptance criteria

1. Formalize the exact observer/floor-sum identity for the actual dual probe.
2. Supply the unconditional squarefree counting and two summatory estimates.
3. Prove the uniform two-dimensional matrix convergence, retaining error terms.
4. Derive eventual coercivity with some explicit positive constant, or an
   existential constant with a complete proof.
5. Only then promote the asymptotic comparison from paper derivation to Lean.

The matrix and determinant were independently checked with Wolfram. That
symbolic check is supporting evidence, not a substitute for steps 1-4.
