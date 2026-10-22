# Actual optimizer limits and quantitative endpoint obstruction

Follow-up: `PhysicalSourceVerificationAdvance20261008.md` adds exact signed
mean repair and quantitative source bounds, verifies the combined declarations,
and discharges the optional pi-transcendence premise. The original verification
record below is retained as a historical snapshot.

The actual source limits published at `efc020d` now give complete physical
agreement of the ordinary mean-one optimizer and the unconstrained projection.
This advance identifies both limiting errors exactly. It does **not** prove
that the common error is zero, and it does **not** prove RH.

## 1. Exact finite agreement identity

Use the actual full Pareto inner product

\[
\langle f,g\rangle_P=\sum_{k\ge1}\frac{f(k)g(k)}{k(k+1)}.
\]

For every finite legal packet set with an odd prime, retain the existing
physical charges and full shifted determinant:

\[
\alpha=-A>0,\quad\gamma=-C>0,\quad D=2\pi+B,
\quad T=\alpha\gamma-D^2>0,
\quad Q=\frac{4\pi\alpha}{T},\quad R=\frac{D^2}{\alpha}.
\]

Let `c0` be the actual ordinary mean-one optimizer, `chat` the actual full
Gram projection coefficient vector, and `f0`, `fhat` their synthesized physical
packet functions. The complete projection identity is

\[
E(c)=1-Q+(c-\widehat c)^T\Gamma(c-\widehat c).
\]

The new physical specialization proves the exact equality

\[
\boxed{
\|f^0-\widehat f\|_P^2
=(c^0-\widehat c)^T\Gamma(c^0-\widehat c)
=E(c^0)-E(\widehat c)
=\frac{4\pi D^2}{\gamma T}
=\frac{RQ}{\gamma}.}
\]

Every cross term remains in the actual Gram square. The signed source enters
through its entire square; no term is silently removed.

## 2. Unconditional physical optimizer limits

For the established primorial packet chain, an actual charge limit
`C_infinity` exists in the certified interval. The earlier improved bound
remains available:

\[
-\frac{43200}{797\sqrt3+1224\cot(\pi/5)+648\cot(2\pi/5)}
\le C_\infty\le-4\pi.
\]

The new declarations prove

\[
E(f_n^0)\longrightarrow 1+\frac{4\pi}{C_\infty},\qquad
E(\widehat f_n)\longrightarrow 1+\frac{4\pi}{C_\infty},
\]

and consequently

\[
\|f_n^0-\widehat f_n\|_P^2\longrightarrow0.
\]

For every fixed site `k`, including the anchored zero site,

\[
f_n^0(k)-\widehat f_n(k)\longrightarrow0.
\]

The pointwise proof uses positive physical coordinate masses and a bound for
each finite synthesis separately. It requires no uniform coefficient bound.
Pointwise agreement does not assert that either family tends to one.
`exists_primorial_complete_optimizer_limits` supplies the charge limit, its
negative sign, both error limits, complete norm agreement and pointwise
agreement without an RH or endpoint hypothesis.

## 3. Exact remaining saturation assertion

The following equivalences are checked:

\[
Q_n\to1
\quad\Longleftrightarrow\quad C_\infty=-4\pi
\quad\Longleftrightarrow\quad E(\widehat f_n)\to0
\quad\Longleftrightarrow\quad E(f_n^0)\to0.
\]

Combining the established physical/arithmetic identification with the existing
squarefree stage equivalences also proves

\[
Q_n\to1
\quad\Longleftrightarrow\quad
\texttt{SquarefreeCenteredApproximation}.
\]

Thus actual inverse-Gram projection saturation implies Mathlib's
`RiemannHypothesis`. This is a **conditional research reduction**: the
saturation premise remains **Open**. The equivalence supplies neither side.
No analytic RH-to-squarefree reverse is used in this forward implication.

## 4. Quantitative actual zeta-zero obstruction

The repository already proves exact Mellin annihilation of the actual legal
Hilbert closure at a hypothetical zeta zero `rho` with `Re rho > 1/2` and
`rho != 1`. The Mellin evaluation of the residual remains `1/rho`.
Its continuous evaluation bound yields

\[
\delta_\rho:=\frac{2\Re\rho-1}{|\rho|^2}>0.
\]

The new module transfers this actual Hilbert theorem to every legal physical
packet synthesis, then retains the complete finite corrections:

\[
\delta_\rho+(c-\widehat c)^T\Gamma(c-\widehat c)\le E(c),
\]

\[
\delta_\rho+\frac{4\pi D^2}{\gamma T}\le E(c^0).
\]

Passing to the actual projection limit proves

\[
0<\delta_\rho\le1-\frac{4\pi}{-C_\infty}<1,
\]

and the quantitative separation

\[
\boxed{C_\infty\le-\frac{4\pi}{1-\delta_\rho}<-4\pi.}
\]

These are implications from a hypothetical right-hand zero. They assert no
such zero exists, and they give no positive floor at a critical-line zero.
They identify why cancellation of `A`, `B`, `T` and `R` leaves the endpoint
problem: the actual Mellin obstruction still acts on the common residual.

## 5. Verification and completion status

`RH/PhysicalOptimizerLimits.lean` adds 13 theorems.
`RH/PhysicalZeroObstruction.lean` adds 9 theorems and one definition.
The final verification manifest records the coherent full-body check,
transitive axiom audit of all 23 public declarations and exact source hashes.
Publication separately validates actual imports and affected dependents
through the standard checkpoint. The allowed axiom set is `propext`,
`Classical.choice`, and `Quot.sound`.

Established: actual optimizer agreement, both exact physical error limits,
the projection/centered-squarefree saturation equivalence, and the quantitative
physical charge obstruction at every hypothetical right-hand zeta zero.

Open: an unconditional provider for `C_infinity=-4*pi`, equivalently complete
squarefree approximation or `Q_n -> 1`. The separate Lean formalization of
`RiemannHypothesis -> SquarefreeCenteredApproximation` and the explicit
pi-transcendence premise also remain unresolved. The invalid coarse stretched
optimizer-tail saving remains excluded.

The completed work is this exact physical optimizer and obstruction advance.
Completing the RH proof still requires a new argument that supplies the
arithmetic endpoint; the established source limits alone do not provide it.

Sources: the repository's complete physical Gram, signed Schur coupling,
legal Mellin separation, and squarefree stage providers. For the classical
squarefree approximation strategy, see Bagchi, *On Nyman, Beurling and
Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*,
[arXiv:math/0607733](https://arxiv.org/abs/math/0607733), Theorem 2 and Remark 4.
The paper is context for the unfinished reverse strategy, not an assumed
provider in these new proofs.
