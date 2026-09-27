# Burnol half-damping endpoint and quantitative arithmetic strengthening

The target is the centered arithmetic/Pareto form of the unconditional
endpoint in J.-F. Burnol, *On an analytic
estimate in the theory of the Riemann zeta function and a theorem of
Báez-Duarte*, Acta Cientifica Venezolana **54** (2003), 210–215,
Lemma 4.1. Author manuscript: https://arxiv.org/abs/math/0202166.
The citation supports the endpoint statement. The formal proof below instead
uses the repository's quantitative prime number theorem, exact finite
arithmetic identities, Abel summation, and a Dirichlet hyperbola decomposition.
No mathematical novelty is claimed.

## Exact result

For positive damping, write

\[
A_\varepsilon(N)=\sum_{1\le d\le N}\mu(d)d^{-\varepsilon}\lfloor N/d\rfloor,
\qquad C_\varepsilon=\operatorname{Re}(1/\zeta(1+\varepsilon)),
\qquad R_\varepsilon(N)=A_\varepsilon(N)-NC_\varepsilon.
\]

`RH/DampedMobiusHalfEndpoint.lean` proves `dampedMobius_half_endpoint`:
there is a real constant K >= 0 such that, for every positive integer N with
log N >= 200,

\[
|R_{1/2}(N)|\le K\frac{\sqrt N}{(6+\log N)^{3/4}},
\qquad
\sum_{N\ge1}\frac{R_{1/2}(N)^2}{N(N+1)}<\infty.
\]

The construction can take K = 2 + 112 B for a constant B in the unconditional
Mertens estimate below. The pointwise estimate strengthens the formalized
qualitative finite-energy statement. It is not asserted to improve the
strongest bounds in the classical literature.

`centered_dampedMobius_square_summable_iff_of_half_le` completes the inclusive
range: for every epsilon >= 1/2 and every real C,

\[
\sum_{N\ge1}\frac{(A_\varepsilon(N)-NC)^2}{N(N+1)}<\infty
\quad\Longleftrightarrow\quad C=C_\varepsilon.
\]

## Arithmetic proof and reusable strengthening

The existing unconditional quantitative PNT supplies
|psi(x)-x| <= D x/(1+log x)^4. The new finite bootstrap keeps every signed
term of the Möbius–von Mangoldt convolution. With M(x) = sum_{d<=x} mu(d),
m(Y) = sum_{d<=Y} mu(d)/d, and Rpsi(x) = psi(x)-x, it proves

\[
M(N)\log N
=\sum_{d\le N}\mu(d)\log(N/d)-Nm(Y)
-\sum_{d\le Y}\mu(d)R_\psi(N/d)
-\sum_{Y<d\le N}\mu(d)\psi(N/d).
\]

The last term is regrouped exactly as
sum_{q<=N/(Y+1)} Lambda(q) (M(N/q)-M(Y)).
The cutoffs Y = floor(N exp(-sqrt(log N))) and J = floor(sqrt(log N))+1
give a half-logarithm improvement over the earlier M(x) log x = O(x) bound:

\[
|M(x)|\le Bx(6+\log x)^{-3/2}\qquad(x\ge1).
\]

The resulting Abel lemmas apply to arbitrary signed real coefficients c(n),
not just mu(n). Under the analogous summatory bound and c(0)=0 they give

\[
\left|\sum_{n\le x}c(n)n^{-1/2}\right|
\le3B\sqrt x(6+\log x)^{-3/2},
\qquad
\left|\sum_{n>y}c(n)n^{-3/2}\right|
\le5B y^{-1/2}(6+\log y)^{-3/2}.
\]

The infinite-tail statement retains summability of the density series as
an explicit hypothesis; the actual Möbius series satisfies it absolutely.
The exact centered hyperbola identity and its estimates also apply to
arbitrary signed weights. Optimizing its cutoff yields the logarithmic
saving 3/4, and the general Pareto energy criterion finishes the proof.
No positivity or multiplicativity assumption on these generic weights is used.

## Limiting theorem with explicit hypotheses

`RH/DampedMobiusEnergyClosure.lean` proves a separate finite-head Fatou theorem.
For damping epsilon_j -> epsilon_0 > 0, it is enough that one constant B bounds
each finite energy head eventually in j. The starting index may depend on the
head length. This is weaker than requiring one threshold for all heads.
The common bound is an explicit premise of the general closure theorem;
the unconditional half-endpoint proof above does not assume it.

## Remaining RH obligation

RH is not proved. The existing declaration
`riemannHypothesis_of_centered_damped_square_summable` requires finite energy
at some sequence of positive dampings tending to zero. It needs no common
norm bound. The newly completed range epsilon >= 1/2 supplies no such sequence.

Further fixed logarithmic savings in this arithmetic estimate alone do not
close that gap. At epsilon < 1/2, a discrepancy estimate of the form
N^(1-epsilon)/(log N)^q gives the divergent energy majorant
N^(-2 epsilon)/(log N)^(2q), for every fixed q. This is a limitation of that
majorant, not a proof that the actual signed energy diverges. Additional
cancellation is required. The reverse RH-to-membership direction also remains
outside this development.

## Verification

The full combined development passed Lean with exit code 0 and
`verified=true`, in 9.637 seconds (job
`job_qfsFKh_Q0l0NbQ5xzBuKPtkgrJFXUaPa`). The principal dependency reports for
the actual half endpoint, the inclusive unique-centering theorem, and the
unconditional Mertens provider contain only `propext`, `Classical.choice`,
and `Quot.sound`. No RH assumption, sorry, admit, project-local axiom, or
unsafe declaration is used. The final publication gate separately builds
the affected project modules and audits the persisted source.

Wolfram was used to check the cutoff's scalar algebra and the corresponding
logarithmic integral during exploration. The Lean proofs supply the formal
justification independently.
