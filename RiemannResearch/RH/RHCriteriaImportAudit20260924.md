# RH criteria, reciprocal limits, and Möbius sign oscillation
24 September 2026

This update is a curated primary-source audit and a formalization of specific
additional results. It is not an import of every published RH criterion, and it
does not prove RH. Published theorems have not been installed as axioms.

## Results established in the new Lean modules

### A growing inverse-Gram scalar

In `RH/ReciprocalGramCorrection.lean`, stage n uses moduli 2 through n+1.
Write s_n=b_n+G_n μ_n and
W_n=Σ_(i<n) (G_n^(-1)s_n)_i/(i+2). Then, unconditionally,

```math
W_n=(P_n1)(1)+\sum_{d\le n+1}\frac{\mu(d)}d-1
\longrightarrow-r(1).
```

The proof combines an exact finite identity, norm convergence of the projections,
continuity of physical evaluation, and the already proved classical PNT limit.
There is no interchange of an infinite limit and growing matrix inversion.

The actual limit obeys
```math
-(2+\sqrt2)E\le -r(1)\le-(2-\sqrt2)E,
\qquad E=\|r\|^2.
```

Main declarations:
- `reciprocalCorrection_eq_firstCoordinate`
- `reciprocalCorrection_tendsto`
- `reciprocalCorrection_zero_iff_residual_zero`
- `reciprocalCorrection_limit_bounds`
- `riemannHypothesis_of_reciprocalCorrection_tendsto_nonneg`

The last declaration is a conditional research reduction: its limit-sign
hypothesis remains Open.

### Independent weighted approximation

`RH/ParetoWeightedApproximationRH.lean` proves, for every actual legal closure
member f and hypothetical zeta zero s with Re(s)>1/2 and 1≤u<2Re(s),

```math
\int_1^\infty |1-f(x)|^2x^{-u-1}\,dx
\ge\frac{2\Re s-u}{|s|^2}>0.
```

Here f is the project's physical step realization, and the legal closure is
the actual closed span associated with a positive integer index set A.

Consequently, if u_j≥1 tends to 1 and, for each j separately, legal vectors
achieve arbitrarily small u_j-weighted error, RH follows. By the proved Mellin
Plancherel identity, it suffices to have independent arbitrarily small errors
on lines σ_j>1/2 with σ_j→1/2:

```math
\forall j,\epsilon>0,\ \exists f\in V:\quad
\int_{\mathbb R}
|\mathcal M(1-f)(\sigma_j+2\pi i t)|^2\,dt<\epsilon.
```

No exact head, common bound, or coherent family of approximants occurs in this
criterion. Existence of those approximants remains Open.

Main declarations:
- `weightedError_lower_of_zeta`
- `zeta_ne_zero_of_arbitrarily_small_weighted_error`
- `riemannHypothesis_of_independent_weighted_approximation`
- `paretoMellin_line_energy`
- `riemannHypothesis_of_independent_line_approximation`

### Sublinearity and the reciprocal difference sum

`RH/ParetoReciprocalDifference.lean` proves for every Hilbert vector f, with
physical sequence F and F(0)=0,

```math
\sum_{n\ge1}\left|\frac{F(n)}n\right|^2\le2\|f\|^2,
\qquad \frac{F(n)}n\longrightarrow0,
```

and the exact finite identity

```math
\sum_{n=0}^{N-1}\frac{F(n+1)-F(n)}{n+1}
=\sum_{n=0}^{N-1}\frac{F(n+1)}{(n+1)(n+2)}
+\frac{F(N)}{N+1}.
```

Its limit is ⟨f,1⟩. For f=r this is E by the existing
`limitResidual_inner_one`. Convergence means ordered partial sums; absolute
convergence is not claimed.

This formalizes a real s=1 case of Balazard's Proposition 8 and resolves
`HilbertPhysicalSublinearTarget` through the new checked provider
`hilbertPhysicalSublinear`. It does not prove the distinct Möbius reciprocal
sum rule in Balazard's Proposition 7.

### New sign obstruction

`RH/MobiusResidualSignOscillation.lean` proves a general order property.
Let δ_m(f)=mobiusDifferenceCLM m f and p_N f be its biorthogonal reconstruction.
If δ_m(f)≥0 for every m≥2, then

```math
F(k)\le(p_Nf)(k)\le0,
\qquad\|p_Nf\|\le\|f\|.
```

Proof: divisor inversion gives F(n)≥nF(1), so sublinearity gives F(1)≤0.
Removing a finite reconstruction leaves nonnegative charges and zero initial
charges. The exact linear-prefix identity then gives the coordinate order.
Weighted square summation gives the norm bound.

If the actual residual charges are eventually nonnegative OR eventually
nonpositive, remove the finitely many exceptional terms. The remaining
reconstructions are bounded. Existing residual reconstruction escape then
forces RH. Therefore, under ¬RH,

```math
\forall M\ \exists m>M,\ m\ge2:\ \delta_m(r)>0,
\qquad
\forall M\ \exists m>M,\ m\ge2:\ \delta_m(r)<0.
```

The existing identity identifies δ_m(r)=c_∞(m)+μ(m). This concerns both signs
of the actual limiting coefficient corrections, not merely nonzero defects.

Main declarations:
- `firstCoordinate_nonpos_of_mobius_nonneg`
- `sequence_nonpos_of_mobius_nonneg`
- `coordinatePartialSum_order_of_mobius_nonneg`
- `coordinatePartialSum_norm_le_of_mobius_one_sign`
- `riemannHypothesis_of_eventually_one_sign_mobiusDifference`
- `not_RH_mobiusDifference_sign_oscillation`

Eventual one-sidedness is an Open sufficient condition. The proof does not
establish that condition or claim mathematical novelty.

## Primary-source import audit

The following statuses distinguish published mathematics, checked providers,
and propositions merely recorded as targets.

| Source or criterion | Published result relevant here | Actual formalization status |
|---|---|---|
| Báez-Duarte, [math/0205003](https://arxiv.org/abs/math/0205003), Theorem 1.1 and Corollary 3.1 | Integer Nyman–Beurling criterion and RH-equivalent damped Möbius approximation | Concrete legal-to-RH Mellin implication and many projection/coefficient results are proved. The complete classical RH-to-density converse is not imported. |
| Balazard, [1812.04309](https://arxiv.org/abs/1812.04309), Propositions 4, 7, 8, 12–13 | Continuous arithmetic coordinates, reciprocal sum rule, Dirichlet series, coefficient criterion | Existing continuous coordinates and stabilization; this update adds sublinearity and the real reciprocal-difference limit. Proposition 7's full Möbius sum rule remains unformalized. |
| Burnol, [math/9910055](https://arxiv.org/abs/math/9910055), Theorems 1.2–1.3 | Projection zero-product formula and BSY logarithmic criterion | Multiplicity-sensitive scalar zero products are proved. `BurnolProjectionConsequences` retains the explicit projection identity hypothesis. The full BSY boundary passage remains missing. |
| Noor, [1809.09577](https://arxiv.org/abs/1809.09577), Theorems 9 and 12 | Shifted density and annihilator rigidity under local Dirichlet regularity | Concrete shifted density and regularity implications are available. The actual residual's required regularity remains Open. |
| CMNS, [2203.05030](https://arxiv.org/abs/2203.05030), Theorems 14–15 | Weighted Hardy sufficient conditions and a complete biorthogonal family | Useful source-backed routes; completeness of a dual family cannot replace density of the legal family. The annihilator dimension alternative there has an additional conjectural premise. |
| Manzur–Noor–Quintero, [2606.16097](https://arxiv.org/abs/2606.16097), Proposition 3.1 and Theorem 3.1 | Weighted Hardy approximation implies a zero-free half-plane; unconditional raw Möbius convergence above Re(s)=1 | The project proves endpoint convergence at σ=1. This update adds independent weighted/line criteria. Approximants near 1/2 remain Open; reported numerics do not supply them. |
| Bettin–Conrey–Farmer, [1211.5191](https://arxiv.org/abs/1211.5191) | Optimal logarithmic approximation rate under RH and a negative ζ′ moment estimate | Its assumptions cannot be removed when importing its conclusion. |
| Li, [DOI 10.1006/jnth.1997.2137](https://doi.org/10.1006/jnth.1997.2137); [Bombieri–Lagarias](https://websites.umich.edu/~lagarias/doc/bombieri.pdf) | Li positivity and relations with Weil positivity | Actual coefficients and zero geometry exist. Full Li positivity equivalence is not yet proved in Lean. The Weil module retains explicit-formula, detection, and arithmetic-bound hypotheses. |
| Robin and Lagarias, [Lagarias math/0008177](https://arxiv.org/abs/math/0008177) | Divisor-sum inequalities equivalent to RH | Arithmetic functions and concrete targets exist; defining the targets does not import the published criterion proofs. |
| Littlewood/Mertens; Riesz; [sequential Báez-Duarte](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/HOA/IJMMS/Volume2005_21/141565.pdf) | Respectively all-ε exponents 1/2+ε, 1/4+ε, and −3/4+ε | Not found as complete checked criteria in the scoped audit. Endpoint exponents must not replace the all-ε assertions. |

This is a coverage ledger, not a claim that all these results were formalized
in this update. The actual zero-free-half-strip equivalence and concrete
Chebyshev–Mellin analyticity criterion already have checked providers.

## What is the least remaining obligation?

There is no unique logically least condition among equivalent reformulations.
A compact scalar obligation within the actual residual framework is

```math
\boxed{r(1)\le0.}
```

The established estimate (2−√2)E≤r(1), with E≥0, makes this equivalent to
r=0. The new scalar theorem reformulates it as a nonnegative limit for W_n.
The older bounded-cofinal-tail criterion is another exact residual equivalence:

```math
\exists C\ \forall N_0\ \exists N\ge N_0:\quad
N\sum_{k>N}\frac{r(k)^2}{k(k+1)}\le C.
```

Each yields RH. The converse RH⇒r=0 is classical Báez-Duarte mathematics but
has not been imported as a kernel-checked theorem in this project. Accordingly,
we claim exact internal residual equivalences and a checked implication to RH.

## Further research: why the current facts do not contradict ¬RH

The following arguments are written mathematical analysis, not additional
Lean declarations.

First, interpolation cannot move the established endpoint to the critical
line. For E_N(u)=∫|1−F_N(x)|²x^(−u−1)dx, Hölder gives

```math
E_N(u)\le E_N(1)^{2-u}E_N(2)^{u-1}
\le(N+1)^{2-u}q_N,\qquad1<u<2,
```

where the existing PNT bounds give E_N(1)≤(N+1)q_N and E_N(2)≤q_N.
Logarithmic or subpower savings in q_N cannot overcome the fixed positive
power for u<2.

There is an exact countermodel to using only those analytic properties.
Fix s₀=β+iγ with 1/2<β<1, take the closed subspace
V=ker(f↦M f(s₀)), and set

```math
e_R(x)=\frac{R^{s_0}}{1-2^{-s_0}}\,1_{[R,2R]}(x),
\qquad F_R=1-e_R.
```

Then M e_R(s₀)=1/s₀, F_R∈V, and F_R=1 on [1,R). Direct integration gives

```math
E_R(u)=\frac{1-2^{-u}}{u|1-2^{-s_0}|^2}R^{2\beta-u}.
```

Thus E_R(2)→0 and E_R(1)/R→0, although E_R(u)→∞ for u<2β.
This subspace is a model, not an identification with the arithmetic legal
space. It proves that extra arithmetic input is necessary for this route.

Second, a hypothetical right-hand zeta zero ρ naturally creates an arithmetic
annihilator with both defect signs. Define

```math
H_\rho(n)=\frac{n(n+1)}{\rho}
\bigl(n^{-\rho}-(n+1)^{-\rho}\bigr),\qquad H_\rho(0)=0.
```

For 1/2<Re(ρ)<1 it belongs to the complex Pareto space. The Mellin formula
gives its bilinear pairing with g_d as
(d^(−1)−d^(−ρ))ζ(ρ)/ρ, which vanishes if ζ(ρ)=0. Its normalized real part
h(n)=Re(H_ρ(n)/H_ρ(1)) has h(1)=1 and Δh(n)→0. Exact Möbius arithmetic yields

```math
\delta_p(h)=\Delta h(p)-1\to-1,
\qquad
\delta_{pq}(h)=\Delta h(pq)-\Delta h(p)-\Delta h(q)+1
\to1-\Delta h(q)>0
```

for primes p→∞ and one sufficiently large fixed prime q, with p≠q.
This neither asserts such a zero nor identifies h with the actual residual.
It explains why orthogonality is compatible with the new sign oscillation
obstruction, rather than supplying the missing eventual-sign premise.

A useful next arithmetic target is to produce independently small weighted
errors for u arbitrarily close to 1. For the canonical exact-head family,
E_N(1)=o(N^(u−1)) suffices at a fixed u∈(1,2), through the existing
head-tail comparison. Obtaining this for every u>1 would prove RH; no such
provider is established here.

Wolfram was used to check finite Möbius inversion/Abel identities and the
countermodel's elementary weighted integral. These computations support
algebraic checking only. Lean proof terms supply formal verification of the
new declarations; computations are not a substitute for the missing
arithmetic theorem.

## Numerical test of finite first-coordinate positivity

A possible route to r(1)≤0 would be (P_n1)(1)≥1 at every finite stage.
Wolfram evaluation of the exact digamma Gram formula gives:

| Stage n (moduli 2 through n+1) | (P_n1)(1), approximately |
|---|---:|
| 1 | 1 |
| 2 | 1.03654893685113206342061329294 |
| 3 | 0.963067442677464723873332120941 |
| 4 | 0.946713055581316091426432023693 |
| 5 | 0.950960867877767219488651373220 |

The below-one values reject this proposed universal finite-stage inequality
as a numerical research route. These inequalities are not Lean-certified
interval bounds; they do not decide the limiting value or rule out a cofinal
subsequence approaching from above. A separate 60-digit matrix evaluation
agreed with the displayed values.

Reproducible Wolfram Language code (the omitted k=L term is zero):

```wolfram
Clear[g];
g[d_, e_] := Module[{l = LCM[d, e]},
  Sum[(Mod[k, d]/d) (Mod[k, e]/e)
    (PolyGamma[0, (k + 1)/l] - PolyGamma[0, k/l])/l,
    {k, 1, l - 1}]];
Table[{n, N[
  Table[1/d, {d, 2, n + 1}] .
    LinearSolve[
      Table[g[d, e], {d, 2, n + 1}, {e, 2, n + 1}],
      Table[Log[d]/d, {d, 2, n + 1}]], 30]},
  {n, 1, 5}]
```

## Verification scope

The four developments were checked in coherent isolated Lean batches. The
printed axiom dependencies of the principal results are only `propext`,
`Classical.choice`, and `Quot.sound`. Explicit hypotheses in conditional
RH theorems remain hypotheses; axiom inspection does not discharge them.
The publication checkpoint validates the saved modules and affected local
reverse dependencies. No unconditional RH theorem is asserted.
