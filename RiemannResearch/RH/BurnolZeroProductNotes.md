# Burnol zero product: formalized results and remaining analytic work

Research and Lean additions, 2026-09-23.

The scalar zero product, its convergence, strict positivity, exact logarithmic
representation, and RH equivalence are proved. The identification with the
continuous Nyman–Beurling projection remains an explicit analytic obligation.

## Canonical quantities

The index type `RightZero` consists of the actual nontrivial zeros of
`riemannZeta` satisfying `1/2 < re`. The open-strip condition excludes the pole
at one. Both signs of the imaginary part are included. Every distinct zero is
raised to `Zeta23.zeroMult`, the project's checked analytic multiplicity.
There is no arbitrary enumeration or user-supplied multiplicity assumption.

Write

\[
a_\rho=\frac{|1-\rho|^2}{|\rho|^2},\qquad
P=\prod_{\Re\rho>1/2}a_\rho^{m_\rho},\qquad
S=\sum_{\Re\rho>1/2}m_\rho\log\left|\frac{\rho}{1-\rho}\right|.
\]

`productSq` is first constructed as the infimum of the directed family of all
finite-subset products. `hasProd_weightedFactorSq` proves that this construction
is a genuine convergent infinite product. `product` is the corresponding
unsquared product, also equipped with an actual `HasProd` proof.

The checked statements give

\[
0<P\le1,\qquad P=e^{-2S},\qquad S\ge0,\qquad
B:=\texttt{product}=e^{-S}=\sqrt P>0,
\]

and

\[
P=1\iff B=1\iff S=0\iff\mathrm{RH}.
\]

These are equivalences; they do not establish that any of the equivalent
RH-strength equalities holds.

## Source modules

| Module under `RiemannResearch` | Main content |
|---|---|
| `Analysis/ContractiveProducts.lean` | Exact finite and infinite weighted-defect telescopes, monotone cutoff limits, limit-one criterion, multiplicity and logarithmic calculus |
| `RH/BurnolZeroFactors.lean` | Exact factor defect, conjugation, half-plane reflection geometry, normalized factors, boundary modulus, logarithmic identity |
| `RH/BurnolProductCalculus.lean` | Zero-factor specializations of the exact cutoff and multiplicity identities |
| `RH/BurnolZeroProduct.lean` | Canonical actual zero family, analytic multiplicities, finite-subset net convergence, RH equivalence, single-zero obstructions |
| `RH/BurnolZeroProductConvergence.lean` | Summability of defects and logarithms, unconditional strict positivity, exponential representation, unsquared infinite product |
| `Analysis/NestedProjectionEnergy.lean` | Exact difference between two nested projections and their residual energies |
| `Analysis/InnerMultiplierProjection.lean` | Abstract isometric-multiplier projection computation from a stated reproducing identity |
| `RH/BurnolProjectionConsequences.lean` | Consequences of an explicitly supplied projection/product identity, including the exact smaller-space remainder |

The main scalar theorem names, in `RiemannResearch.RH.Burnol`, are
`productSq_pos`, `productSq_eq_exp_neg_two_logarithmicZeroSum`,
`hasProd_weightedFactor`, `product_eq_one_iff_rh`, and
`logarithmicZeroSum_zero_iff_rh`.

## Exact defects and convergence

The base identity is

\[
1-a_\rho=\frac{2\Re\rho-1}{|\rho|^2}.
\]

Multiplicity has the exact effect

\[
1-a_\rho^m=(1-a_\rho)\sum_{j=0}^{m-1}a_\rho^j.
\]

For a sequence of factors, with `P_k` the product before index `k`,

\[
1-P_N=\sum_{k<N}P_k(1-a_k).
\]

The infinite version is proved with `HasSum` whenever the contractive cutoff
product has the stated limit. Its coefficients retain all preceding factors.

Positivity of the actual zero product is derived from the checked theorem
`Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam`. An elementary comparison bounds
the multiplicity-weighted defect by five times that summable zero weight.
Mathlib's logarithm summability theorem then supplies the exponential product
representation. No RH or projection identity is used in this proof.

## The projection connection and its precise boundary

Burnol's Theorem 1.2 identifies the norm of the projection of the constant
function onto the continuous Nyman–Beurling space with the unsquared product
`B`. His proof uses the Mellin/Hardy correspondence and a normalized Blaschke
product. Lemma 2.4 computes the projection of the kernel `1/s` onto the inner
multiplier range. Theorem 1.3 connects `S` with the normalized critical-line
integral of `log |zeta|` [1].

The generic Hilbert-space part of the kernel computation is now proved. To use
it analytically one must still supply the multiplier isometry, the reproducing
relation, and the identification of the scalar coefficient with `B`.

If `U <= V`, `e` has norm one, and the supplied identity is
`norm (P_V e)^2 = productSq`, the checked transfer theorem gives exactly

\[
\|e-P_Ue\|^2=1-P+\|P_Ve-P_Ue\|^2.
\]

Consequently inclusion alone does not eliminate the last term. Applying this
formula to a discrete Pareto space requires an actual isometric transport into
the continuous ambient space and a checked inclusion. Equality of the discrete
and continuous projections needs an additional argument.

**Open formalization obligations:** the full continuous Nyman–Beurling/Hardy
space identification; the analytic inner-factor identification and evaluation;
the BSY critical-line integral identity and its integrability; and the precise
continuous-to-Pareto transport needed for the desired application. None is
introduced as an axiom or silently treated as a proved provider.

## Related literature kept separate

Bui–Lester–Milinovich restate the BSY zero-sum identity and prove results on
truncated integrals, including an unconditional error estimate. Their
asymptotic theorems are not formalized in this addition [2].

Burnol's later approximation lower-bound paper is a different result [3]. The
existing `BurnolDyadicComparison.lean` remains a conditional consumer of a
logarithmic distance envelope. It is not evidence for the zero-product
projection identity.

## References and verification

1. J.-F. Burnol, *A note on Nyman's equivalent formulation of the Riemann Hypothesis*, Theorems 1.2–1.3, formula (2.1), Lemma 2.4. [arXiv:math/9910055](https://arxiv.org/abs/math/9910055).
2. H. M. Bui, S. J. Lester, M. B. Milinovich, *On Balazard, Saias, and Yor's equivalence to the Riemann Hypothesis*, formula (1.1), Theorems 1.1–1.2. [arXiv:1306.0856](https://arxiv.org/abs/1306.0856).
3. J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*. [arXiv:math/0103058](https://arxiv.org/abs/math/0103058).

Representative scalar and projection results passed Lean verification with
axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, or project axiom is added. The publication checkpoint
validates the actual module imports and the affected project dependency chain.
