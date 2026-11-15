# P/Q density operators and the remaining RH premise

Date: 2026-11-12 (user-facing date).
Source: user-provided correction reserving B for dQ/dP.
Base examined: 8b94e4c6fcadf811881e42aa2999f5c099b643c4.

## Seven-agenda continuation

The follow-up [seven-agenda catalog](THEOREM_CATALOG_PQ_SEVEN_AGENDAS_20261112.md)
records the reverse Q/P pairing, compressed V pairing, arithmetic target-totality
equivalence, normalized signed budget, residual correlations, leakage/parity
criteria, canonical CRT norm escape, and the conditional analytic converse.
The explicit analytic approximation provider and the arithmetic bounds remain Open.

## Operator-variance continuation

The [coupling-variance catalog](THEOREM_CATALOG_COUPLING_VARIANCE_20261115.md)
records C* C = Phi(B^2) - Phi(B)^2, the exact total-variance decomposition,
and zero variance iff full unaugmented density. Actual zero variance remains
Open. A uniform positive gap for C C* is equivalent to finite-dimensionality
of the Q complement; that gap also remains Open.

## Notation and scope

For physical n >= 1:
P(n)=1/[n(n+1)], Q(n)=1/[zeta(2)n^2].
Bf(n)=(n+1)f(n)/[zeta(2)n], Df(n)=f(n)/n, Rf(n)=f(n)/(n+1).
B inverse is zeta(2)n/(n+1). B always means QDensityMetric.B here.
Historical QShiftedReciprocal.B implements R; new modules use local notation R.
The physical index n is encoded at normalized l2 coordinate n-1.
All density results below use every conductor k>=2.

## Established declarations

Module: RH/QDensityMetricInverse.lean
Namespace: RiemannResearch.RH.QDensityMetricInverse

| Declaration | Meaning |
|---|---|
| inverse, inverse_apply | Bounded continuous linear inverse density |
| inverse_B, B_inverse, densityEquiv | Two-sided bounded linear equivalence B |
| qSequence_inverse | Physical multiplier zeta(2)n/(n+1) |
| D_eq_density | Df=zeta(2) Bf-f |
| inverse_D, R_eq_inverse_D | B inverse D=zeta(2) R |
| R_eq_inverse | R=I-B inverse/zeta(2) |
| pareto_inner_inverse | <f,g>_P=<f,B inverse g>_Q |
| q_inner_density | <f,g>_Q=<f,Bg>_P |
| q_inner_pareto_add_D | Q pairing = (P pairing + P pairing with D)/zeta(2) |
| q_inner_pareto_compressed | P pairing with D can be compressed into a closed P subspace |
| norm_comparison | (zeta(2)/2)||f||_Q^2 <= ||f||_P^2 <= zeta(2)||f||_Q^2 |
| DP, DP_toPareto, DP_physical | D_P=T D_Q T inverse; D_P T=T D_Q; physical division by n |
| map_closure | B(cl S)=cl(BS) for any submodule |
| mem_density_closure_iff | Bf in cl(BS) iff f in cl S |
| density_closure_eq_top_iff | Density is preserved and reflected by B |

Module: RH/QDensityClosureTransfer.lean
Namespace: RiemannResearch.RH.QDensityClosureTransfer
Here S=QFullResidueProjection.legalSpan and V=QFullResidueProjection.closure.

| Declaration | Meaning |
|---|---|
| map_legalSpan | Operator image of S equals the corresponding generator span |
| full_D_map_dense | cl(D S)=H, from the existing full-conductor theorem |
| full_joint_orthogonal_eq_bot | U_P ∩ U_Q = {0} for the full conductor span, with both complements realized in Q coordinates |
| full_R_map_dense | cl(R S)=H |
| full_augmentedClosure_eq_top | cl span{g_k,Bg_k}=H |
| densityClosure_eq_image | cl(B S)=B(V) |
| densityClosure_eq_top_iff | cl(B S)=H iff V=H |
| fullClosure_eq_top_iff_density_generators_mem | V=H iff all B g_k belong to V |
| fullClosure_eq_top_iff_density_invariant | V=H iff B(V) is contained in V |
| density_target_mem_iff | B1 in cl(B S) iff 1 in V |

Full R-density is transferred by B inverse D=zeta(2)R, not by inverting D.
The complete P statements follow from the sequence-preserving equivalence and equivalent norms.

For `full_joint_orthogonal_eq_bot`, let `U_v` be the orthogonal complement of the same
physical full-conductor span in measure `v`. Orthogonality in both measures gives
`<D g_k,f>_P=0` by the exact change-of-weight identity. The reciprocal density
proved by the finite sieve in `QReciprocalFullDensity` then forces `f=0`.

## Complement separation and the bounded residual criterion (2026-11-15)

Module: RH/QComplementDensitySeparation.lean
Namespace: RiemannResearch.RH.QComplementDensitySeparation
Here U=V-perp-Q, and the P complement is pulled back to the same Q carrier.

| Declaration | Exact content |
|---|---|
| pareto_orthogonal_eq_density_image | U_P=B(U_Q), with the physical sequence identification explicit |
| density_mem_orthogonal_iff | For u in U, B u belongs to U if and only if u=0 |
| orthogonal_inf_density_image_eq_bot | U intersect B(U) is zero |
| orthogonal_inf_inverse_image_eq_bot | U intersect B inverse(U) is zero |
| id_sub_density_injective | I-B restricted to U is injective into the ambient space |
| density_eigenvector_eq_zero | U contains no nonzero B-eigenvector |
| orthogonal_eq_bot_iff_density_invariant | U=0 if and only if B(U) is contained in U |
| orthogonal_inf_reciprocal_range_eq_bot | U intersect range(D) is zero |
| orthogonal_eq_bot_iff_bounded_constant_residual | U=0 if and only if the physical values of Pi_U(1) admit a finite uniform bound |
| exists_nonzero_submodule_inf_density_image_eq_bot | The actual B has a nonzero subspace S with S intersect B(S)=0 |
| riemannHypothesis_of_orthogonal_eq_bot | Conditional research reduction: U=0 implies RH |

The counterexample S is a line supported on the first two normalized coordinates.
It is not the actual arithmetic complement U. It demonstrates that invertibility,
positivity and trivial intersection alone cannot establish U=0.

Canonical next check: prove that the actual residual r=Pi_U(1) satisfies
`exists A >= 0, forall physical n >= 1, abs(r(n)) <= A`.
This remains **Open**. The existing annihilator tail-escape theorem kills a
bounded r; the checked arithmetic target-totality theorem then forces V=H.
The complete Q norm bound on r does not supply this physical sup bound.
Density invariance of U is likewise an equivalent open condition, not a provider.
No unconditional U=0 or RH theorem is claimed.

## Density-coupling surjectivity continuation (2026-11-14)

Let V be the actual full-conductor closure, W=V-perp-Q, and
C=Pi_W B|V : V -> W. Its adjoint maps W -> V. The new result is the
unconditional equivalence
\[
\operatorname{Surjective}(C)
\iff \exists N,\ \forall w\in W,\
  [w(1)=\cdots=w(N)=0\Rightarrow w=0]
\iff \dim W<\infty.
\]
Existence of such a finite detecting head remains **Open**. Surjectivity,
finite-dimensionality, W=0, and RH are not asserted unconditionally.
N=0 is allowed and then the detecting-head condition says W=0.

Module: RH/QDensityCouplingSurjectivity.lean
Namespace: RiemannResearch.RH.QDensityCouplingSurjectivity

| Declaration | Exact content |
|---|---|
| coupling, reverseCoupling, coupling_coe | Actual density leakage V -> W and reverse compression W -> V |
| coupling_adjoint | The reverse compression is the Q adjoint |
| reverseCoupling_eq_reciprocal | C* w=(1/zeta(2)) Pi_V D w |
| reverseCoupling_zero, coupling_adjoint_injective | Unconditional injectivity from full reciprocal density |
| coupling_dense_range | The range of C is dense in W |
| coupling_adjoint_tail_bound | First N normalized coordinates zero implies norm(C* w) <= norm(w)/(zeta(2)(N+1)) |
| PhysicalHeadUnique, physicalHeadUnique_iff | Exact translation to physical sites 1 through N |
| coupling_surjective_iff_finite_head | Surjectivity is equivalent to existence of one detecting physical head |
| coupling_surjective_iff_finiteDimensional | Surjectivity is equivalent to finite-dimensionality of W |
| exists_unit_head_zero_small_adjoint | If W is infinite-dimensional, each head misses a unit vector with the explicit adjoint bound |
| coupling_not_surjective_of_infiniteDimensional | The infinite-dimensional case rules out surjectivity |
| coupling_surjective_of_finite_head | **Conditional research reduction**; the finite-head existence premise is Open |

The reusable proof is in Analysis/FiniteHeadSurjectivity.lean. It derives a
uniform adjoint norm bound from surjectivity using the Banach open mapping
theorem, then combines a tail bound with finite-coordinate linear algebra.
Its reverse implication uses dense range in a finite-dimensional target.

The owning metric modules also add QDensityMetric.B_symmetric,
QReciprocalMetric.D_norm_sq (the exact complete energy), and
QReciprocalMetric.D_norm_le_of_head_zero. No infinite tail is discarded.


Focused acceptance for this continuation:
- Job: job_z7V0NFKgfzXtYNY8pGgC7IU0_lMKCrZo.
- Backend: Bazel --config=buildbuddy.
- Target: //RiemannResearch/RH:QDensityCouplingSurjectivity.
- Result: verified=true, exit_code=0; server verification duration 202.086 seconds.
- Source SHA-256: a94b00dd8fe54d8222170f10ae6cda35b3d36ddc09bb04da0900a459776d5da1.
- [BuildBuddy log](https://app.buildbuddy.io/invocation/b5465e74-72da-4ddb-9864-e437ac0becde).
- Full-project validation and publication are performed by the required checkpoint;
  this focused receipt alone does not certify downstream consumers.

## Actual-zero dimension obstruction (2026-11-14)

Module: RH/QComplementZeroDimension.lean
Namespace: RiemannResearch.RH.QComplementZeroDimension

The requested finite upper bound on dim W remains **Open**. The new result
is the sharp opposite-direction obstruction: if W has real dimension d,
every finite family of distinct actual zeros with 1/2 < Re(s) < 1 has
cardinality at most d. Consequently finite dimension of W, or surjectivity
of the actual density coupling, forces finitely many such zeros.

| Declaration | Exact content |
|---|---|
| powerCharacters_linearIndependent | The characters n^(1-s), indexed by distinct complex s, are independent over C |
| normalizedMellin_linearIndependent | Actual continuous normalized Mellin functionals on Q are independent |
| normalizedMellin_zero_on_closure | An actual right-hand zero annihilates the full all-conductor closure |
| zeroFunctionals_linearIndependent | Their restrictions to W remain independent over C |
| rightZero_family_card_le_finrank | Any finite distinct family of actual right-hand zeros has cardinality at most dim_R W, assuming W is finite-dimensional |
| finite_rightZeros_of_finiteDimensional | Finite-dimensional W forces a finite actual right-hand zero set |
| not_finiteDimensional_of_infinite_rightZeros | An infinite actual right-hand zero set forces infinite-dimensional W |
| finite_rightZeros_of_coupling_surjective | Proposed surjectivity implies the same arithmetic finiteness conclusion |

The proof uses the existing complete Q/P transfer, actual arithmetic Mellin
formula and integer dilation identity. Dedekind character independence
and the proved two/three logarithm argument supply independence. Restriction
to W loses no information because the functionals vanish on V. Evaluation
on a real basis of W gives the sharp complex dimension bound d, not 2d.
No RH, zero-simplicity, RH-failure conjecture, spectral-synthesis assumption,
or unproved analytic provider is used.

This does not prove the converse from finitely many zeros to finite dimension.
It also does not prove that the right-hand zero set is finite.
The cited Hardy-space paper's zero-or-infinite conclusion assumes the
RH-failure conjecture; it is not imported as an unconditional theorem.

Sources: [Bagchi, Theorem 1](https://arxiv.org/abs/math/0607733) for the discrete
space; [Calderaro--Manzur--Noor--Santos, Section 4](https://arxiv.org/html/2203.05030v4)
for the related independent-zero-kernel strategy. The actual Q bridge is
proved directly here.

Candidate acceptance: job_1KAFEsq7-gDmcj6jYs6dl1gJM2H9FuPE,
Bazel --config=buildbuddy, verified=true, exit_code=0,
40.488 seconds server verification.
[BuildBuddy log](https://app.buildbuddy.io/invocation/9a9fdf6b-e8d1-4f6f-b1e8-9805444a651f).
This is a snippet receipt; publication requires the full-project checkpoint.

## Structural dimension audit and quantitative bounds (2026-11-14)

Proofs developed and reviewed on base commit
`13df1e0c895794f6cecde835a577c6f96f5ec253`.
Finite-dimensionality of W, surjectivity of C, and RH remain **Open**.

Write Z = zeta(2), H = QHilbert, V = the actual closed all-conductor residue
span, W = V-perp-Q, and C = Pi_W B|V. In normalized coordinates indexed by
n >= 0, D acts by division by n+1 and B = (I+D)/Z.

### Exact statements added

| Module / declaration | Status and exact content |
|---|---|
| Analysis/FiniteHeadSurjectivity.finrank_le_of_headUnique | A detecting head of length N gives finrank <= N |
| Analysis/FiniteHeadSurjectivity.headUnique_of_adjoint_lower_bound | An adjoint lower estimate above the tail coefficient gives a detecting head |
| Analysis/FiniteHeadSurjectivity.exists_unit_head_zero_of_not_headUnique | Failure of detection has a unit witness |
| RH/QDensityCouplingSurjectivity.coupling_adjoint_energy_identity | Exact complete reciprocal energy with the W-projected remainder retained |
| RH/QDensityCouplingSurjectivity.eq_zero_of_reciprocal_mem_orthogonal | Df in W implies f=0; in particular W intersects range(D) only at zero |
| RH/QDensityCouplingSurjectivity.physicalHeadUnique_of_adjoint_lower_bound | A uniform lower estimate gives the explicit physical head cutoff |
| RH/QDensityCouplingSurjectivity.finrank_le_of_physicalHeadUnique | A physical head of length N bounds the real dimension by N |
| RH/QDensityCouplingSurjectivity.finiteDimensional_iff_adjoint_lower_bound | Exact equivalence between finite dimension and a uniform positive lower bound for C* |
| RH/QDensityCouplingSurjectivity.finiteDimensional_and_finrank_le_of_adjoint_lower_bound | **Conditional** finite dimension and finrank <= N from the stated lower bound |
| RH/QComplementZeroDimension.rightZero_family_card_le_of_adjoint_lower_bound | **Conditional** bound by N for any finite distinct family of actual right-hand zeros |
| RH/QComplementZeroDimension.exists_unit_small_adjoint_of_rightZero_family | More than N actual distinct right-hand zeros force a unit vector with head zero and small C* image |

The exact energy identity is
\[
 Z^2\|C^*w\|^2+\|\Pi_W Dw\|^2
 =\|Dw\|^2
 =\sum_{n=0}^{\infty}\frac{|\widehat w_n|^2}{(n+1)^2}.
\]
Here \(\widehat w_n\) is the normalized coordinate, not the physical value.
No signed or projected remainder is discarded.

The exact dimension criterion is
\[
 \dim_{\mathbb R}W<\infty
 \quad\Longleftrightarrow\quad
 \exists\delta>0\ \forall w\in W,\quad
       \delta\|w\|\le\|C^*w\|.
\]
Neither side has an unconditional provider. If such a lower estimate is supplied,
then for every N satisfying \(1/[Z(N+1)]<\delta\),
\[
 \dim_{\mathbb R}W\le N.
\]
Indeed, a vector whose first N coordinates vanish satisfies the reverse upper
estimate \(\|C^*w\|\le\|w\|/[Z(N+1)]\); the strict gap forces that vector to
vanish. The head map into \(\mathbb R^N\) is therefore injective.

Conversely, more than N actual distinct right-hand zeros force a unit vector
with its first N coordinates zero and
\[
 \|C^*w\|\le\frac1{Z(N+1)}.
\]
If the head map were injective, the new dimension upper bound and the existing
independent-zero-functional lower bound would contradict each other. This
argument does not assume W is finite-dimensional. It counts distinct zeros,
not their analytic multiplicities.

### Counterexample to the operator-only route

The following is an explicit analytic counterexample, not a Lean-formalized
construction and not a counterexample to finite-dimensionality of the actual
arithmetic W. It preserves the exact diagonal D and B, full reciprocal image
density, and the regularity obstruction, while its complement is infinite.

Work in real \(\ell^2(\mathbb N_{\ge1})\), put \(Dx(n)=x(n)/n\) and
\(B=(I+D)/Z\). Partition positive integers into
\[
 A_j=\{2^j(2k+1):k\ge0\},\qquad j\ge0.
\]
Let \(a_p=(1-2^{-p})\zeta(p)\), and define unit vectors with disjoint supports:
\[
 u_j(2^j(2k+1))=a_{3/2}^{-1/2}(2k+1)^{-3/4},\qquad
 u_j(n)=0\quad(n\notin A_j).
\]
Then \(W_0=\overline{\operatorname{span}}\{u_j:j\ge0\}\) is a closed
infinite-dimensional space. Set \(V_0=W_0^\perp\).

1. \(W_0\cap\operatorname{ran}D=\{0\}\). If
   \(u=\sum_j c_j u_j\ne0\), choose \(c_j\ne0\). On A_j the coordinates of
   the only possible \(D^{-1}u\) equal a nonzero constant times
   \(2^j(2k+1)^{1/4}\); they are not square summable.
2. \(\overline{D(V_0)}=H\). If \(y\perp D(V_0)\), self-adjointness gives
   \(Dy\in W_0\cap\operatorname{ran}D=\{0\}\); injectivity of D gives y=0.
3. B is positive, bounded, boundedly invertible, and has exactly the same
   diagonal spectrum as the actual density multiplier.
4. \(C_0=\Pi_{W_0}B|_{V_0}=Z^{-1}\Pi_{W_0}D|_{V_0}\) is compact.
   Its adjoint is injective by item 1, so its range is dense.
   It cannot be surjective onto infinite-dimensional W_0.
5. The failure of a uniform lower bound is explicit:
   \[
   \|C_0^*u_j\|^2=
   \frac{4^{-j}}{Z^2}
   \left(\frac{a_{7/2}}{a_{3/2}}-
         \left(\frac{a_{5/2}}{a_{3/2}}\right)^2\right)\longrightarrow0.
   \]
   The bracket is strictly positive: it is the variance of reciprocal odd
   integers under strictly positive weights. This is the complete projected
   energy, not just an upper estimate.
6. Every finite head misses some u_j, by taking \(2^j>N\). Thus there is no
   uniform detecting head.
7. These are rough vectors: the physical coordinate corresponding to a
   nonzero u is unbounded on a block with \(c_j\ne0\). Also its normalized
   squared tail is bounded below by a positive multiple of \(N^{-1/2}\);
   hence \(N\|\operatorname{tail}_N u\|^2/(\log N)^k\to\infty\) for each
   fixed k. Even these qualitative roughness consequences of the actual
   dilation results do not by themselves exclude infinite dimension.

Wolfram checked the three scalar normalization sums \(a_{3/2},a_{5/2},a_{7/2}\).
The orthogonality, density, compactness, and infinite-dimensionality arguments
above are analytic proofs, not conclusions from finite numerical data.

The model does not assert the arithmetic residue identities, actual common
Mellin-zero functionals, or invariance under the repository's floor dilations.
It refutes an inference from the operator assumptions alone; arithmetic
dilation structure could still supply a missing estimate.

### Audit of the other routes

| Available input | What follows | What is still missing |
|---|---|---|
| B is positive and invertible | A metric equivalence on H | C is an off-diagonal map V -> W, not a self-adjoint invertible endomorphism |
| C* is injective | C has dense range; ker(C*)=0 | Closed range, equivalently the uniform positive lower estimate |
| D is compact and C is its off-diagonal compression | C is compact | Compactness is compatible with injective dense range in infinite dimension |
| I+D is invertible (hence Fredholm) | The ambient multiplier B is invertible | Its off-diagonal compression C need not be Fredholm |
| Full reciprocal density | W intersects range(D) only at zero | A dimension bound; the explicit model satisfies this stronger density too |
| Floor dilation preserves V | W is invariant under adjoint dilations | A finite-rank constraint, finite detecting head, or uniform observability estimate |
| Common Mellin characters are independent | Dimension lower bounds | Completeness of those functionals and a finite zero set would be additional assumptions |
| Exact finite CRT compatibility and interpolation | Solvability on each finite head | A single stage-independent norm/energy bound controlling full tails |
| Weak compactness | Limits of bounded legal lifts remain legal | Boundedness of the unsmoothed lifts must first be proved |

There is also a kernel obstruction to a naive Fredholm argument. Full D-density
implies that V is infinite-dimensional: otherwise D(V) would be finite-dimensional,
closed, and dense in the infinite-dimensional H. If W were finite-dimensional,
C would have finite rank and consequently an infinite-dimensional kernel.
More generally, a compact C with closed range has finite-dimensional range.
Thus demanding both closed range and finite-dimensional kernel for C would
contradict the already infinite-dimensional source V. The appropriate missing
condition concerns closed range of C (or a lower estimate for C*), not a
Fredholm assertion for the whole ambient multiplier.

A contraction semigroup alone does not force a nonzero co-invariant complement
to be infinite-dimensional. For right translations on \(L^2(0,\infty)\),
the backward translations satisfy \(S_t^*e^{-a x}=e^{-at}e^{-a x}\)
for \(a>0\); their common invariant line is one-dimensional.
Conversely, neither infinite ambient dimension nor a unitary extension
bounds a general complement's dimension. The actual residue arithmetic is essential.

The inspected exact declarations are
`QFloorDilation.floorDilation_mem_legalClosure`,
`QAnnihilatorDilationEscape.nonzero_annihilator_log_scaled_tail_tendsto_atTop`,
`QDensityClosureTransfer.full_D_map_dense`,
`QDensityClosureTransfer.fullClosure_eq_top_iff_density_invariant`, and
`Pareto.riemannHypothesis_of_cofinal_reciprocal_bound`.
The last theorem explicitly requires one full CRT-energy bound for all stages.
Density invariance \(B(V)\subseteq V\) is already equivalent to V=H in this
development, so assuming it would conceal the desired density conclusion.

### Precise remaining requirement

Prove, for the actual arithmetic W, one constant \(\delta>0\) such that
\[
 \sum_{n=0}^{\infty}\frac{|\widehat w_n|^2}{(n+1)^2}
 -\|\Pi_W Dw\|^2
 \ge Z^2\delta^2\|w\|^2\qquad(w\in W).
\]
Equivalently, prove that a single finite physical head determines every w in W.
Pointwise positivity for each nonzero w is already known; uniform positivity
on the whole unit sphere is the undisclosed mathematical content. Obtaining it
from finite-dimensional compactness would be circular.

Even after proving finite dimension, the current zero-functional results give
only finiteness of the actual right-hand zero set. They do not prove that this
set is empty. The related Hardy-space paper explicitly assumes the RH-failure
conjecture to obtain its zero-or-infinite dimension result; that hypothesis has
not been imported here. No spectral-synthesis converse has been assumed.

Primary references: [Bagchi's discrete criterion](https://arxiv.org/abs/math/0607733);
[Calderaro--Manzur--Noor--Santos, Section 4 and Theorem 21](https://arxiv.org/html/2203.05030v4).
These support the context and the stated conditionality, not an unconditional
dimension upper bound.

### Verification and review boundary

Prepublication verification: job `job_H8RqnO2JWkO8blpUnvj79H8X-7BbUgqk`,
Bazel `--config=buildbuddy`, verified=true, exit_code=0, 48.583 seconds
reported server verification. The snippet imports the final
`QComplementZeroDimension` module and its transitive dependencies, including
all three changed Lean modules. Eleven `#guard_msgs` checks confirm that
each added theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
[Final verification log](https://app.buildbuddy.io/invocation/9f6f7f62-3b5f-470a-95e5-5482859d80dc).

An earlier focused build of `//RiemannResearch/RH:QComplementZeroDimension`
also passed (job `job_EjTQBGGZ90pa828Zh9prDEUei0qEQmoM`, 77.948 seconds).
The final guard job above includes subsequent direct-import additions.

Final source SHA-256 values:

| File | SHA-256 |
|---|---|
| Analysis/FiniteHeadSurjectivity.lean | 220e00212c83b8e30b93579d0b7bf3d9e7aac1442844093d6ca74b9745b313b9 |
| RH/QDensityCouplingSurjectivity.lean | 1f6fbc872e46e82fa2fd13ed7c334e8fa8f52cee2c33f49b0566573effb50ea2 |
| RH/QComplementZeroDimension.lean | 5fbea844d83bfc69f0041a788e599664bff17adf4fd367b375c4a1595b2bda7e |

This receipt covers the changed modules and their imports.
Publication uses a separate whole-project checkpoint.

## Conditional research reductions

| Declaration | Exact open premise | Conclusion |
|---|---|---|
| riemannHypothesis_of_densityClosure_eq_top | cl(B S)=H | Mathlib RiemannHypothesis |
| riemannHypothesis_of_density_target | B1 in cl(B S) | Mathlib RiemannHypothesis |
| riemannHypothesis_of_density_invariant | For every f in V, Bf is in V | Mathlib RiemannHypothesis |

All use the existing QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure.
That bridge takes 1 in V explicitly, transfers to the Pareto legal closure, and
uses the existing Mellin separation theorem. No RH premise is discharged by
full_D_map_dense or full_augmentedClosure_eq_top.
The continuation proves 1 in V iff V=H without analytic assumptions.
It also proves RH iff V=H conditional on the explicit
BaezDuarteMobiusApproximation provider; this analytic hypothesis is not discharged.

## Why the abstract shortcut fails (paper proof, not a new Lean theorem)

In l2 on positive integers let D0=diag(1/n), a=(1/n), and W=a-perp.
W is a proper closed hyperplane. If y is orthogonal to D0 W, self-adjointness
gives D0 y in span(a), so y is constant; the only constant l2 sequence is zero.
Thus D0 W is dense. For any c>0 set B0=(I+D0)/c and R0=diag(1/(n+1)).
B0 is positive and boundedly invertible, R0=B0 inverse D0/c, and
D0 W is contained in W+B0 W. Hence D0 W, R0 W and W+B0 W are all dense,
although W is proper. D0 and R0 are compact and injective.

This refutes the general operator-theoretic inference to full totality.
It does not refute totality of the arithmetic residue family.
It shows that arithmetic information or a source bound is still needed.

## Research agenda

1. Open, highest priority: produce finite legal v_j with Dv_j -> D1 and
   bounded source norms, or a bounded cofinal subsequence.
   QReciprocalTargetLift.riemannHypothesis_of_bounded_D_target is the consumer.
2. Open: prove a complete O(alpha_j) regularized cost for explicit cofinal
   cutoffs and positive alpha_j -> 0. Retain the parameter-change correction
   and infinite tails when using inverse-Gram minimizers.
   QReciprocalCostEquivalence.mem_closure_iff_regularized_cost is the exact
   closure equivalence.
3. Open: force the actual residual 1-Pi_V 1 to vanish, preserving
   ||1-Pi_VN 1||^2=1-b_N^T G_N inverse b_N and its limiting remainder.
4. Open: prove density leakage (I-Pi_V)B|V is zero from arithmetic.
   This is equivalent to V=H, rather than a free consequence of measure change.
5. Open: prove saturation for Dg_2, then prove any conductor propagation needed.
   The exact existing limit is pi^2/64 minus ||Dg_2-Pi_V Dg_2||^2.
6. Open: combine CRT interpolation with uniform complete Q-tail/source-energy
   estimates; neither finite-coordinate agreement nor profinite continuity
   alone supplies a bounded legal lift.
7. Translation chain completed in the continuation, with the published analytic
   provider explicit. The provider itself remains Open in Lean. The arithmetic
   equivalence 1 in V iff V=H is now formalized without that provider.

## Verification evidence

Focused acceptance:
- Job job_W7uADcOlCs7XcldAS62aR12J-Z6wNsQw
- Bazel --config=buildbuddy //RiemannResearch/RH:QDensityClosureTransfer
- verified=true, exit_code=0, server verification duration 61.101 seconds.
- Includes both new modules and all transitive imports.
- Closure module SHA256: 158e0c1076ce2191ca425002a5b4f1c48940a8548afefabac56b56be29d1549c.
- Full project acceptance and exact publication commit are provided by the
  required server checkpoint; a focused check is not that publication result.

The new source introduces no unproved domain-specific axioms or proof placeholders.
Its RH declarations retain the exact open hypotheses displayed above.
The companion PDF/TeX distinguishes formal declarations from paper arguments.

## Literature context

Luis Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the Riemann
hypothesis, Rend. Lincei Mat. Appl. 14 (2003), 5-11.
https://arxiv.org/abs/math/0202141

Luis Baez-Duarte, Arithmetical Aspects of Beurling's Real Variable Reformulation
of the Riemann Hypothesis (2000).
https://arxiv.org/abs/math/0011254

These references motivate target approximation and the L2 requirement;
they do not supply the open bounded-lift or cost estimates above.
