# Random legal-atom selection: exact projection comparison and RH obligations

Task date: 14 October 2026, America/New_York.
Source: the user's nested-projection and conductor-DPP question.
Continuation of QLegalDPPResearch20261014.md.

## Status and scope

The nested deterministic Pythagorean identity was already present in
Analysis/NestedProjectionEnergy.lean. This continuation reuses it.

New Lean results cover finite-law and Bochner-integral expectations, exact
equality conditions, deterministic extraction, actual full and squarefree
conductor selections, existing finite-DPP PMFs, two-stage wavelet vacancies,
and conditional consumers of Mathlib's RiemannHypothesis.

The Gram L-ensemble resolvent formulas below are proved analytically in this
record. They are not new Lean theorems in this continuation. In particular,
the Lean conductor-DPP theorems accept a supplied positive-contraction
matrix K; they do not silently assume that the resolvent kernel derived
below has been specialized and verified in Lean.

No legal-density provider, vanishing full optimizer error, RH proof,
Hilbert--Polya identification, or zeta-zero spectral identification is claimed.

## 1. Exact deterministic and expected identities

Let H=L²(Q), Q({n})=1/(zeta(2)n²), and x=1. Write V for a finite
legal atom span and W_J for the span of a subset of its conductors.
Set

\[
F=P_Vx,\qquad F_J=P_{W_J}x,\qquad
\delta=\|x-F\|^2,\qquad D_J=\|F-F_J\|^2.
\]

Since W_J is contained in V,

\[
x-F_J=(x-F)+(F-F_J),\qquad
x-F\perp V,\qquad F-F_J\in V.
\]

Therefore, with no omitted term,

\[
\boxed{\|x-F_J\|^2=\delta+D_J.}
\]

For any finite probability law w_J on conductor subsets, and equivalently
for any measurable random subset with that law,

\[
\boxed{\mathbb E\|x-F_J\|^2
=\delta+\sum_J w_J\|F-F_J\|^2.}
\]

There is no independence, determinantal, or arithmetic hypothesis in this
identity. Because there are finitely many subsets, both random variables
are integrable. The more general Lean Bochner-integral statement assumes
integrability of the gap explicitly; for finite measurable selection this
assumption is automatic.

The precise equality conditions are

\[
\begin{aligned}
\|x-F_J\|^2=\delta
&\iff F_J=F
\iff F\in W_J,\\
\mathbb E\|x-F_J\|^2=\delta
&\iff F\in W_J\quad\hbox{almost surely}\\
&\iff \forall J\ (w_J>0\Longrightarrow F\in W_J).
\end{aligned}
\]

Suppose the finite dictionary consists of distinct legal conductors, so its
atoms v_i are linearly independent, and F=sum_i c_i v_i is its unique
representation. Then these conditions become

\[
F\in W_J\iff \{i:c_i\ne0\}\subseteq J.
\]

Consequently equality in expectation is equivalent to

\[
\forall i\ (c_i\ne0\Longrightarrow \Pr(i\in J)=1).
\]

For a conductor DPP with marginal kernel K this is the exact condition
K(i,i)=1 on the support of c. This coefficient-support reformulation is an
analytic consequence of uniqueness; the Lean equality theorem is stated
directly as membership of the full projected vector in each supported span.

For any chosen y_J in W_J there is a further exact decomposition:

\[
\|F-y_J\|^2
=\|F-F_J\|^2+\|F_J-y_J\|^2.
\]

Thus projected fitting after selection always improves or preserves the
error of a specified coefficient truncation, and the improvement is the
displayed final square. It is not an unexplained loss term.

A finite weighted-average argument supplies a supported J with

\[
\|x-F_J\|^2\le\mathbb E\|x-F_J\|^2.
\]

This is a deterministic extraction result, not an algorithmic guarantee of
cheaply finding the witness. If all supported subsets have cardinality at
most k, the extracted witness also has at most k atoms. Both statements are
formalized, including the specialization to the existing finite DPP PMF.

## 2. Two different sampling spaces and an explicit connection

The existing law modeLaw(V) has sites r in the positive divisor-wavelet
labels. Site 1 represents qOne. It is not a conductor index.

A conductor-selection law instead has outcomes J contained in the finite
set of dictionary indices. In the full stage, index i in Fin n denotes
conductor i+2. In the new squarefree selection type, indices are restricted
to Squarefree(i+2); zero placeholders are not sampling sites.

For a positive-contraction matrix K on these conductor indices, the
existing finiteLaw constructor supplies an actual PMF on their subsets.
Its existing finiteLaw_isDPP theorem gives the determinantal inclusion
probabilities. The new full_conductorDPP_expected_error and
squarefree_conductorDPP_expected_error theorems instantiate the exact
expectation identity with this actual PMF.

One can connect the two spaces by a two-stage experiment:

1. Draw a conductor subset J with probabilities w_J.
2. Conditional on J, draw a wavelet configuration with law modeLaw(W_J).

Its constant-mode vacancy is exactly

\[
\begin{aligned}
\Pr(\text{wavelet site 1 vacant})
&=\sum_Jw_J\,\operatorname{modeLaw}(W_J)(\text{site 1 vacant})\\
&=\mathbb E\|x-F_J\|^2\\
&=1-p_V+\mathbb E\|F-F_J\|^2,
\end{aligned}
\]

where p_V is the existing constant-mode occupation of modeLaw(V).
The finite weighted-vacancy equalities are formalized for both legal
families. The joint two-stage measure is described here by its conditional
laws; no new joint-measure declaration is claimed.

In particular the mixed constant occupation cannot exceed p_V.
This is an explicit relationship between two laws, not an identification
of their sites. A mixture of DPPs is not asserted to be a DPP.

## 3. An actual conductor Gram L-ensemble

This section is an analytic investigation, separate from the verified
positive-contraction-parametrized specialization above.

Enumerate m distinct legal atoms v_1,...,v_m. Let A be their synthesis map,
G=A* A their positive-definite Gram matrix, b=A* x, and c=G^{-1}b. Here
every inner product is the actual Q inner product. No Pareto formula for b
is substituted.

For t>0 define a law directly on conductor subsets by

\[
\Pr_t(J)=\frac{t^{|J|}\det G_J}{\det(I+tG)},\qquad \det G_\varnothing=1.
\]

The principal-minor expansion of det(I+tG) proves normalization.
Every principal Gram determinant is positive. This is the standard
L-ensemble with L=tG, whose conductor marginal kernel is

\[
K_t=tG(I+tG)^{-1}=I-(I+tG)^{-1}.
\]

For the L-ensemble terminology and marginal-kernel relation, see
N. Tremblay, S. Barthelme, K. Usevich and P.-O. Amblard,
Extended L-ensembles: a new representation for Determinantal Point Processes,
arXiv:2107.06345v2, Sections 1.2 and 2:
https://arxiv.org/abs/2107.06345.
This reference supports the DPP construction and terminology. The
target-specific resolvent computation is supplied explicitly next.

Put R=(I+tG)^{-1}. Given J, use its exact least-squares coefficients

\[
c^{(J)}_J=G_J^{-1}b_J,\qquad
c^{(J)}_i=0\quad(i\notin J).
\]

The empty selection has zero coefficient vector. This produces a legal
approximation F_J=A c^{(J)} with at most |J| nonzero coefficients.

### Exact determinant proof of the mean captured energy

For an auxiliary real u, the matrix determinant lemma gives

\[
\det(G_J+u b_Jb_J^{\mathsf T})
=\det G_J\left(1+u b_J^{\mathsf T}G_J^{-1}b_J\right).
\]

Apply the principal-minor expansion also to G+u bb^T:

\[
\begin{aligned}
\sum_Jt^{|J|}\det(G_J+u b_Jb_J^{\mathsf T})
&=\det(I+tG+tu bb^{\mathsf T})\\
&=\det(I+tG)\left(1+tu b^{\mathsf T}R b\right).
\end{aligned}
\]

Equating the coefficients of u and dividing by det(I+tG) proves

\[
\boxed{\mathbb E_t\|F_J\|^2=t b^{\mathsf T}R b.}
\]

Because F_J is a projection, its error is \|x\|²-\|F_J\|². Hence

\[
\boxed{\mathbb E_t\|x-F_J\|^2
=\|x\|^2-tb^{\mathsf T}R b
=\delta+b^{\mathsf T}G^{-1}R b.}
\]

The last equality uses G^{-1}-tR=G^{-1}R, and keeps the entire
positive sampling penalty.

The same captured-energy formula holds for every b. Polarization, or
differentiation of this finite quadratic identity with respect to b, gives

\[
\boxed{\mathbb E_t[c^{(J)}]=tR b,\qquad
\mathbb E_t[F_J]=AtR b.}
\]

Thus the averaged subset coefficients are precisely ridge coefficients:

\[
tR b=(G+t^{-1}I)^{-1}b.
\]

They are not, at finite t, the full inverse-Gram coefficients.
There is an exact bias--variance refinement:

\[
\begin{aligned}
\|F-\mathbb E_tF_J\|^2&=b^{\mathsf T}G^{-1}R^2b,\\
\mathbb E_t\|F_J-\mathbb E_tF_J\|^2&=t b^{\mathsf T}R^2b,\\
b^{\mathsf T}G^{-1}R b
&=b^{\mathsf T}G^{-1}R^2b+t b^{\mathsf T}R^2b.
\end{aligned}
\]

These follow by expanding the mean, using E||F_J||² above, and the
commutation of G with R.

### Exact target spectrum and sample size

Let G u_l=lambda_l u_l be an orthonormal eigendecomposition with
lambda_l>0, and define alpha_l=(u_l^T b)/sqrt(lambda_l). Then

\[
\begin{aligned}
\|F\|^2&=\sum_l\alpha_l^2,\\
\delta&=\|x\|^2-\sum_l\alpha_l^2,\\
\mathbb E_t\|F-F_J\|^2
&=\sum_l\frac{\alpha_l^2}{1+t\lambda_l},\\
\mathbb E_t|J|
&=\sum_l\frac{t\lambda_l}{1+t\lambda_l}.
\end{aligned}
\]

This is a concrete sparse-selection mechanism: large Gram directions are
retained preferentially and their associated principal systems supply
the coefficients. Sparsity with a small target error needs arithmetic
information showing that most target energy lies in those directions.
The marginal kernel eigenvalues here describe this finite Gram sampler;
they are not identified with zeta zero ordinates.

For fixed m, letting t increase removes the selection penalty, but the
expected number of selected atoms tends to m. That observation alone
therefore gives no sparse growing-dictionary theorem.

For finite t every subset, including the empty set, has positive mass.
If F is nonzero the mean error is strictly greater than delta.
Likewise, a fixed-size L-ensemble on all k-element subsets of an independent
m-atom dictionary cannot attain delta when k<m and F is nonzero: the
intersection of all such subsets is empty. A fixed-size k-DPP need not
itself be an ordinary DPP with a correlation kernel; the generic finite
probability identities still apply to it.

There is also exact redundancy removal. If a dictionary has rank r<m,
choose an orthonormal basis of its span and form the r-by-m coordinate
matrix B. The projection conductor kernel

\[
K_{\rm basis}=B^{\mathsf T}(BB^{\mathsf T})^{-1}B
\]

samples r-element bases with probabilities
det(B_J)^2/det(BB^T). Every supported subset spans V, so equality holds.
For an independent legal dictionary r=m this kernel is I and the selection
contains every conductor. Target-specific exact compression is possible
when the full coefficient vector itself has smaller support.

## 4. Arithmetic conditions still needed for convergence to one

For each growing dictionary V_N, choose any law on its subsets and define

\[
S_N=\mathbb E\|P_{V_N}1-P_{W_{J_N}}1\|^2.
\]

The exact finite-stage equality is

\[
\mathbb E\|1-P_{W_{J_N}}1\|^2=(1-p_N)+S_N.
\]

Both summands are nonnegative, so

\[
\boxed{\mathbb E\|1-P_{W_{J_N}}1\|^2\longrightarrow0
\iff p_N\longrightarrow1\ \text{and}\ S_N\longrightarrow0.}
\]

This equivalence is Lean-verified for the full legal family and for the
actual squarefree conductor family. The separate conditional consumers
deduce Mathlib RH from the mean-square zero limit. They do not supply it.
No RH-to-Q-density converse is introduced.

For the Gram L-ensemble, the new selection condition is explicitly

\[
\boxed{
\sum_l\frac{\alpha_{N,l}^2}{1+t_N\lambda_{N,l}}\longrightarrow0.
}
\]

A quantitative sparse theorem additionally needs a cardinality estimate on

\[
\mathbb E|J_N|=\sum_l\frac{t_N\lambda_{N,l}}{1+t_N\lambda_{N,l}}.
\]

For example, a strict sparsity target k_N/m_N -> 0 requires proving that
the displayed sum is at most k_N while the target-weighted leakage
vanishes. A Gram eigenvalue count by itself does not locate target energy.
The separate arithmetic condition p_N -> 1 is still indispensable.

The existing equivalent squarefree targets include divergence of the
actual capacity and SquarefreeExactHeadTailBound: one uniform C such that
every head length M has a legal exact head with squarefree common period L
and

\[
\sum_{a=M+1}^{L}\frac{|1-F(a)|^2}{a^2}\le C.
\]

A potentially useful randomized sufficient provider would construct legal
squarefree exact heads almost surely and prove a uniform expected bound
on this entire one-period tail energy. Finite averaging would then supply
deterministic exact heads with the same uniform bound, discharging the
existing CRT closure criterion. Such an arithmetic expected-tail provider
has not been proved here.

A uniform tail bound yields closure and convergence of the complete
optimizers through the existing machinery; it does not by itself prove
mean-square convergence of the initially sampled trial functions.
For that stronger conclusion the exact sampling gap must also vanish.
Fixed-head agreement, prime independence, or wavelet-DPP occupation without
this energy control is not substituted for either missing estimate.

## 5. Formal declarations and verification

Four new exported modules:

- Analysis/RandomSubspaceProjection.lean: expected_error_eq,
  expected_error_eq_iff, integral_error_eq, integral_error_eq_iff,
  error_eq_iff_mem, expected_error_tendsto_zero_iff,
  exists_error_le_expected, and trial_gap_decomposition.
- Analysis/FiniteAtomSelection.lean: the literal selectedSpan, its finite
  dimensionality and inclusions, and selected_trial_error.
- Probability/DeterminantalAtomSelection.lean:
  finiteLaw_expected_atom_error, finiteLaw_expected_atom_error_eq_iff,
  finiteLaw_exists_good_atom_selection, and
  finiteLaw_exists_sparse_atom_selection.
- RH/QLegalAtomSelection.lean: full and actual-squarefree selections,
  exact individual and expected errors, equality conditions, the two
  convergence equivalences, finite-conductor-DPP specializations, explicit
  two-stage vacancy averages, and two conditional RH consumers.

Probability/FiniteDeterminantalLaw.lean adds finiteLaw_apply_toReal, the
exact real configuration mass already implicit in the existing PMF.

The generic nested residual identity is reused, not counted as new.
The L=tG kernel construction, resolvent means, coefficient-support
reformulation, and spectral sample-size tradeoff in Section 3 are analytic
proofs in this record, not newly checked Lean specializations.

The saved modules and seven central-declaration axiom inspections passed
job_GQ4fG-Ed695fkJy-1L92RKQimyPqubeo (exit code 0, verified true,
14.092 seconds). The final bridge specializations and four additional axiom
inspections passed job_AUqHp7LhY04S_SNgWv_gpespYcZ-VqW0 (exit code 0,
verified true, 16.676 seconds). Every inspected declaration depends only on
propext, Classical.choice and Quot.sound. The conditional zero-limit
hypotheses remain visible in the theorem types.

Publication additionally requires the separate final checkpoint source
audit and affected-module/reverse-dependent server validation. The final
checkpoint result and published commit are reported with the completion
message; these targeted checks are not represented as a whole-project build.
