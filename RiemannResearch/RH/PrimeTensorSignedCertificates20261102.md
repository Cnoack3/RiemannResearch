# Signed prime-tensor certificates: Lean continuation

Prepared for Christian Noack, 2 November 2026.

## Scope and status

This continuation formalizes the signed-tail geometry in section 4 of
PrimeTensorCRTResults20261102.md. It does not establish RH or claim that
every agenda in that memorandum is now formalized.

Base: 08ea57dfeda0c89e6f476fee055da6168a8158b2.
The coherent development candidates passed the user's Lean server. The
checkpoint carrying this file supplies final saved-source validation and
publication. The accompanying focused theorem catalog records the job IDs.

## Exact signed identities

Let H be a real inner-product space, let (e_k) be a finite orthonormal
family, let P project onto its span S, and put T=I-P. For columns a_i set

\[
K_{ij}=\langle Ta_i,Ta_j\rangle,\quad
G_{ij}=\langle a_i,a_j\rangle,\quad A_{ki}=\langle e_k,a_i\rangle .
\]

The newly checked entrywise identity is exactly

\[
K=G-A^\top A.
\]

For arbitrary anchors b_i in S, put F_c=sum_i c_i a_i and
B_c=sum_i c_i b_i. Then

\[
\|F_c-B_c\|^2
=\|TF_c\|^2+\sum_k|\langle e_k,F_c-B_c\rangle|^2 .
\]

In particular, if R is the Gram matrix of (a_i-b_i), then R-K is
positive semidefinite. This assertion holds for all signed c; it does
not replace c by its absolute value.

For a target h in S, the signed anchor certificate satisfies

\[
\underbrace{\sum_k|\langle e_k,h-F_c\rangle|^2+\|F_c-B_c\|^2}_{C_{\rm anc}}
=\|h-F_c\|^2+\sum_k|\langle e_k,F_c-B_c\rangle|^2 .
\]

Its excess over the true error is therefore exactly the retained anchor
bias. Choosing exact projection anchors eliminates that bias but leaves
the complete tail norm to be computed or estimated.

## Adaptive rows, blocks, and a valid PSD bound

For the complete column certificate

\[
C_{\rm col}
=\sum_k|\langle e_k,h-F_c\rangle|^2+
  \left(\sum_i|c_i|\|Ta_i\|\right)^2,
\]

adding one orthonormal analysis row cannot increase C_col, provided the
target was already in the old retained span. The proof first checks the
exact Pythagorean identity for every column. A two-coordinate triangle
inequality then pays for the new retained error with the decrease in the
column penalty. Iterating gives finite row additions.

For every u_i>0, Lean also proves

\[
c^\top Kc\le
 \left(\sum_i K_{ii}/u_i\right)\sum_i u_i c_i^2 .
\]

This is a genuine diagonal PSD majorant. The coefficient-dependent
absolute-value column estimate is not asserted to be a rank-one PSD
matrix majorant.

Grouping synthesized columns into blocks retains the exact covariance
inside each block. The penalty is the squared sum of block residual norms.
Merging two blocks cannot increase this penalty. No block covariance has
been inferred from a finite physical truncation.

## Actual Q specialization and RH

The arithmetic application uses the repository's actual QHilbert,
qResidue, qSynthesis, and normalizedDivisorWavelet objects, with
Q(n)=1/(zeta(2)n^2). The retained rows are distinct and include conductor
one, so the actual constant target is retained.

The new theorem
QTensorCertificate.anchoredCertificate_eq_error_add_bias is the complete-Q
version of the exact identity above. Its anchors must belong to the finite
analysis span. Its synthesis conductors are restricted to squarefree d>=2
in the research criterion.

The checked chain is

\[
\texttt{ArbitrarilySmallAnchoredCertificates}
\Longrightarrow 1\in\overline{\mathcal L_{sf}}^{L^2(Q)}
\Longrightarrow \texttt{RiemannHypothesis}.
\]

The second implication uses the existing checked capacity/Mellin consumer.
The first premise is OPEN. These finite geometric identities supply no
unconditional family with error tending to zero. They also supply no
subpolynomial exact-head energy estimate.

The published RH-to-squarefree-closure implication remains a separate
analytic formalization obligation. Bagchi, Remark 8, already proves the
equivalence on paper; the equivalent-weight discussion after Theorem 1
allows passage to Q. Balazard-de Roton's quantitative Mobius estimates
explicitly assume RH and cannot serve as an unconditional provider.

## Finite diagnostic, not an infinite-Q proof

Wolfram was used solely for exact polynomial identities and a finite
arithmetic experiment. On N={1,...,12}, with weights proportional to n^-2,
columns g_2,g_3,g_6, and gcd(N,6) cells, it returned R-K-B=0 exactly,
where B is the weighted outer-product sum of conditional anchor biases.
The residual Gram has rank two. For c=(1,-2,3), the finite conditional
quadratic tail was approximately 0.153443749864 and the anchored bound
0.183512246303. This uses Q conditioned on a finite set and is not a
certificate for the infinite Q measure. The general statements above
are proved in Lean independently of these numerical values.

## Next research obligations

1. Formalize that the actual gcd-anchored columns
   b_d(n)=g_d(gcd(n,M)) belong to the retained divisor-wavelet span, and
   identify their complete conditional means. This makes the abstract
   anchor certificate an explicit arithmetic certificate without adding
   an unproved membership hypothesis.
2. Preserve the signed cell differences and prove a cofinal arithmetic
   estimate that makes the complete anchored certificate tend to zero.
   Small universal cutoff probabilities alone do not do this.
3. Alternatively, provide zero lower logarithmic growth for the actual
   squarefree exact-head family and use the existing checked RH consumer.
   The known unconditional o(H) squared-energy estimate does not imply
   this subpolynomial condition.

The sharp summed gcd bound, its PNT asymptotic, the full Cesaro
counterexample, operator classification, and the published analytic
reverse implication remain outside this continuation's Lean scope.

## Sources

- User-supplied PrimeTensorCRTResults20261102.md, section 4: statements and
  proof strategy for signed anchors, adaptive rows, blocks, and diagonal
  majorants. These are standard projection/Cauchy-Schwarz arguments;
  no mathematical novelty is claimed.
- B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
  of the Riemann hypothesis, Proceedings of the Indian Academy of Sciences
  (Mathematical Sciences) 116 (2006), 137-146. Remark 8 and the discussion
  after Theorem 1 support the squarefree closure and equivalent-weight
  context. https://arxiv.org/pdf/math/0607733
- M. Balazard and A. de Roton, Sur un critere de Baez-Duarte pour l'hypothese
  de Riemann, International Journal of Number Theory 6 (2010), 883-903.
  The theorem and Propositions 1-3 support the explicitly RH-conditional
  quantitative benchmark, not an unconditional input.
  https://arxiv.org/pdf/0812.1689
