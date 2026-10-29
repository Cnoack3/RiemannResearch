# Squarefree finite-head dimension, dual basis, and exact energy certificates

29 October 2026. Continuation of commit 35ef0f4, developed on main at
ab26627255f04e6e1fe6ba7a0dae2a27c5bdb350.

## Result and scope

The general attainable-head dimension, the explicit triangular constraint basis,
and the exact finite-head annihilator classification are now formalized.
A separate module proves an exact complete-Q energy certificate from the
constraint at 25. A third module proves that a uniform projected finite-head
dual estimate is equivalent to vanishing of the actual squarefree residual.
**The existence of that uniform estimate remains Open. No RH proof is claimed.**

The repository already contained QSquarefreeHeadCompression.physical_rank for
finite dictionaries containing all required small squarefree conductors and
a conductor above the head. The new dimension module supplies the unrestricted
legal-head statement for every H, including H = 0, constructs the explicit
constraint basis, and identifies its entire finite-dimensional annihilator.
It uses the existing physicalMap and exact_head_iff_radicalCompatible.

## 1. Triangular basis and dimension

Let
\[
\mathcal S_H=\{n:1\le n\le H,\ n\text{ squarefree}\},\qquad
\mathcal N_H=\{n:1\le n\le H,\ n\text{ not squarefree}\}.
\]
The physical head is (f(1),...,f(H)), with the additional coordinate f(0)
fixed to zero. For m in \(\mathcal N_H\), define
\[
\ell_m(f)=f(m)-f(m-1)-f(\operatorname{rad}m)
                         +f(\operatorname{rad}m-1).
\]
Since \(\operatorname{rad}m<m\), the row has its final coefficient 1 at
coordinate m. Ordered by m, the submatrix on nonsquarefree columns is lower
triangular with unit diagonal. The formal declarations
constraintRow_point_diagonal and constraintRow_point_above state these pivots
and zeros explicitly.

There is also an exact biorthogonal construction. Put
\[
s_n(k)=\mathbf1_{\{n\le k\}},\qquad 0\le k\le H,\quad n\in\mathcal N_H.
\]
Its jump at k is \(\mathbf1_{\{k=n\}}\). The radical of m is squarefree, so
\[
\boxed{\ell_m(s_n)=\delta_{mn}.}
\]
Consequently the constraint map \(C_Hf=(\ell_m(f))_{m\in\mathcal N_H}\)
has the explicit right inverse \(b\mapsto\sum_m b_ms_m\). Its rank and the
dimension of the row span both equal \(|\mathcal N_H|\).

The existing radical-compatible interpolation theorem identifies
\(\ker C_H\) with precisely the heads of finite legal squarefree combinations.
Rank-nullity therefore gives
\[
\boxed{\dim V_H=H-|\mathcal N_H|=|\mathcal S_H|.}
\]
The formulation includes H = 0 without an extra hypothesis. Reinstating the
coordinate f(0)=0 does not change the dimension. Squarefree 1 supplies the
free initial jump f(1)-f(0); it does not introduce conductor 1.

The given examples follow by counting: dimensions 3, 7, and 13 for
H = 4, 10, and 20. These examples are consequences of the theorem, not its proof.

For every linear functional l annihilating V_H, there is the explicit expansion
\[
\boxed{l=\sum_{m\in\mathcal N_H}l(s_m)\ell_m.}
\]
Indeed, \(f-\sum_m\ell_m(f)s_m\) lies in \(\ker C_H\).
Together with biorthogonality this proves spanning, independence, and uniqueness.
The Lean object constraintBasis is a basis of the row span, and
constraintSpan_iff_annihilates identifies that span with the full annihilator.
Finally, constraintRow_physicalMap identifies these rows with the previously
constructed Hilbert vectors radicalWitness m through the exact inner product.
No claim about density of their infinite union is used.

## 2. Exact finite-window energy bound: paper-level general formula

This subsection proves the general matrix consequence on paper; its full
weighted-window assembly has not been added as a Lean theorem in this work.
The specific certificate in section 3 is checked in Lean.

Fix an attainable head v through H and K > H. Retain the nonsquarefree
constraints with H < m <= K. Split their matrix into the old head columns
and the remaining columns:
\[
C=[C_{\rm head}\ D],\qquad b=-C_{\rm head}v.
\]
The rows indexed by m <= H are already satisfied. The same triangular pivots,
all lying in the tail columns, show that D has full row rank.

For arbitrary positive weights w_n, put
\[
W=\operatorname{diag}(w_{H+1},\ldots,w_K),\quad
G=DW^{-1}D^{\mathsf T},\quad
z_*=W^{-1}D^{\mathsf T}G^{-1}b .
\]
The matrix G is positive definite: for nonzero u,
\(u^{\mathsf T}Gu=\|W^{-1/2}D^{\mathsf T}u\|^2>0\).
We have \(Dz_*=b\), and for every feasible z,
\[
z_*^{\mathsf T}W(z-z_*)
=b^{\mathsf T}G^{-1}D(z-z_*)=0.
\]
Thus, for any compatible Hilbert vector F with the prescribed head,
\[
\boxed{
\|F\|_w^2=
\sum_{n=1}^H w_nv_n^2+
b^{\mathsf T}G^{-1}b+
\|F|_{(H,K]}-z_*\|_W^2+
\sum_{n>K}w_nF(n)^2.}
\]
This is an exact identity before either nonnegative remainder is discarded.
The bound is sharp for the finite-window relaxation. The optimized finite
head is compatible and therefore has a legal extension by finite interpolation.
That extension's complete tail energy is not controlled by this argument.

The same construction for approximation of a finite target t yields the
squared-distance contribution
\[
(C_Kt)^{\mathsf T}
(C_KW_K^{-1}C_K^{\mathsf T})^{-1}(C_Kt).
\]
For the target with f(0)=0 and f(n)=1 for n>=1, all radical constraints vanish.
Consequently finite constraints alone give zero for this target-error test.
They can still give positive extra energy when an initial head is prescribed.

## 3. A checked complete-Q certificate beyond the head

Suppose F is radical-compatible and F(1)=...=F(4)=1.
The relation at 25, whose radical is 5, gives
\[
x+y-z=1,\qquad x=F(5),\quad y=F(24),\quad z=F(25).
\]
The exact weighted completion is
\[
\frac{x^2}{25}+\frac{y^2}{576}+\frac{z^2}{625}
=\frac1{1226}
+\frac{(x-25/1226)^2}{25}
+\frac{(y-576/1226)^2}{576}
+\frac{(z+625/1226)^2}{625}.
\]
Write \(E_{\rm omitted}(F)=\sum_{n\notin\{1,2,3,4,5,24,25\}}Q(n)F(n)^2\),
with the physical zero coordinate contributing zero. Lean proves both its
nonnegativity and the complete identity
\[
\boxed{
\|F\|_Q^2=
\frac1{\zeta(2)}
\left[
\frac{125737}{88272}
+\frac{(F(5)-25/1226)^2}{25}
+\frac{(F(24)-576/1226)^2}{576}
+\frac{(F(25)+625/1226)^2}{625}
\right]+E_{\rm omitted}(F).
}
\]
Therefore every legal exact-head vector, and indeed every compatible Hilbert
vector with that head, satisfies
\[
\boxed{\|F\|_Q^2\ge\frac{125737}{88272\,\zeta(2)}
=\frac1{\zeta(2)}\left(\frac{205}{144}+\frac1{1226}\right).}
\]
This strictly improves the head-only bound \(205/[144\zeta(2)]\).
It is not asserted to be the optimal complete constrained energy.

Lean also checks the analogous three-variable Pareto completion, with
denominators 30, 600, and 650 and centers 30/1280, 600/1280, and -650/1280.
Adding the Pareto head energy 4/5 gives the paper-level Hilbert consequence
\(\|F\|_P^2\ge205/256\). The full Pareto norm-and-omitted-series assembly has
not been formalized here; only its algebraic completion is in the new module.

More generally, for squarefree d>=2 and an exact head through d-1, the
constraint at d^2 gives \(F(d)+F(d^2-1)-F(d^2)=1\). The same paper calculation
yields
\[
\|F\|_Q^2\ge\frac1{\zeta(2)}
\left(\sum_{n=1}^{d-1}\frac1{n^2}+\frac1{2d^4-d^2+1}\right),
\qquad
\|F\|_P^2\ge\frac{d-1}{d}+\frac1{2d^4+d^2+d}.
\]
These general-d applications are not new Lean theorems in this checkpoint.

## 4. The precise infinite-dimensional estimate

Let \(S=\overline{L_{\rm sf}}\), P_S its Q-orthogonal projection, and
\(r=\mathbf1-P_S\mathbf1\) the actual squarefree residual.

The new Lean module proves the exact equivalence
\[
\boxed{
r=0\quad\Longleftrightarrow\quad
\exists C\in\mathbb R\ \forall H\ \forall a\in Q{\rm Hilbert},\
|\langle\mathbf1,P_Ha\rangle_Q|^2
\le C\|P_SP_Ha\|_Q^2 .
}
\]
Here P_H is physical truncation through H, not legal projection.
If r=0, C=1 works by self-adjointness and Cauchy--Schwarz.
Conversely, apply the asserted estimate to a=r and let H tend to infinity:
\(P_Hr\to r\), \(P_SP_Hr\to P_Sr=0\), while
\(\langle\mathbf1,P_Hr\rangle\to\langle\mathbf1,r\rangle=\|r\|^2\).
The limiting inequality forces r=0.

**Open provider:** establish one constant C valid for every H and every test.
The formal equivalence does not establish this existence.

Equivalently, for
\(a_\lambda=\sum_{n=1}^H\lambda_n qSiteRiesz(n)\), the needed estimate is
\[
\left|\sum_{n=1}^H\lambda_n\right|^2
\le C\left\|P_S\sum_{n=1}^H\lambda_nqSiteRiesz(n)\right\|_Q^2 .
\]
The finite dual classification proves only the zero-denominator implication.
Neither a rank count nor a change to Ramanujan coordinates controls the
positive denominators uniformly.

The corresponding constructive target is a cofinal sequence of legal
exact-head vectors with uniformly bounded complete energies. The existing
residual_eq_zero_of_frequently_bounded_exact_head_energies already consumes
even a frequently bounded subsequence. In a sufficiently rich finite
dictionary, the established independent compressed observations give the
complete Gram minimum \(b_H^{\mathsf T}G_{H,D}^{-1}b_H\).
One needs a uniform upper bound on such complete minima along a cofinal
choice of dictionaries, not merely a finite-window lower bound.

A separate paper-level sufficient estimate, using the existing cofinal
legal sublinear-energy family, is
\[
\sup_j H_j\|T_{H_j}r\|_Q^2<\infty.
\]
Indeed the existing exact residual pairing and Cauchy--Schwarz give
\[
\|r\|_Q^4
\le
\bigl(H_j\|T_{H_j}r\|_Q^2\bigr)
\frac{\|\mathbf1-F_j\|_Q^2}{H_j}.
\]
The second factor tends to zero whenever \(H_j\to\infty\) and
\(\|F_j\|_Q^2/H_j\to0\). This scaled residual-tail bound remains Open;
finite-head dimension does not imply it.

## 5. Verification and next work

New modules and their central declarations:

- QSquarefreeHeadDimension.lean: constraintRow_step,
  constraintRow_linearIndependent, constraintBasis, constraintSpan_dimension,
  constraintMap_rank, legalHeads_eq_kernel, legalHeads_dimension,
  anchoredLegalHeads_dimension, anchoredLegalHeads_iff,
  constraintSpan_iff_annihilates, and constraintRow_physicalMap.
- QSquarefreeConstraintEnergy.lean: exact_head_four_energy_completion,
  legal_exact_head_four_energy_lower_bound, and both three-site completions.
- QSquarefreeUniformHeadDual.lean: exists_uniformHeadDualBound_iff.
  This is a conditional research reduction; its uniform-bound provider is Open.

The combined saved-import/snippet verification job
job_mLOmefq4koZlAR8uduZt9SS3Y_vM5QE9 succeeded with exit code 0.
The audited dimension, exact-energy, and uniform-dual-equivalence declarations
depend only on propext, Classical.choice, and Quot.sound. No placeholders or
new axioms are introduced. The final saved project and aggregate exports
must also pass the publication checkpoint; its terminal result and commit
are reported in the accompanying response.

Timing: the server reported 14.825 seconds for the combined check; recorded
queue delay was approximately 0.0014 seconds. The prescribed polling interval
was 30 seconds. These differ from client round-trip and polling wall time.
Workspace-opening duration was not independently instrumented and is not
being reported as Lean verification time.

Next useful work is to formalize the general weighted-window matrix identity,
then seek an arithmetic upper bound for the actual complete compressed Gram
minima. Increasing finite rank, calculating more examples, or truncating
infinite annihilators does not supply that upper bound.
