# Canonical CRT lifts at prime-power admissions

7 November 2026 — continuation approved for publication after review.

**11 November 2026 formalization update.** Section 3's actual screened
coordinate assembly is now implemented in `QCRTScreenedCoordinates.lean`:
complete physical Gram inverses, old/full/Schur difference-test inverses,
screened source, canonical synthesis, and exact signed energy. See
[the declaration and verification map](ScreenedCRTCoordinateAssembly20261111.md).
The quantitative canonical growth and reciprocal-tail obligations remain open.

**Conclusion.** The exact canonical source and nonsymmetric block equations can be derived without a canonical escape-energy assumption. They retain a newly visible old-leakage term and the signed old/new correlation. The existing bounds do not yet control the resulting canonical norm increase. A uniform summable-depth bound for the actual canonical sequence is neither proved nor refuted here. There is an explicit obstruction to obtaining it from periodicity, old-cell orthogonality, and small unnormalized divisor moments alone.

## 1. Definitions and provenance

Work in the complete space \(L^2(Q)\), with \(Q(n)=1/(Z n^2)\), \(n\ge1\), and \(Z=\zeta(2)\). Put
\[
g_d(n)=\{n/d\},\quad a_d(n)=1_{d\mid n},\quad
V_L=\operatorname{span}\{g_d:d\mid L,\ d>1\}.
\]
Let \(C_L=\operatorname{span}\{a_d:d\mid L\}\), \(T_L=P_{C_L}\), and \(h_L=1-a_L\).
The **actual** canonical lift is the unique \(F_L\in V_L\) with
\(T_LF_L=h_L\). Write \(r_L=F_L-h_L\) and \(E_L=\|F_L\|_Q^2\).
All formulas below use the entire infinite physical tail.

The source definitions and existing theorems were read from:
- [QCRTFiniteCollocation.lean](https://github.com/Cnoack3/RiemannResearch/blob/8f11fcee05b12c462bb0538be8839bb6aa7df5a5/RiemannResearch/RH/QCRTFiniteCollocation.lean);
- [QCRTNestedCutoffs.lean](https://github.com/Cnoack3/RiemannResearch/blob/8f11fcee05b12c462bb0538be8839bb6aa7df5a5/RiemannResearch/RH/QCRTNestedCutoffs.lean);
- [November 7 machinery audit](https://github.com/Cnoack3/RiemannResearch/blob/8f11fcee05b12c462bb0538be8839bb6aa7df5a5/RiemannResearch/RH/CanonicalUpdateMachineryAudit20261107.md);
- [sharp sampler memorandum](https://github.com/Cnoack3/RiemannResearch/blob/8f11fcee05b12c462bb0538be8839bb6aa7df5a5/RiemannResearch/RH/CRTCollocationStabilityResearch20261107.md).

This is an independently derived continuation of the user's requested investigation, not a novelty claim. The retained Lean workspace is based on commit 8f11fcee. GitHub main was observed at 27d47559; publication must validate any integration with newer main.

## 2. Exact source at an admission \(m=p^k\)

Let \(L=\operatorname{lcm}(1,\ldots,m-1)\), \(N=pL\), and
\[
\delta=L^{-2}-N^{-2},\qquad \Delta F=F_N-F_L,\qquad \Delta r=r_N-r_L.
\]
Write \(L=p^{k-1}R\), with \((p,R)=1\). The new trial atoms are all
\(g_{p^k e}\), \(e\mid R\); an admission is generally a block, not one atom.

The exact finer-cell source is
\[
b_{L,N}=h_N-T_NF_L=(h_N-h_L)-T_Nr_L,\qquad T_N\Delta F=b_{L,N}.
\]
Old leakage is orthogonal to \(h_L,h_N\). Consequently
\[
\boxed{\|b_{L,N}\|_Q^2=\delta+\|T_Nr_L\|_Q^2.}
\]
Thus the small target increment does not give a small total source.

For every \(d\mid N\), the raw divisor source is
\[
\boxed{
\langle h_N-F_L,a_d\rangle_Q
=\operatorname{lcm}(L,d)^{-2}-N^{-2}-\langle r_L,a_d\rangle_Q.}
\]
It equals \(\delta\) on old divisors \(d\mid L\). On a new divisor
\(d=p^k e\), \(\operatorname{lcm}(L,d)=N\), so it equals
\(-\langle r_L,a_d\rangle_Q\). The row \(d=N\) is identically zero.

For the difference operator \(\mathcal Df(n)=f(n)-f(n-1)\), with \(f(0)=0\),
\(\mathcal Dg_d=d^{-1}1-a_d\). The square difference-test system has source
\[
s_d=\langle h_N-F_L,\mathcal Dg_d\rangle_Q
=\frac{\delta}{d}-
 [\operatorname{lcm}(L,d)^{-2}-N^{-2}]
 +\langle r_L,a_d\rangle_Q.
\]
In particular,
\[
\boxed{s_d=(d^{-1}-1)\delta\quad(d\mid L,\ d>1),}
\qquad
\boxed{s_{p^ke}=\frac{\delta}{p^ke}+\langle r_L,a_{p^ke}\rangle_Q.}
\]
The positive leakage sign in the difference-test source is essential.

Cauchy–Schwarz gives the unconditional bound
\[
|\langle r_L,a_d\rangle_Q|^2\le \frac{\|r_L\|_Q^2}{d^2}.
\]
Hence, for the new raw difference source,
\[
\sum_{e\mid R}|s_{p^ke}|^2
\le \frac{2Z}{p^{2k}}\bigl(\delta^2+\|r_L\|_Q^2\bigr).
\]
The individual Cauchy–Schwarz estimate and this finite-sum corollary are now
formalized in `QCRTNestedCutoffs.lean`, culminating in
`signed_difference_update_source_prime_power_sum_sq_le`. The specialization
uses `L = p^k R`, `N = p^(k+1) R`, `p ≥ 2`, `R > 0`, `L ≥ 2`, and
`Nat.Coprime p R`; primality is not needed. The exact positive leakage source
is retained in `signed_difference_update_source_prime_power`. The theorem
`signed_difference_update_source_new_scaled` records `d*s_d = delta + d*<r_L,a_d>`.
This is a bound in unnormalized row coordinates. Since `||a_d||_Q = 1/d`,
rescaling the divisor tests removes the apparent depth gain; no canonical
response or growth bound follows from this corollary alone.

## 3. Screened Gram and collocation equations

Let \(U\) be the synthesis map of the old atoms and \(V\) that of the new atoms.
Use the complete-Q physical Gram matrices
\[
G=U^*U,\quad B=U^*V,\quad W=V-UG^{-1}B,\quad
H=W^*W=V^*V-B^*G^{-1}B.
\]
Then \(U^*W=0\). The old and new atom families are independent: their finite differences distinguish their divisor coefficients. Thus these physical Gram inverses are legitimate finite-stage inverses.

Write \(\Delta F=Ux+Wy\), and \(F_L=Uc\).
With \(\phi=(U,W)\), define the generally **nonsymmetric** matrix
\[
A_{ij}=\langle\phi_j,\mathcal D\phi_i\rangle_Q,\qquad
\beta_i=\langle h_N-F_L,\mathcal D\phi_i\rangle_Q.
\]
The new part of \(\beta\) is the raw new source minus
\((G^{-1}B)^*\) times the old source. The equations are
\[
A_{00}x+A_{01}y=\beta_0,\qquad
A_{10}x+A_{11}y=\beta_1.
\]
The checked strict-accretivity argument gives invertibility of the old and full finite collocation operators. Therefore their Schur complement is invertible, and exact elimination gives
\[
K=A_{11}-A_{10}A_{00}^{-1}A_{01},\quad
\sigma=\beta_1-A_{10}A_{00}^{-1}\beta_0,
\]
\[
\boxed{y=K^{-1}\sigma,\qquad
x=A_{00}^{-1}(\beta_0-A_{01}y).}
\]
No transpose identification of \(A_{01}\) and \(A_{10}\) is made.

The physical Gram equation is
\[
Hy=(\langle\Delta F,W_i\rangle_Q)_i.
\]
Its right-hand side is an unknown response pairing, not the known difference-test source \(\sigma\). Replacing one by the other would be circular.

The exact energy update is
\[
\boxed{E_N-E_L=2c^*Gx+x^*Gx+y^*Hy.}
\]
Equivalently,
\[
\boxed{E_N-E_L=\delta+\|\Delta r\|_Q^2
 +2\langle r_L,\Delta r\rangle_Q.}
\]
This last identity, the equivalence with any proposed multiplicative budget, and generic nonsymmetric block elimination are Lean-checked. The coordinate assembly above is a paper derivation from these finite systems.

## 4. What the existing coercivity actually supplies

The full update satisfies the new checked identity
\[
\|\mathcal D\Delta F-b_{L,N}\|_Q^2+
 \bigl(\|\Delta F\|_Q^2-\|S\Delta F\|_Q^2\bigr)
=\delta+\|T_Nr_L\|_Q^2,
\]
where \(S\) is the anchored physical shift. This is the existing accretive machinery applied to the actual canonical update. Its contraction defect has the stronger-decaying physical weight; it does not bound \(\|\Delta F\|_Q^2\) uniformly.

The bound \(b^*G_{\rm head}^{-1}b\le4Z(1+\log H_0)^2\|b\|_2^2\) in QSquarefreeSchurCoercivity concerns a screened squarefree physical-head family. The new canonical block includes prime powers, and its response is governed by \(K^{-1}\). No theorem identifying those operators or bounding the required transfer was found.

Carry identities preserve their signed coefficients. Coprime Bezout carries do not perform the repeated admission of an already present prime. Changing Bezout representatives leaves the physically screened vector unchanged. Thus these results furnish neither a bound on \(K^{-1}\sigma\) nor the required signed old-refit term \(2c^*Gx\).

An elementary finite-dimensional check illustrates the distinction. Let old trial space be \(\mathbb Re_1\), new trial space be \(\operatorname{span}(e_1,e_2+A e_3)\), and test spaces be \(\mathbb Re_1\subset\operatorname{span}(e_1,e_2)\). The targets are \(e_1\) and \(e_1+\varepsilon e_2\). The new canonical lift is \(e_1+\varepsilon(e_2+A e_3)\), whose energy increase is \(\varepsilon^2(1+A^2)\). Yet the screened physical inverse Gram is \(1/(1+A^2)\le1\). A bound on that inverse Gram and a small test source do not bound the oblique lift. Wolfram checked the symbolic identities; this example is not asserted to model the actual CRT coefficients.

## 5. Exact refinement geometry and an arithmetic obstruction

This section is a proved paper argument, not yet a Lean formalization.

At \(L=aR\), where \(a=p^{k-1}\) and \((p,R)=1\), only the old cells
\[
E_e=\{\gcd(n,L)=ae\},\qquad e\mid R,
\]
split on passing to \(N=pL\). Put
\(B_e=\{\gcd(n,N)=pae\}\), \(\rho_e=Q(\gcd(j,R)=e)\).
Then
\[
Q(E_e)=a^{-2}\rho_e,\qquad Q(B_e)=p^{-2}Q(E_e).
\]
These masses follow by writing \(n=aj\) and then \(j=p\ell\).
The orthogonal cell innovation
\(\eta_e=1_{B_e}-p^{-2}1_{E_e}\) has
\[
\|\eta_e\|_Q^2=Q(E_e)p^{-2}(1-p^{-2}).
\]
For every \(r\perp C_L\),
\[
\boxed{\|T_Nr\|_Q^2=
 \sum_{e\mid R}\frac{|\langle r,1_{B_e}\rangle_Q|^2}
 {Q(E_e)p^{-2}(1-p^{-2})}.}
\]
For canonical leakage, the \(e=R\) term vanishes. The reciprocal cell mass in this exact screened **test** Gram cancels naive small-mass gains.

There is a uniform counterexample to generic depth decay even at the genuine \(2^k\) LCM admissions. For \(k\ge2\), put
\(a=2^{k-1}\), \(L=\operatorname{lcm}(1,\ldots,2^k-1)=aR\).
Here \(R\ge3\) is odd. Let
\[
w_i=Q(n\equiv i\pmod R),\qquad
u(j)=w_2\,1_{j\equiv1\pmod R}-w_1\,1_{j\equiv2\pmod R},
\]
\[
r(n)=
\begin{cases}a\,u(n/a),&a\mid n,\\0,&a\nmid n.\end{cases}
\]
Then:
1. \(r\) is \(L\)-periodic and vanishes on multiples of \(L\);
2. \(r\perp C_L\), since its only nonzero old gcd cell is \(a\), where its mean is zero;
3. \(\|r\|_Q^2=w_1w_2(w_1+w_2)\le1/4\).

Let \(v_i=Q(n\equiv i\pmod R,\ 2\mid n)\) and
\(b=w_2v_1-w_1v_2\). We have
\[
w_1\ge Z^{-1},\quad w_2\le1-Z^{-1},\quad
v_1\le(1-Z^{-1})/4,\quad v_2\ge1/(4Z).
\]
The elementary integral bound
\(Z=1+1/4+\sum_{n\ge3}n^{-2}\le7/4\) implies
\[
b\le(1-2/Z)/4\le-1/28.
\]
For \(\rho=Q(\gcd(n,R)=1)\le1\), the refinement formula gives
\[
\boxed{\|T_{2L}r\|_Q^2=\frac{16b^2}{3\rho}
 \ge\frac1{147}\ge\frac4{147}\|r\|_Q^2.}
\]
After normalizing \(r\), the visible energy remains bounded below independently of \(k\). Thus these three structural leakage properties cannot imply any uniformly depth-decaying factor for the newly revealed energy.

**Scope:** this \(r\) is not asserted to satisfy \(h_L+r\in V_L\), and hence is not asserted to be the actual canonical leakage. Its purpose is to identify the extra arithmetic information a proof must use. It does not refute a canonical-specific bound.

## 6. Complete-tail experiments and certified finite counterexamples

For an \(L\)-periodic function, the exact residue weights are
\[
W_L(j)=\frac{\psi_1(j/L)}{ZL^2},\qquad 1\le j\le L,
\]
where \(\psi_1\) is trigamma. These include all physical integers congruent to \(j\), not a head truncation.

Solving the normalized gcd-cell system gives the following floating-point exploration. Values beyond \(L=60\) are not interval certificates.

| Admission \(m\) | \(L_m\) | \(E_{L_m}\) | \(m(E_{L_m}/E_{L_{m-1}}-1)\) |
|---:|---:|---:|---:|
| 2 | 2 | 0.750000000 | — |
| 3 | 6 | 1.009917462 | 1.039669849 |
| 4 | 12 | 1.068712676 | 0.232871361 |
| 5 | 60 | 1.053173736 | -0.072699332 |
| 7 | 420 | 1.036793041 | -0.108875545 |
| 8 | 840 | 1.046195256 | 0.072548438 |
| 9 | 2520 | 1.029984673 | -0.139453170 |
| 11 | 27720 | 1.029076489 | -0.009699192 |
| 13 | 360360 | 1.032628803 | 0.044875266 |
| 16 | 720720 | 1.033448814 | 0.012705609 |

The normalized cell matrix condition number reaches about \(6.43\times10^4\) at \(m=16\); the largest coefficient is about 189.76. Small observed energy does not bound coefficients or establish an asymptotic rate.

Wolfram independently recomputed the full-tail energies at \(L=2,6,12,60\) at 50-digit working precision. A separate standard-library Python calculation certifies rational enclosures without trigamma or floating-point assumptions:
\[
1.00991745<E_6<1.00991748,\quad
1.06871260<E_{12}<1.06871275,\quad
1.05317316<E_{60}<1.05317431.
\]
At the \(12\to60\) update, the same certificate gives
\[
0.03737990<\|\Delta r\|_Q^2<0.03738005,
\]
\[
-0.05958572<2\langle r_{12},\Delta r\rangle_Q<-0.05958544.
\]
The exact target increment is \(1/150\). The energy therefore decreases despite the positive leakage increment. Conversely \(E_6>1=(1+1/3)E_2\), so the literal choice \(C=1\) fails at the first nontrivial update. Neither observation disproves an eventual estimate with some larger constant \(C\).

Certificate method: for each residue progression, sum \(K=16384\) terms using outward dyadic rounding at 80 bits. Bound the remaining unnormalized tail between
\(1/[L(j+KL)]\) and that value plus \(1/(j+KL)^2\). Solve the midpoint matrix over exact rational numbers and enclose coefficient errors by a Neumann perturbation bound. Enclose all quadratic energies and correlations with rational interval arithmetic. The script asserts every displayed sign and comparison; these are independently checked calculations, not Lean certificates.

## 7. What would close this route

For the actual canonical sequence, the precise one-step target remains
\[
\delta+\|\Delta r\|_Q^2+2\langle r_L,\Delta r\rangle_Q
 \le \frac{C}{p^k}E_L.
\]
This is exactly equivalent to \(E_{pL}\le(1+C/p^k)E_L\).
The new Lean equivalence exposes the full unresolved inequality.

If such a bound holds beyond finitely many admissions with one fixed \(C\), multiplying it gives polylogarithmic energy growth. The higher-depth budget is explicitly finite:
\[
\sum_p\sum_{k\ge2}p^{-k}
=\sum_p\frac1{p(p-1)}
\le\sum_{n\ge2}\frac1{n(n-1)}=1.
\]
The depth-one contribution has the classical \(O(\log\log M)\) bound. The resulting polylogarithmic energy, combined with the repository's checked
\(D_t(L_M)=O_t(M^{1-t}/\log M)\), would force the required product to zero for every fixed \(1<t<2\).

The sharp sampler result \(S_t/D_t=\Theta_t(M^{t-2})\) improves the Mellin detector correction to \(1+O(M^{\Re s-1})\). It supplies no estimate for \(x,y,K^{-1}\sigma\), or the signed norm increase above. Making the sampler smaller cannot replace this missing bound.

A weaker sufficient target is a bound \(o(\log M)\) for the sum of positive relative canonical energy increments up to \(M\). It could allow irregular individual admissions. This also remains an open, canonical-specific obligation.

**Next proof obligation:** estimate the actual nonsymmetric Schur response and its signed refit against \(F_L\), using the legal affine condition \(F_L=h_L+r_L\in V_L\). The refinement counterexample shows why the more general leakage properties cannot provide this information. No canonical escape-energy hypothesis was assumed, and RH is not proved.

## 8. Repository changes and verification

- Extend QCRTNestedCutoffs.lean with 14 theorems and one source definition: exact growth, budget equivalence, finer conditional source and its norm, divisor and difference source equations, actual difference-test matching, contraction-defect identity, and the raw divisor-moment bound.
- Add LinearAlgebra/ObliqueBlockElimination.lean with the nonsymmetric block-elimination theorem; export it from RiemannResearch.lean.
- Append an explicitly scoped status entry to THEOREM_CATALOG_CRT_COLLOCATION_20261107.md.
- Add this research note. Include two reproducible Python scripts as review-package attachments; they are not part of the publication patch.

Both saved owning modules were built successfully and all 15 new theorems were axiom-audited in server job `job_ujFCPKlblpVJB_6DH7Fzyzfv96rawsgQ` (reported verification duration 15.547 seconds). Every audited theorem used only `propext`, `Classical.choice`, and `Quot.sound`. This is targeted module verification, not a final checkpoint or a whole-repository validation.

The fresh-workspace request timed out; reopening the retained workspace succeeded. Opening round-trip duration was not instrumented. The final job's reported submission/start timestamps show less than 0.01 seconds of queue delay; status polling respected the returned 30-second minimum. Request and polling latency are separate from the reported verification duration.

The exact saved Lean source contains no `sorry`, `admit`, project-local axiom, or unsafe declaration. The paper refinement obstruction and the coordinate Schur assembly are not claimed as kernel-checked. The rational certificate and higher-stage floating-point experiment have separate evidence files. The user approved publication after reviewing the proposed patch. Publication must pass the Lean server checkpoint, including validation of any integration with newer main.
