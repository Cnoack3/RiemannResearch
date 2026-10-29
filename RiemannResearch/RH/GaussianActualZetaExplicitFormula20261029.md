# The actual zeta explicit-formula connection for Gaussian signed matrices

29 October 2026.

## Result and verification status

This note completes the ordinary analytic proof connecting the arithmetic Gaussian
moment matrices in GaussianSignedMatricesResearch20261029.md to the actual
nontrivial zeros of the Riemann zeta function. It supplies the Fourier transform,
absolute convergence, contour argument, pole removal, real polynomial functional,
and actual-zero summability needed by the previously checked abstract localization
lemmas. All zeros and prime powers, with their multiplicities, are retained.

The principal unconditional identity is
\[
\boxed{
(\mathcal K_d(R,\tau))_{ij}
 =\sum_{\rho\in\mathcal Z}m_\rho[\rho(1-\rho)]^2
   (z_\rho-\tau)^{i+j}e^{-R(z_\rho-\tau)^2},
\quad z_\rho=\frac{\rho-\frac12}{i}.
}
\tag{T}
\]
Here \(R>0\), \(\tau\in\mathbb R\), \(d\ge2\), and \(0\le i,j\le d-2\).
The matrix on the left is defined entirely by the complete prime sum and
archimedean integral below.

This is an ordinary mathematical proof using classical unconditional analytic
properties of zeta, not new Lean verification. The remaining universal signed
lower bound is not proved: Section 8 proves precisely why that additional
assertion is equivalent to RH. No new zero-free region or RH proof is claimed.

## 1. Conventions and classical inputs

Let \(\mathcal Z\) be the set of distinct nontrivial zeros \(\rho=\beta+i\gamma\)
of zeta, and let \(m_\rho\) be their positive integer multiplicities. Every sum
over \(\mathcal Z\) below explicitly includes \(m_\rho\).

We use the following classical unconditional facts:

1. \(0<\beta<1\); the maps \(\rho\mapsto\overline\rho\) and
   \(\rho\mapsto1-\rho\) preserve zeros and multiplicities.
2. For a fixed constant \(C_0\),
   \[
   N_*(T):=\sum_{\substack{\rho\in\mathcal Z\\|\gamma|\le T}}m_\rho
      \le C_0(T+2)\log(T+2)\qquad(T\ge0).
   \]
   The usual Riemann--von Mangoldt theorem implies this deliberately weak bound.
3. The meromorphic completed function
   \[
   Z(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)
   \]
   satisfies \(Z(s)=Z(1-s)\), has simple poles at \(0,1\), and has exactly the
   nontrivial zeta zeros with their multiplicities as its zeros.
   The entire function \(\xi(s)=s(s-1)Z(s)/2\) has order one and its usual
   genus-one Hadamard product.
4. On \(\Re s>1\),
   \[
   \frac{\zeta'}{\zeta}(s)=-\sum_{n\ge2}\Lambda(n)n^{-s},
   \]
   absolutely. The gamma logarithmic derivative has its usual Stirling
   bounds on fixed vertical strips away from its poles.

There are no real nontrivial zeros: for real \(0<s<1\), the alternating
eta series is strictly positive (group consecutive pairs), while
\(\zeta(s)=\eta(s)/(1-2^{1-s})<0\). Thus any off-line zero has a conjugate
with positive ordinate.

These are established analytic inputs, not RH or a zero-density assumption.
The explicit formula itself is also classical. Section 4 gives its contour
derivation for the present test class, checking the non-even tests and all
normalizing constants directly.

Write
\[
w_\rho=z_\rho-\tau=\eta_\rho+i\delta_\rho,\qquad
\eta_\rho=\gamma-\tau,\quad\delta_\rho=\tfrac12-\beta.
\]
Then \(|\delta_\rho|<1/2\). Reflection
\(\rho\mapsto1-\overline\rho\) induces \(w_\rho\mapsto\overline{w_\rho}\)
with the same multiplicity.

For a real polynomial \(B\), set
\[
h_B(z)=B(z-\tau)e^{-R(z-\tau)^2},\qquad
g_B(u)=\frac1{2\pi}\int_{\mathbb R}h_B(t)e^{-itu}\,dt .
\]
The inverse convention is \(h_B(z)=\int_{\mathbb R}g_B(u)e^{izu}\,du\);
the integral converges for every complex \(z\).

## 2. Exact Fourier transform

Put
\[
F_R(u)=\frac{e^{-u^2/(4R)}}{\sqrt{4\pi R}},\qquad
G_k(R,u)=i^k\frac{d^k}{du^k}F_R(u).
\]
For \(B(w)=\sum_{k=0}^M b_kw^k\),
\[
\boxed{g_B(u)=e^{-i\tau u}\sum_{k=0}^M b_kG_k(R,u).}
\tag{2.1}
\]
Indeed, the substitution \(t=\tau+w\) reduces the transform to the Gaussian
integral, and differentiation under that integral inserts \(w^k\).
Every derivative is justified by a polynomial times an integrable Gaussian.

The generating identity
\[
\frac1{2\pi}\int_{\mathbb R}e^{-Rw^2+vw-iuw}\,dw
 =F_R(u)\exp\!\left(\frac{v^2}{4R}-\frac{iuv}{2R}\right)
\]
also gives the finite formula
\[
\boxed{
G_k(R,u)=F_R(u)k!\sum_{j=0}^{\lfloor k/2\rfloor}
 \frac{(4R)^{-j}(-iu/(2R))^{k-2j}}{j!(k-2j)!}.
}
\tag{2.2}
\]
For example,
\[
G_0=F_R,\quad G_1=-\frac{iu}{2R}F_R,\quad
G_2=\left(\frac1{2R}-\frac{u^2}{4R^2}\right)F_R.
\]
For real \(B\), \(g_B(-u)=\overline{g_B(u)}\).

## 3. Convergence and admissibility

For every fixed \(b>0\), \(x\in\mathbb R\), and \(|y|\le b\),
\[
|h_B(x+iy)|
 \le C_{B,b,\tau}(1+|x-\tau|)^M
       e^{Rb^2}e^{-R(x-\tau)^2}.
\tag{3.1}
\]
Thus \(h_B\) is entire and decreases faster than every inverse power uniformly
on each fixed horizontal strip. It satisfies the classical explicit-formula
test assumptions, including any strip wider than \(|\Im z|\le1/2\).

The Fourier formula gives
\[
|g_B(u)|\le C_{B,R}(1+|u|)^M e^{-u^2/(4R)}.
\tag{3.2}
\]
Consequently
\[
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
       (|g_B(\log n)|+|g_B(-\log n)|)<\infty.
\tag{3.3}
\]
For a direct comparison use \(\Lambda(n)\le\log n\).
The majorant
\((\log n)(1+\log n)^M n^{-1/2}e^{-(\log n)^2/(4R)}\)
is at most a constant times \(n^{-2}\) for sufficiently large \(n\).
This uses every integer as a majorant and includes every prime power.

Define
\[
\Omega(t)=\Re\psi\!\left(\tfrac14+\tfrac{it}{2}\right)-\log\pi,
\qquad\psi=\Gamma'/\Gamma.
\]
This is a smooth, real, even function with
\(|\Omega(t)|\le C\log(2+|t|)\). Therefore
\[
\int_{\mathbb R}|h_B(t)\Omega(t)|\,dt<\infty.
\tag{3.4}
\]

On the zero side,
\[
|h_B(z_\rho)|
 =|B(w_\rho)|e^{R(\delta_\rho^2-\eta_\rho^2)}
 \le C_B(1+|\eta_\rho|)^M e^{R/4}e^{-R\eta_\rho^2}.
\]
The shell \(k\le|\eta_\rho|<k+1\) contains at most
\(C_\tau(k+2)\log(k+3)\) zeros counted with multiplicity, by the bound for
\(N_*\). Hence
\[
\sum_\rho m_\rho|h_B(z_\rho)|
 \le C_{B,R,\tau}
       \sum_{k=0}^\infty(k+2)^{M+1}\log(k+3)e^{-Rk^2}<\infty.
\tag{3.5}
\]
No symmetric or conditionally convergent zero summation convention
is required for these Gaussian tests.

These estimates are locally uniform in \((R,\tau)\in(0,\infty)\times\mathbb R\).
They remain valid after any fixed number of parameter derivatives, with changed
polynomial majorants. This permits the finite linear combinations, regroupings
and differentiations used below. It does not assert domination independent of
\(R\) as \(R\to\infty\); Section 7 supplies the required separate bound.

## 4. The full explicit formula, with a contour proof

For every real polynomial \(B\),
\[
\boxed{
\sum_\rho m_\rho h_B(z_\rho)
 =h_B(i/2)+h_B(-i/2)
  +\frac1{2\pi}\int_{\mathbb R}h_B(t)\Omega(t)\,dt
  -\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
       [g_B(\log n)+g_B(-\log n)].
}
\tag{4.1}
\]

Here is a proof specialized to the present Gaussian functions. Set
\(H(s)=h_B((s-\tfrac12)/i)\) and choose \(c=3/2\).
Integrate \(Z'/Z(s)H(s)\) around the rectangle with vertical sides
\(\Re s=1-c,c\).

The horizontal sides can be sent to infinity without assuming RH.
For completeness, for each sufficiently large integer \(j\), remove intervals
of radius \(j^{-3}\) around every ordinate with \(|\gamma|\le4(j+2)\).
Their total length is less than one, by the bound for \(N_*\).
Choose \(T_j\in[j,j+1]\) outside those intervals. Conjugation symmetry supplies
the same separation at \(-T_j\).

The logarithmic derivative of the genus-one product is
\[
\frac{\xi'}{\xi}(s)
 =b+\sum_\rho m_\rho\left(\frac1{s-\rho}+\frac1\rho\right).
\]
It converges normally off the zeros; \(\sum_\rho m_\rho/|\rho|^2<\infty\).
On either chosen horizontal segment the terms with \(|\rho|\le4(j+2)\)
are bounded using \(|s-\rho|\ge j^{-3}\); their total has a polynomial
bound in \(j\). For the remaining terms,
\[
\left|\frac1{s-\rho}+\frac1\rho\right|
 =\left|\frac{s}{\rho(s-\rho)}\right|
 \le\frac{2|s|}{|\rho|^2}.
\]
This again gives a polynomial bound. The identity
\(Z'/Z=\xi'/\xi-1/s-1/(s-1)\) transfers it to \(Z'/Z\).
Meanwhile (3.1) makes \(H(s)\) decrease as a Gaussian in \(T_j-\tau\)
or \(T_j+\tau\). Thus both horizontal integrals tend to zero.

The residues of \(Z'/Z\) are \(m_\rho\) at a zero and \(-1\) at each
of \(0,1\). Using (3.5) to pass to the full zero sum, the residue theorem
and \(Z'/Z(1-s)=-Z'/Z(s)\) give
\[
\sum_\rho m_\rho H(\rho)-H(0)-H(1)
 =\frac1{2\pi i}\int_{(c)}
       \frac{Z'}{Z}(s)[H(s)+H(1-s)]\,ds.
\tag{4.2}
\]
The vertical-line integrals use upward orientation.

Now split
\[
\frac{Z'}{Z}(s)=a(s)+\frac{\zeta'}{\zeta}(s),\qquad
a(s)=-\frac12\log\pi+\frac12\psi(s/2).
\]

For the gamma contribution, shift the contour from \(c\) to \(1/2\).
There are no poles of \(a\) between these lines, and the Gaussian kills
the horizontal segments. Substituting \(s=1/2+it\) and replacing \(t\)
by \(-t\) in the second term gives
\[
\frac1{2\pi}\int_{\mathbb R}
 h_B(t)[a(1/2+it)+a(1/2-it)]\,dt
 =\frac1{2\pi}\int_{\mathbb R}h_B(t)\Omega(t)\,dt.
\tag{4.3}
\]

For the prime contribution, first expand \(\zeta'/\zeta\) on \(\Re s=c>1\).
The series is absolutely convergent there and its interchange with the
vertical integral follows from
\[
\left(\sum_{n\ge2}\Lambda(n)n^{-c}\right)
  \int_{\mathbb R}|H(c+it)+H(1-c-it)|\,dt<\infty.
\]
For each individual \(n\), the entire integrand
\(n^{-s}[H(s)+H(1-s)]\) can then be moved to \(\Re s=1/2\).
Its integral is exactly
\[
\frac1{2\pi i}\int_{(c)}n^{-s}[H(s)+H(1-s)]\,ds
 =\frac{g_B(\log n)+g_B(-\log n)}{\sqrt n}.
\tag{4.4}
\]
The resulting series is absolutely convergent by (3.3).
This is a termwise contour shift after the legitimate expansion on
\(\Re s>1\); it does not assert convergence of the logarithmic-derivative
Dirichlet series on the critical line.

Finally \(H(0)=h_B(i/2)\), \(H(1)=h_B(-i/2)\).
Substitution of (4.3)--(4.4) into (4.2) proves (4.1).
No evenness of \(h_B\) was assumed. The real part in \(\Omega\) comes
from combining \(a(1/2+it)\) with \(a(1/2-it)\).

The completed function already incorporates the trivial zeros through its
gamma factor. Adding a separate trivial-zero sum to (4.1) would double count.

## 5. The actual real polynomial functional and Hankel matrix

Define the real linear functional
\[
L_{R,\tau}(B)=
 \frac1{2\pi}\int_{\mathbb R}B(t-\tau)e^{-R(t-\tau)^2}\Omega(t)\,dt
 -2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\Re g_B(\log n).
\tag{5.1}
\]
Absolute convergence proves that this is a well-defined map
\(\mathbb R[w]\to\mathbb R\), linear over \(\mathbb R\).

For \(k\ge0\), put
\[
A_k=\frac1{2\pi}\int_{\mathbb R}
 (t-\tau)^ke^{-R(t-\tau)^2}\Omega(t)\,dt,
\]
\[
\Pi_k=2\sum_p\sum_{\ell\ge1}\frac{\log p}{p^{\ell/2}}
 \Re[e^{-i\tau\ell\log p}G_k(R,\ell\log p)],
\qquad \mu_k=A_k-\Pi_k.
\tag{5.2}
\]
Regrouping by prime powers is justified by (3.3), and
\(\mu_k=L_{R,\tau}(w^k)\).

Let \(M_d=(\mu_{i+j})_{0\le i,j\le d}\) and
\(P(w)=\sum_{j=0}^d c_jw^j\). Finite linearity gives
\[
c^{\mathsf T}M_dc=L_{R,\tau}(P^2).
\tag{5.3}
\]
This is the actual analytic instance of the previously Lean-checked
polynomialFunctional_square.

It is essential to retain the poles before imposing constraints:
\[
\sum_\rho m_\rho w_\rho^k e^{-Rw_\rho^2}
 =\mu_k+
 2\Re[(-\tau+i/2)^ke^{-R(-\tau+i/2)^2}].
\tag{5.4}
\]
Thus the unrestricted zero-side matrix is \(M_d+E_d\), where \(E_d\)
has the pole moments in (5.4). The arithmetic matrix \(M_d\) alone is
not asserted to be nonnegative under RH.

## 6. Pole removal and the exact actual-zero matrix

Set
\[
D_\tau(w)=(w+\tau)^2+\tfrac14,\qquad q_j(w)=D_\tau(w)w^j.
\]
For real \(P\), the condition \(P(-\tau+i/2)=0\) also forces its conjugate
root. The polynomial factor theorem therefore gives
\[
P(-\tau+i/2)=P(-\tau-i/2)=0
 \quad\Longleftrightarrow\quad P=D_\tau S,\quad S\in\mathbb R[w].
\tag{6.1}
\]
For \(d\ge2\), let \(S(w)=\sum_{j=0}^{d-2}x_jw^j\).
Multiplication by \(D_\tau\) is the coefficient map \(T\) whose columns
have the three entries \(\tau^2+1/4,2\tau,1\). Consequently
\[
\mathcal K_d=T^{\mathsf T}M_dT.
\tag{6.2}
\]
The entry formula is
\[
(\mathcal K_d)_{ij}
 =\mu_{i+j+4}+4\tau\mu_{i+j+3}
 +(6\tau^2+\tfrac12)\mu_{i+j+2}
 +(4\tau^3+\tau)\mu_{i+j+1}
 +(\tau^2+\tfrac14)^2\mu_{i+j}.
\tag{6.3}
\]

Apply (4.1) to \(B(w)=D_\tau(w)^2w^{i+j}\).
Both pole evaluations vanish. We obtain
\[
(\mathcal K_d)_{ij}
 =\sum_\rho m_\rho q_i(w_\rho)q_j(w_\rho)e^{-Rw_\rho^2}.
\tag{6.4}
\]
Every series converges absolutely by Section 3.

At an actual zeta zero the pole factor simplifies exactly:
\[
D_\tau(w_\rho)=z_\rho^2+\tfrac14
 =-(\rho-\tfrac12)^2+\tfrac14=\rho(1-\rho).
\tag{6.5}
\]
Equations (6.4)--(6.5) prove (T), and for every real vector \(x\),
\[
\boxed{
x^{\mathsf T}\mathcal K_d x
 =\sum_\rho m_\rho[\rho(1-\rho)]^2
   S(w_\rho)^2e^{-Rw_\rho^2}.
}
\tag{6.6}
\]
Conjugation of spectral points proves that the sum is real.
It is a bilinear square, not an absolute square at a nonreal \(w_\rho\).

For one conjugate spectral pair, put
\(v=(q_j(w)e^{-Rw^2/2})_j=u+iv'\).
Its exact matrix contribution, with multiplicity \(m\) at each point, is
\[
m(vv^{\mathsf T}+\overline v\,\overline v^{\mathsf T})
 =2m(uu^{\mathsf T}-v'v'^{\mathsf T}).
\tag{6.7}
\]
This explicitly identifies the possible negative contribution.

## 7. Discharging the actual-zero localization assumptions on paper

Define
\[
\theta_\rho=\delta_\rho^2-\eta_\rho^2,\qquad
W_{d,\tau}(w)=|D_\tau(w)|^2\sum_{j=0}^{d-2}|w|^{2j},
\]
\[
C_{d,\tau}=\sum_\rho m_\rho W_{d,\tau}(w_\rho)e^{\theta_\rho}.
\tag{7.1}
\]
This constant is finite: \(W\) has polynomial growth of degree at most \(2d\),
and the shell argument of Section 3 applies with \(R=1\).

Cauchy--Schwarz and the exact Gaussian modulus give
\[
\left|\left(\sum_jx_jq_j(w_\rho)\right)^2e^{-Rw_\rho^2}\right|
 \le\|x\|_2^2 W_{d,\tau}(w_\rho)e^{R\theta_\rho}.
\tag{7.2}
\]
For \(R\ge1\), the exact factorization is
\[
e^{R\theta_\rho}=e^{\theta_\rho}e^{(R-1)\theta_\rho}.
\tag{7.3}
\]
Thus if \(\theta_\rho\le\eta\) for all zeros,
\[
|x^{\mathsf T}\mathcal K_d(R,\tau)x|
 \le C_{d,\tau}e^{\eta(R-1)}\|x\|_2^2,
\qquad
\|\mathcal K_d(R,\tau)\|_{\rm op}
 \le C_{d,\tau}e^{\eta(R-1)}.
\tag{7.4}
\]
This supplies all actual-zero hypotheses of the abstract
norm_tsum_le_exp_rate: positivity of the majorant, its summability,
the pointwise exponential bound, and multiplicities.

For a fixed \(\tau\), let \(\eta_\tau\) be the maximum of zero and all
\(\theta_\rho\) with \(|\gamma-\tau|\le1\).
There are finitely many such distinct zeros. Each satisfies
\(\theta_\rho<1/4\). Outside the window \(\theta_\rho<-3/4\).
Consequently \(0\le\eta_\tau<1/4\), and (7.4) holds unconditionally
with \(\eta=\eta_\tau\).

If all zeros in \(|\gamma-\tau|\le L\) are critical, where \(L>1/2\),
the exact local matrix is
\[
H_{\rm loc}(R)=
 \sum_{|\gamma-\tau|\le L}m_\rho
 e^{-R(\gamma-\tau)^2}
 (q_i(\gamma-\tau)q_j(\gamma-\tau))_{ij}\succeq0.
\]
The exact decomposition is \(\mathcal K_d=H_{\rm loc}+E_{\rm tail}\).
Writing \(\kappa=L^2-1/4>0\), all tail exponents satisfy
\(\theta_\rho\le-\kappa\). Therefore
\[
\boxed{
\mathcal K_d(R,\tau)\succeq
 -C_{\rm tail}e^{-\kappa(R-1)}I,\quad
C_{\rm tail}=\sum_{|\gamma-\tau|>L}
 m_\rho W_{d,\tau}(w_\rho)e^{\theta_\rho}<\infty .
}
\tag{7.5}
\]
This supplies the analytic application of nonnegative_head_add_tsum_lower.
Local criticality remains an explicit hypothesis; it is not deduced from
the explicit formula.

## 8. Exact detector and the boundary of the result

Under RH, \(w_\rho=\gamma-\tau\) is real and (6.6) becomes
\[
x^{\mathsf T}\mathcal K_dx
 =\sum_\rho m_\rho(\gamma^2+\tfrac14)^2
      S(\gamma-\tau)^2e^{-R(\gamma-\tau)^2}\ge0.
\tag{8.1}
\]

Conversely, suppose an off-line pair has positive ordinate \(\tau\) and
displacement \(0<a<1/2\), giving spectral points \(\tau\pm ia\), each
with multiplicity \(m\). Let \(U\) be the finite set of distinct shifted
spectral points in \(|\gamma-\tau|\le1\), and let \(J=|U|\).
It is closed under conjugation and contains \(\pm ia\).

The factor \(D_\tau\) never vanishes at a nontrivial zero, by (6.5).
Assign values to a polynomial \(S\) on \(U\):
\[
S(ia)=\frac{i}{D_\tau(ia)},\qquad
S(-ia)=\frac{-i}{D_\tau(-ia)},\qquad
S(w)=0\quad(w\in U\setminus\{ia,-ia\}).
\]
The Lagrange polynomial of degree at most \(J-1\) for these values has
real coefficients: conjugating its coefficients and variable preserves
the same interpolation data, so uniqueness proves reality.
Set \(P=D_\tau S\), of degree at most \(J+1\).
Then \(P(ia)=i\), \(P(-ia)=-i\), every other local zero is annihilated,
and the two pole conditions hold automatically.

For its fixed coefficient vector \(x\) in the pole basis, (6.6) gives the
complete exact identity
\[
x^{\mathsf T}\mathcal K_d(R,\tau)x
 =-2m e^{a^2R}+
   \sum_{|\gamma-\tau|>1}m_\rho P(w_\rho)^2e^{-Rw_\rho^2}.
\tag{8.2}
\]
Here \(d\) is any integer at least the degree of \(P\).
Define the finite constant
\[
C_P=\sum_{|\gamma-\tau|>1}
 m_\rho|P(w_\rho)|^2e^{\theta_\rho}.
\]
Then the retained tail obeys
\[
\left|\sum_{|\gamma-\tau|>1}
 m_\rho P(w_\rho)^2e^{-Rw_\rho^2}\right|
 \le C_Pe^{-3(R-1)/4}\quad(R\ge1).
\tag{8.3}
\]
In particular,
\[
\lim_{R\to\infty}e^{-a^2R}
 x^{\mathsf T}\mathcal K_d(R,\tau)x=-2m.
\tag{8.4}
\]
No simplicity or maximal-displacement hypothesis is needed.
Polynomial values suffice even for multiple zeros.

Consequently the following statements are equivalent:

- RH.
- \(\mathcal K_d(R,\tau)\succeq0\) for every \(d\ge2,\tau>0,R\ge1\).
- For every \(d\ge2,\tau>0,\varepsilon>0\), there are finite constants
  \(C\ge0,R_0\ge1\) such that
  \[
  \lambda_{\min}(\mathcal K_d(R,\tau))\ge-Ce^{\varepsilon R}
  \qquad(R\ge R_0).
  \]

For the last implication, choose the detector and \(0<\varepsilon<a^2\).
The claimed lower bound would give
\(x^{\mathsf T}\mathcal K_dx\ge-Ce^{\varepsilon R}\|x\|_2^2\),
contradicting (8.4). The constants may depend on \(d,\tau,\varepsilon\);
no common constant over all heights is required.

The unconditional rate in Section 7 cannot yield that contradiction:
at the target zero \(\theta_\rho=a^2\), so necessarily
\(\eta_\tau\ge a^2\).
The completed connection removes an analytic identification gap,
while leaving the independent arithmetic lower-bound problem open.

## 9. Additional exact differential identities

Set
\[
\nu_k(R,\tau)=L_{R,\tau}(D_\tau^2w^k)
 =\sum_\rho m_\rho[\rho(1-\rho)]^2w_\rho^ke^{-Rw_\rho^2}.
\]
The locally uniform bounds from Section 3 justify differentiation under all
sums and integrals. Since \(\rho(1-\rho)\) is independent of \(\tau\),
\[
\partial_R\nu_k=-\nu_{k+2},\qquad
\partial_\tau\nu_k=2R\nu_{k+1}-k\nu_{k-1}.
\tag{9.1}
\]
For \(k=0\) omit the last term. The same relations hold for \(\mu_k\),
by differentiating its defining test \(w^ke^{-Rw^2}\).
These are exact identities for the actual arithmetic moments; they do not
imply a sign for the matrices.

## 10. Formalization handoff and sources

The analytic functional (5.1) now has a complete ordinary proof of
well-definedness and the zero formula (4.1). Equations (5.3), (6.2)--(6.4)
instantiate the finite algebra already checked in
Analysis/GaussianSignedMatrixAlgebra.lean.
Section 7 supplies the actual-zero inputs to
Analysis/GaussianLocalization.lean.

Still to formalize in Lean are the actual Gaussian Fourier transform,
analytic convergence and contour theorem, actual multiplicity-weighted zero
sum, and their assembly with those existing declarations. No Lean source
was changed for this paper proof, and a documentation checkpoint does not
certify these analytic statements in the Lean kernel.

References and provenance:

1. A. Bondarenko, D. Radchenko, K. Seip, *Fourier interpolation with zeros of
   zeta and L-functions*, Constructive Approximation 57 (2023), 405--461,
   equation (1.1) and its adjacent admissibility conditions.
   https://arxiv.org/abs/2005.02996
   https://doi.org/10.1007/s00365-022-09599-w
   Supports the classical explicit formula. Applying the even version to the
   even part of a test yields the same real gamma kernel; Section 4 directly
   derives the non-even formula used here.
2. P. Garrett, *Guinand's explicit formula*, 12 February 2021.
   https://www-users.cse.umn.edu/~garrett/m/complex/notes_2020-21/12g_guinand_explicit_fml.pdf
   Supports the completed-zeta contour strategy and the two gamma factors.
   The Gaussian specialization, convergence estimates and good-height
   justification have been supplied explicitly here.
3. E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann
   Zeta-function*, second edition, Oxford, 1986: classical analytic
   continuation, completed-function product and zero-count results.
   NIST DLMF Sections 25.4 and 25.10 also record the functional equation,
   strict strip and zero symmetries:
   https://dlmf.nist.gov/25.4
   https://dlmf.nist.gov/25.10
4. Project context: RiemannResearch/RH/LandauSingleZeroDetection20261028.md
   and RiemannResearch/RH/GaussianSignedMatricesResearch20261029.md.
   This note completes their analytic connection on paper. The interpolation
   criterion is an application of classical Weil positivity ideas; no novelty
   claim is made.
