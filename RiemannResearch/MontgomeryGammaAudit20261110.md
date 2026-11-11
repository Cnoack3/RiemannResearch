# Complete gamma and pole audit for the homogeneous Weil matrix

Initial audit: 2026-11-10. Publication status updated: 2026-11-11.
Requested baseline: ac28c2fb041b0440427adf2372e757ae7d15b0c8.
Initial working source baseline: cbec05a996ad24c24329f8b9f1a85d868664eec7.
Publication review baseline: c21093e386f59f4045607c0b34c0c78abe875609.

This memo preserves the original derivation and numerical checks. Subsequent
Lean work has already formalized the cubic estimate, its actual-zero matrix
identification, and the complete diagonal, with a sharper remainder constant.
The current status and declaration map appear in Section 10. This publication
adds the missing audit document; it does not change the published Lean files.

## Conclusion

The complete error relative to a unit diagonal generally has a nonzero
c_F / log T term. Killing the pole terms by a zero-mean frequency window
does not kill this diagonal. A bound depending only on a positive power of
D/T is therefore false for this explicitly defined, uncentered error.

There is a useful repair. Subtract the exact scalar diagonal, retain the
two pole terms as their explicit rank-one matrix, and use actual window
moments. For a real even C² window supported in [-1,1], with zero integral,
the normalized, diagonally centered homogeneous matrix satisfies

    ||Z_T / N_T - a_T I||_(2→2)
      ≤ 72 M_2(F) (D/T)^3 / log T,

where N_T=T log T/(2π), M_2(F)=∫_{-1}^1 x²|F(x)| dx, and
T ≥ max(4,2D). The original mathematical deduction is given below.
Subsequent published Lean developments prove the corresponding actual-zero
quadratic estimate and a sharper diagonal remainder; see Section 10.
The initial audit's focused verification covered the exact components and
the regularity inputs for the spatial gamma adapter. Its job record is
retained separately from the later formalization evidence.

This matrix uses all nontrivial zeros and analytic multiplicities with a
smooth height test. It is not the hard-cutoff, ordinate-only Montgomery
form factor. No RH, raw pair-correlation limit, or high-support prime
correlation estimate follows just from this calculation.

## 1. Exact definitions and Fourier convention

Use the repository's convention

    h(z)=paperFT k z=∫_R k(v) exp(i z v) dv,
    z_rho=(rho-1/2)/i=gamma-i(beta-1/2),
    g(r)=Re psi(1/4+i r/2)-log π.

For F∈C_c²(R), supp(F)⊆[-1,1], T>0, set

    k_(T,u)(v)=T/(2π) F(T(v-u)) sech(v/2),
    h_(T,u)=paperFT k_(T,u),
    u_nm=log n-log m,
    Z_T(n,m)=∑_rho mult(rho) h_(T,u_nm)(z_rho).

The sum ranges over the complete nontrivial-zero configuration, with both
signs of the ordinate. It is absolutely convergent. The checked provider is
PrimeBandlimitedWeil.actual_zero_sum_eq_resonance, specialized in
PrimeHomogeneousResonance.actual_zero_sum_homogeneous.

For positive n,m with n+1<T and m+1<T,

    Z_T(n,m)=P_T(u_nm)
      -T/(2π) F(0) resonance(n,m)+G_T(u_nm),

where

    P_T(u)=h_(T,u)(i/2)+h_(T,u)(-i/2),
    G_T(u)=1/(2π) ∫_R h_(T,u)(r) g(r) dr.

For Ω(n)=Ω(m), resonance(n,m)=0 exactly. Thus Z_T=P_T+G_T
on a homogeneous block, including its diagonal.

The natural normalization is N_T=T log T/(2π) if F(0)=1.
More generally the leading diagonal is F(0)N_T. This does not insert
an extra factor two for the two signs of the zeros: the full height window
has total integral F(0). For η(y)=(1/(2π))∫F(x)e^(iyx)dx,
∫η=F(0). Replacing η by a hard cutoff requires its own transfer.

Primary source for the explicit formula, including signs and both poles:
Paul Garrett, Guinand's explicit formula, Theorem 0.0.1,
https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2015-16/04_Guinand_explicit_fml.pdf
The repository also cites Iwaniec–Kowalski, Analytic Number Theory, Theorem 5.12.

## 2. Both poles: exact cancellation of the sech factor

Before estimating anything,

    exp(-v/2)+exp(v/2)=2 cosh(v/2).

Consequently, for every u,

    P_T(u)=∫ 2 cosh(v/2) k_(T,u)(v) dv
          =1/π ∫_{-1}^1 F(x) dx =: p_F.

Both poles have been included. Neither is separately discarded.
On any finite coefficient family,

    ∑_(n,m) c_n conj(c_m) P_T(u_nm)
      = p_F |∑_n c_n|².

Thus the pole matrix is p_F times the all-ones matrix. It vanishes
exactly when ∫F=0, or its quadratic form vanishes on the subspace
∑c_n=0. Homogeneity alone implies neither condition.

## 3. Complete spatial gamma formula

Let γ_E denote Euler's constant and put

    W(v)=e^(-v/2)/(1-e^(-2v)),   v>0.

DLMF 5.9.16, followed by Fourier inversion with the convention above, gives

    G(k)=-(γ_E+log π) k(0)
      +∫_0^∞ [2e^(-2v)k(0)-e^(-v/2)(k(v)+k(-v))]
               /(1-e^(-2v)) dv.                         (3.1)

The combined integrand is retained at v=0. Splitting its two singular
pieces into separate improper integrals would be invalid.
A rigorous passage uses a positive lower cutoff first, Fourier inversion,
and then dominated convergence; C² compact support supplies quadratic
Fourier decay and logarithmic integrability.

The equivalent regulator convention already used by the repository is

    Re G(k)=-(γ_E+log(4π)) Re k(0)
      -2∫_0^∞ W(v)[Re k(v)-e^(-v/2)Re k(0)] dv,          (3.2)

when Re k is even. The different constants reflect different regulators.
The existing theorem is
SignedWeilCorrelation.re_integral_paperFT_gammaBracket_eq_regulated.
The now-published gamma_spatial_of_contDiff_two discharges its Fourier
integrability, quadratic decay, continuity, and Lipschitz inputs from
C² compact support. The even-real-part condition remains explicit.

Source for the actual digamma identity:
https://dlmf.nist.gov/5.9.E16
The remaining equations here are deductions, not statements quoted from DLMF.

## 4. Off-diagonal gamma and the exact kernel

Define, for v>0,

    A(v)=W(v) sech(v/2)
        =1/(2 sinh v)+1/(4 cosh²(v/2)),                  (4.1)
    B(v)=A(v)-1/(2v).

The split in (4.1) is exact. In particular,

    B(v)=1/4-v/12-v²/16+7v³/720+O(v⁴),
    B(0):=1/4

extends smoothly at zero from the right.

If |u|>1/T, k_(T,u)(0)=0 and its support avoids zero. Formula (3.1) becomes

    G_T(u)=-1/(2π)∫_{-1}^1 F(x) A(|u+x/T|) dx,         (4.2)

and the complete pole-plus-gamma expression is

    Z_T(n,m)=1/(2π)∫_{-1}^1 F(x)
                   [2-A(|u_nm+x/T|)] dx.               (4.3)

For distinct positive integers n,m≤D,

    |log n-log m| ≥ |n-m|/D.

Therefore |u_nm|>1/T whenever T>D, in particular in the range
T≥max(4,2D). All arithmetic-isolation hypotheses also hold there.

For a general window, μ_j=∫_{-1}^1 x^j F(x)dx. Taylor expansion on the
fixed sign of u gives the complete off-diagonal expansion

    Z_T(n,m)=μ_0/π
      -(1/(2π))∑_(j=0)^(r-1)
         μ_j sign(u_nm)^j A^(j)(|u_nm|)/(j! T^j)
      +R_r(n,m).                                      (4.4)

The remainder is the integral Taylor remainder, with no discarded
prime or pole term. For r≥1, |A^(r)(v)|≤C_r v^(-r-1) on v>0.
Thus, when μ_0=...=μ_(r-1)=0,

    ||offdiag(Z_T/N_T)||_(2→2)
      ≤ C_(F,r) (D/T)^(r+1)/log T                     (4.5)

for T≥max(4,2D). The constants depend on the stated window and r,
not on the size of the homogeneous block. These are constraints on a
chosen analytic test, not assumptions on zeta zeros or primes.

Without moment cancellation, a direct row bound gives instead

    ||offdiag(Z_T/N_T)||_(2→2)
      ≤ C_F D log(2D)/(T log T).

One may alternatively retain the explicit leading matrices in (4.4)
and estimate only its remainder. They cannot simply be omitted.

## 5. An explicit cubic operator bound

Assume F is real and even, ∫F=0. Evenness also gives ∫xF(x)dx=0.
Here is a fully elementary proof of the constant 72 in the conclusion.

Write A=f+q, with f(v)=1/(2sinh v), q(v)=1/(4cosh²(v/2)).
Then

    f''(v)=1/sinh³v+1/(2sinh v) ≤4/v³.

We used sinh v≥v and sinh v≥v³/6.
Also

    q''(v)=q(v)[1-(3/2)sech²(v/2)],
    |q''(v)|≤q(v)≤e^(-v)≤2/v³.

The last inequality follows by maximizing v³e^(-v) at v=3:
27/e³<2. Hence |A''(v)|≤6/v³.

When T≥2D, |x|≤1, and n≠m,

    |u_nm+x/T|≥|u_nm|/2.

The constant and linear Taylor terms in (4.2) integrate to zero, and

    |Z_T(n,m)/N_T|
      ≤24 M_2(F)/(T³ log T |u_nm|³)
      ≤24 M_2(F)(D/T)³/(log T |n-m|³).

Each row and column is bounded by the same number times
2∑_(h≥1)h^(-3)≤3. Schur's inequality proves

    ||Z_T/N_T-a_T I||_(2→2)
      ≤72 M_2(F)(D/T)³/log T,                         (5.1)

where a_T=Z_T(n,n)/N_T, independent of n.
More generally, for T>D+1 the same argument with
theta=1-D/T gives 9 M_2(F)(D/(T-D))³/log T. The constant
72 version is its simpler specialization when T≥2D.
Equivalently, for arbitrary complex coefficients,

    |∑_(n,m)c_n conj(c_m)Z_T(n,m)/N_T
       -a_T∑_n|c_n|²|
      ≤72 M_2(F)(D/T)³/log T ∑_n|c_n|².

No positivity of F, its physical transform, or the homogeneous zero
matrix was used. Repeated integer indices must first be combined; the
matrix indices in (5.1) are distinct integers.

## 6. The diagonal, including the poles

Now take F real and even. Define

    c_F=-(γ_E+log(2π))F(0)
          +∫_0^1 [F(0)-F(x)]/x dx.                   (6.1)

The apparent singularity in (6.1) is removable.
Using a common lower cutoff ε in (3.1), substituting x=Tv, and only then
letting ε decrease to zero gives the exact identity

    G_T(0)=N_T F(0)+T/(2π)c_F
                    -1/π∫_0^1 F(x)B(x/T)dx.         (6.2)

For clarity, the cancellation that produces log T is

    -log(1-e^(-2ε))-log(1/(Tε)) → log T-log 2.

The two poles add p_F=(2/π)∫_0^1F(x)dx. Thus the exact full diagonal is

    a_T=F(0)+c_F/log T
          +2/(T log T)∫_0^1 F(x)[2-B(x/T)]dx.        (6.3)

This formula preserves every diagonal and pole contribution.

If η(y)=(1/(2π))∫F(x)e^(iyx)dx, the equivalent interpretation is

    c_F=∫_R η(y)log(|y|/(2π))dy.

This is the weighted logarithmic height correction. It does not depend on D.

For general even F, (6.3) also yields

    Z_T(n,n)=N_T F(0)+T/(2π)c_F+(7/4)η(0)+O_F(1/T).

The constant 7/4 combines the two poles, 2η(0), with the
gamma correction -η(0)/4. It applies to this smooth full-zero sum;
it is not a claim about an unsmoothed zero count at an endpoint.

When ∫F=0, the poles vanish and ∫_0^1F=0. Since for 0<v≤1,

    |B(v)-1/4|≤v/4,

formula (6.3) gives, with M_1(F)=∫_{-1}^1|x||F(x)|dx,

    |a_T-F(0)-c_F/log T|≤M_1(F)/(4T²log T),   T>1.   (6.4)

One proof of the displayed bound on B uses
sinh v-v≤cosh(1)v³/6< v³/3 and tanh(v/2)≤v/2:
the two deviations in (4.1) sum to at most
v/6+v²/16≤11v/48<v/4.

Combining (5.1) and (6.4) gives the complete, correctly normalized estimate

    ||Z_T/N_T-[F(0)+c_F/log T]I||_(2→2)
       ≤72M_2(F)(D/T)³/log T + M_1(F)/(4T²log T).      (6.5)

The final scalar term in (6.5) also cannot be suppressed if an exact
cubic rate is asserted for fixed D.

Three legitimate normalization choices are now available:

1. Keep N_T and include a_T I as the exact main term.
2. Subtract (a_T-F(0))I exactly, then use (5.1).
3. If F(0)=1, divide by Z_T(n,n)=N_T a_T once a_T is nonzero.
   Then the identity main term has error bounded by (5.1)/|a_T|.

Absorbing only c_F/log T gives (6.5), not (5.1).
A specially calibrated test may have c_F=0, but homogeneity and the
vanishing ordinary moments do not imply this logarithmic-moment condition.

## 7. A precise counterexample to the uncentered proposed rate

Take

    F(x)=(1-x²)³(1-9x²) for |x|≤1, and F(x)=0 otherwise.

This is a real even C² compactly supported function. Its endpoint
derivatives through order two vanish, and

    F(0)=1,   ∫F=0,
    ∫_0^1 [1-F(x)]/x dx=49/24,
    c_F=49/24-γ_E-log(2π)≈-0.3734260646442116775.

Thus every pole contribution is exactly zero, but

    a_T-1=c_F/log T+O(1/(T²log T)).

In fact ∫_0^1 xF(x)dx=-1/10, so the next term is

    a_T=1+c_F/log T-1/(60T²log T)+O(1/(T³log T)).

Fix a one-mode homogeneous block, for example the integer 2, and take D=2.
Then ||Z_T/N_T-I||=|a_T-1| is asymptotic to |c_F|/log T.
It cannot satisfy O((D/T)^s/log T) for any fixed s>0.
This disproves that precise complete-error claim; it does not contradict
a bound whose diagonal was already subtracted.

For this example M_2(F)=11244032/68201595, and the finite numerical
checks compare the original regulated integral with (6.2).
They give agreement to more than 50 decimal places at T=10,100,1000.
The script and output accompany the review bundle. Such computations
support the bookkeeping but prove neither the asymptotic nor the Lean
declarations.

## 8. Connection to Parseval and Gaussian smoothing

The homogeneous Haar theorem gives exactly ∑|c_n|², because the
signed prime-axis Fourier correction vanishes on equal-degree
differences. The arithmetic version is precisely resonance(n,m)=0.
Equations (5.1) and (6.3) supply a quantitative gamma/pole comparison
for the corresponding smoothed actual-zero matrix in the length range
D≤T/2, with its exact scalar mass retained.

For a degree-k polynomial built from integers of size at most D_0, the
relevant integer length can be D_0^k. The bound applies to that complete
length, not merely D_0. Increasing the number of torus coordinates
does not remove this length restriction.

The Gaussian theorem controls, for a raw frequency test f,

    |∫f(α)F_T(α)dα
      -∫f(α)exp(-(α/log T)²)F_T(α)dα|
       ≤ C/log T ∫α²|f(α)|dα.

It removes Gaussian Fourier damping from an already established raw
pairing estimate. It supplies no limiting value for that pairing.
It does not invert the fixed-width sech factor in k_(T,u), remove
horizontal factors from z_rho, or turn the full smoothed zero sum into
Copies(T). These remain distinct analytic transfers.

## 9. Remaining arithmetic and spectral obligations

The homogeneous cancellation is about multiplicative prime-power ratios.
Montgomery's range X=T^α with fixed α>1 involves signed additive
close-shift correlations. In the repository's centered short-interval
notation, the unresolved target remains

    C(N,H)=-HN log H+o_ε(HN log N),

uniformly for N^ε≤H≤N^(1-ε), together with the separately controlled
diagonal, so that the full variance has main term HN log(N/H).
The correspondence H≈X/T motivates this target above support one.
The classical transfer requires its stated RH/zero-side and uniformity
hypotheses; an unconditional prime-to-raw-ordinate transfer is not supplied
by the finite variance identity.

A justified transfer between complex-zero/sech statistics and raw
ordinate statistics, and control of concentration near the transition
frequencies (in particular |α|=1), also remain necessary.
The original low-support formula must use the corrected uniform error
from Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Section 3:
https://arxiv.org/html/2501.14545v3#S3

None of these obligations is discharged by the gamma correction.

## 10. Published formalization and verification scope

The initial module PrimeBandlimitedGamma.lean contains:

- exact cancellation of the pole integrands;
- exact evaluation of both poles and the zero-mean corollary;
- the rank-one pole quadratic form;
- the complete homogeneous actual-zero identity with explicit pole and
  gamma contributions;
- a C² compact-support specialization of the existing spatial gamma
  adapter, with its regularity hypotheses discharged;
- the exact spatial gamma formula for the diagonal frequency test;
- the exact split (4.1) of the sech-modified gamma kernel.

At the initial audit stage, the cubic Taylor/Schur estimate, formulas
(6.1)–(6.5), and the polynomial-window asymptotic were mathematical deductions
in this memo, not kernel-checked results from the audit's focused job.
The later developments below supersede that historical status for the cubic
bound, actual-zero identification, and exact diagonal. The polynomial example,
its numerical evaluation, and the more general T>D+1 variant in Section 5
are not claimed to be kernel-checked by the evidence recorded here.

### Subsequent published improvements

- [869857d79633cf098a2431836349f11c52fd1f3e](https://github.com/Cnoack3/RiemannResearch/commit/869857d79633cf098a2431836349f11c52fd1f3e)
  integrated the exact pole/gamma module and C2 adapter, and formalized the
  constant-72 spatial bound.
- [4990152321b0c1926efeeebc10cc0e33b46cd562](https://github.com/Cnoack3/RiemannResearch/commit/4990152321b0c1926efeeebc10cc0e33b46cd562)
  established the actual-zero matrix identification, complete diagonal, and
  assembled corrected bound.

The current declaration and verification records are
[the gamma catalog](THEOREM_CATALOG_MONTGOMERY_GAMMA_20261110.md) and
[the matrix, transfer, and primes catalog](THEOREM_CATALOG_MONTGOMERY_MATRIX_TRANSFER_PRIMES_20261110.md).
In particular:

| Declaration | Result |
| --- | --- |
| `SechGammaMatrix.quadratic_bound` | Constant-72 spatial quadratic estimate. |
| `PrimeBandlimitedWeil.centeredZeroEntry_eq_spatial` | Exact identification with the centered actual-zero matrix. |
| `PrimeBandlimitedWeil.actual_zero_centered_quadratic_bound` | Constant-72 bound after exact diagonal subtraction. |
| `PrimeBandlimitedWeil.normalizedDiagonal_exact` | Complete diagonal formula, including both poles, for T>2. |
| `PrimeBandlimitedWeil.actual_zero_quadratic_corrected_bound` | Corrected actual-zero quadratic bound with the improved diagonal remainder. |

The formalized estimate improves (6.4) and (6.5), under their common
zero-mean/even-window hypotheses, to

    |a_T-F(0)-c_F/log T| ≤ 11 M_1(F)/(48 T² log T),  T>2,

and, for the homogeneous block and T≥max(4,2D),

    |sum_(n,m) c_n conj(c_m) Z_T(n,m)/N_T
       - [F(0)+c_F/log T] sum_n |c_n|²|
      ≤ [72 M_2(F)(D/T)³/log T
           + 11 M_1(F)/(48 T² log T)] sum_n |c_n|².

The matrix/transfer catalog records verification of the assembled theorem
and its axiom guard in job `job_Xz6US6d-Zqk5IVpfZ0-PhB6cjs426tc_`, with
[BuildBuddy evidence](https://app.buildbuddy.io/invocation/d39f2aea-8b52-40e8-b290-e3f90d4e52b0).
The recorded axiom set is `[propext, Classical.choice, Quot.sound]`.
This is previously published evidence, not a new compilation performed by
this documentation-only publication.

These developments close the gamma matrix and diagonal obligations discussed
here. They do not supply the complete signed close-shift prime estimate,
transition-frequency concentration, or all transfers to the raw ordinate
pair statistic. Later partial transfer and prime results are tracked in the
current catalog rather than inferred from this audit.

### Initial focused verification (historical)

- Bazel/BuildBuddy file job: job_V64zA2gVGx8630L-zO7gtSQOWO81vc3N.
- Terminal state: succeeded; verified=true; exit_code=0.
- Target: //RiemannResearch/Analysis:PrimeBandlimitedGamma.
- Scope: the new module and all transitive imports, including the changed
  WeilGammaFourierAdapter. This is not a whole-project or publication check.
- Checked new-file SHA-256:
  7db7f10d8195815a0a84c0f1196f73fd2c6a5b0592065dd624284fde678e84ec.
- Server-reported verification duration: 113.988 seconds.
  Workspace setup and polling delays are separate; no claim about pure
  kernel-check CPU time is made.
- Build evidence:
  https://app.buildbuddy.io/invocation/80a28c52-5b1d-4678-9a91-475b0c4218a5
- The preceding combined candidate passed snippet job
  job_ucWU_dy5O5xcdXYqHrrs5Gmg74LuuvMJ.
- No commit, push, or publication checkpoint was performed during that initial
  review. The later code publications are identified above; this document is
  being added separately after the user authorized publication.
