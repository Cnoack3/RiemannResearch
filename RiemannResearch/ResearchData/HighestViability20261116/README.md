# Continuous spectral-correction certificates

Source: [highest viability RH.pdf](https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view), equations (44), (58), (62), (72), (73), and agenda G1–G5. The extracted source is `source_extracted.md` in this directory.

These are **external computational certificates**, not Lean-kernel certificates and not asymptotic bounds. The Lean results are catalogued in `../../THEOREM_CATALOG_SPECTRAL_CORRECTION_20261116.md`.

## Exact statement certified

For each x in {53,97,199}, use all primes p≤x, Haar weights a_x/φ(d) on squarefree head atoms d≤x, and all distinct prime pairs. The retained decimal coefficients, multiplied by the exact rational 9999/10000, specify one fixed real correction r_x for each cutoff and each input file. Put

\[
J_x(I)=\int_I\frac{|H_x+\zeta(1/2-it)\Gamma_{x,r}(1/2+it)|^2}{\pi(t^2+1/4)}\,dt,
\quad E_D(c)=\sum_{i<j}(p_i-1)(p_j-1)c_{ij}^2.
\]

The independently certified inequalities are E_D(c)<x²log(x), 0<J_x([1,4])<10⁻⁴x²log(x), and, for separate fits on the larger windows, 0<J_x([1,16])<10⁻²x²log(x) and 0<J_x([0,16])<10⁻²x²log(x). **Each larger window uses a single fixed correction across that whole window.** Corrections optimized for different windows are not identified or combined.

All coefficients and prime logs are real, so the [0,16] integral with weight 1/π is also the symmetric [-16,16] contribution with the paper's weight 1/(2π). The same [0,16] coefficients were also certified on [16,64]. Their sums give J_x([0,64])<(1/20)x²log(x) for x=53,97,199, without refitting. Thus the symmetric [-64,64] contribution is controlled. Frequencies |t|>64 remain uncontrolled here.

| x | Pair columns | Certified J_x([0,16])/(x²log x) enclosure |
|---:|---:|---|
| 53 | 120 | [0.0024632652 ± 7.14e-11] |
| 97 | 300 | [0.004499037 ± 1.02e-10] |
| 199 | 1035 | [0.002639813 ± 2.57e-10] |

The diagonal energy ratios are approximately 0.99980001; the strict bound <1 is checked with balls. Exact rational LDL pivots establish positive definiteness of the free first-chaos Gram matrix at each cutoff.

## Same correction through t=64

`spectral_correction_out_of_window_arb_certificates.json` certifies J_x([16,64])<(1/25)x²log(x) using exactly the same coefficients as the [0,16] reports. The assembler checks matching coefficient SHA-256, rational scaling, and input identity before adding the interval enclosures.

| x | Certified J_x([0,64])/(x²log x) |
|---:|---|
| 53 | [0.038379024 ± 1.16e-10] |
| 97 | [0.034711018 ± 4.05e-10] |
| 199 | [0.029668509 ± 5.03e-10] |

All totals are strictly below 1/20. The correction-energy bound is used once, because the coefficient vector is unchanged. Interval additivity applies to the continuous integrand. The assembled report is `spectral_correction_combined_arb_certificates.json`. This is finite-window progress on G5; there is still no uniform cutoff estimate or high-frequency-tail bound.

## Larger cutoff and factored evaluation

At x=397, using 78 primes and all 3,003 pair columns, the continuous [0,16] certificate gives

- residual ratio [0.00842189859732497 ± 7.29e-18] <1/100;
- diagonal energy ratio approximately 0.99980001 <1.

The retained input and certificate are `spectral_correction_cutoff397_diagnostics.json` and `spectral_correction_cutoff397_arb_certificates.json`. The out-of-window diagnostic at x=397 is floating-point evidence only until a separate continuous certificate is recorded.

The current certifier can use the exact factorization

\[
K_d(z)=K_1(z)\prod_{p\mid d}\frac{p^z}{1-(p^z-1)/(p-1)}.
\]

It shares the full-prime product across head atoms, reducing repeated head-product evaluation. Apparent poles are removable in the exact expression; a ball meeting a denominator zero returns a nonfinite enclosure and forces subdivision. The factorization is checked by exact rational cube enumeration at x=7,11,13. A rigorous x=53 comparison on [16,64] produced overlapping enclosures with the original direct product; see `spectral_correction_factored_regression.json`.

Earlier reports used the direct product. The current default uses the factored product; `--direct-kernel` selects the original evaluator. Both evaluate the same exact integrand. Enclosure widths and runtimes may differ.

## Signed compressed formula

Let X=(1,X_p), X_p(d)=p·1_{p|d}−1, W=diag(a_x/φ(d)) on the head, M=D₁−XᵀWX, C_{d,ij}=X_i(d)X_j(d), g=S+H_x·1_{d=1}, and m=g+Cc. Solve u=M⁻¹XᵀWm. With a_p(z)=p^z−1 and K_d(z)=∏_p(1+X_p(d)a_p(z)/(p−1)), evaluate

\[
\Gamma_{x,r}(z)=u_0+\sum_p(\log p+u_p)a_p(z)
+\sum_{i<j}c_{ij}a_i(z)a_j(z)
-\sum_{d\le x}w_d\bigl(m_d+X(d)u\bigr)K_d(z).
\]

The head contraction is retained with its sign throughout. This formula is independently compared with direct full-Boolean-cube enumeration using exact rationals at x=7,11,13. The regression also checks the head constraint, all first moments, orthogonality of the correction to the original derivative, the exact energy decomposition, and the diagonal energy majorant. Transcendental inputs are replaced by arbitrary rational values for this algebra regression; no claim about zeta evaluation follows from that regression alone.

## Certification mechanism and trust boundary

`spectral_correction_experiment.py` uses ordinary floating-point optimization to propose decimal coefficients. Its reported objective and singular values are diagnostics only. Those decimals are treated as exact rationals by `certify_spectral_block.py`; coefficient selection does not need to be optimal for the certified inequalities.

The certifier recomputes the Gram matrix from exact rational Haar weights, checks positive rational LDL pivots, and uses FLINT/Arb balls for logarithms, the verified linear solve, zeta, and continuous adaptive integration. It integrates the analytic extension N(1/2+it)N(1/2−it)/(π(t²+1/4)), **not** conjugation of a variable complex argument. All constant logs are real. This extension is meromorphic without variable branch cuts; its isolated poles are outside the real integration segment. Nonfinite enclosures cause subdivision or certification failure. The final result must be finite, contain zero in its imaginary interval, have a positive real lower endpoint, and have a real upper endpoint below the requested rational bound.

Trust boundary: Python, SymPy, FLINT/Arb, and the implementation of this translation are external to Lean. See [Arb arithmetic documentation](https://python-flint.readthedocs.io/en/stable/arb.html), [complex integration documentation](https://python-flint.readthedocs.io/en/latest/acb.html), and [Johansson, Arb](https://arxiv.org/abs/1611.02831). The separate Lean obstruction uses actual Mathlib zeta and does not depend on these computations.

## Reproduce

Copy the four Python listings and requirements listing from `REPRODUCTION_CODE.md` into the named local files beside the JSON inputs. Install `requirements.txt`, then run:

```sh
python test_spectral_correction_exact.py
python certify_spectral_block.py
python certify_spectral_block.py --input spectral_correction_extended_diagnostics.json --output spectral_correction_extended_arb_certificates.json --bound 1/100
python certify_spectral_block.py --input spectral_correction_low_extended_diagnostics.json --output spectral_correction_low_extended_arb_certificates.json --bound 1/100
python certify_spectral_block.py --input spectral_correction_low_extended_diagnostics.json --output spectral_correction_out_of_window_arb_certificates.json --block 16 64 --bound 1/25
python assemble_spectral_certificates.py
python certify_spectral_block.py 397 --input spectral_correction_cutoff397_diagnostics.json --output spectral_correction_cutoff397_arb_certificates.json --bound 1/100
```

The retained coefficients are sufficient to reproduce certification. To generate fresh floating-point candidates:

```sh
OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2 python spectral_correction_experiment.py 53 97 199
OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2 python -c "from spectral_correction_experiment import run; run([53,97,199], 'spectral_correction_extended_diagnostics.json', (1.,16.))"
OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2 python -c "from spectral_correction_experiment import run; run([53,97,199], 'spectral_correction_low_extended_diagnostics.json', (0.,16.))"
```

Fresh optimizer runs may produce different decimal coefficients. Regenerate the matching certificate afterward; its SHA-256 binds the coefficient list. The coefficient hash uses UTF-8 JSON of the string list with separators `(',',':')` and no trailing newline, before rational scaling. No uniform inference in x, whole-line bound, or RH conclusion is justified by these three cutoffs.
