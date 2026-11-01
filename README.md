# Binary-Scaling-and-the-Accelerated-Collatz-Map
# Binary Scaling and the Accelerated Collatz Map

This directory contains a research manuscript, a Lean 4 companion, and exact
finite computations concerning the accelerated Collatz map on odd positive
integers,

\[
T(n)=\frac{3n+1}{2^{v_2(3n+1)}}.
\]

The project develops rigorous local identities, descent certificates, binary
and ternary residue calculations, and finite searches for long noncrossing
valuation prefixes. It also identifies precisely where these methods stop.

> **Status:** this project does **not** prove the Collatz conjecture. The
> universal pointwise step—excluding every infinite positive noncrossing
> orbit—remains open. Computational statements below are finite certificates,
> not asymptotic theorems.

## Main outputs

- [Manuscript (PDF)](output/binary_scaling_accelerated_collatz.pdf)
- [Manuscript (Word)](output/binary_scaling_accelerated_collatz.docx)
- [Lean 4 companion](output/CollatzLocal.lean)
- [Manuscript generator](build_collatz_manuscript.py)
- [Analytic computation report](collatz_analytic_directions_report.md)
- [Least-representative search report](collatz_L_records_report.md)
- [Research program and open targets](collatz_research_program.md)

## Core notation

For an accelerated orbit \(n_{i+1}=T(n_i)\), define

\[
k_i=v_2(3n_i+1),\qquad K_r=\sum_{i=0}^{r-1}k_i.
\]

A prefix of length \(r\) is called **noncrossing** when

\[
K_j\le \lfloor j\log_2 3\rfloor\qquad(1\le j\le r).
\]

The least positive odd integer greater than one realizing such a prefix is

\[
L(r)=\min\{n>1:n\text{ odd and noncrossing through time }r\}.
\]

Proving \(L(r)\to\infty\) would exclude a positive integer that remains in the
noncrossing corridor forever. The stronger growth condition
\(\liminf L(r)^{1/r}>3/2\), combined with the bounded-horizon argument in the
manuscript, would imply eventual descent outside an effective finite range.
Neither statement is proved here.

## What is established

The manuscript and Lean development verify, among other results:

- exact one-step behavior for odd residue classes modulo powers of two;
- controlled finite descent for odd integers whose lowest positive binary
  exponent is at least three;
- exact treatment of trailing runs of binary ones;
- the finite-iterate identity with its additive burden;
- necessary-and-sufficient finite descent certificates in the \(M_r,Q_r\) and
  surplus-record formulations;
- exact joint local transition laws involving \(v_2(3n+1)\) and
  \(v_3(n+1)\);
- finite tests for any prescribed cycle valuation vector;
- exact common-modulus Fourier and origin-sensitive finite calculations;
- the equivalence between escape of all nested noncrossing representatives
  and \(L(r)\to\infty\).

The manuscript also explains why density estimates, fixed-modulus arguments,
finite-state base-conversion descriptions, and ordinary spectral gaps do not
by themselves remove a single exceptional positive orbit.

## Certified finite computation

The exact scanner exhaustively tested every odd start below \(10^{11}\). It
certifies \(L(r)\) through \(r=344\), with the final record

\[
L(r)=12{,}235{,}060{,}455\qquad(282\le r\le344),
\]

and proves the finite bound

\[
L(345)>99{,}999{,}999{,}999.
\]

The complete record words and replay data are stored in
[collatz_L_records_100b.json](collatz_L_records_100b.json). The interval
certificates are the `collatz_L_interval_*.tsv` files. See
[collatz_L_records_report.md](collatz_L_records_report.md) for the full table,
certification method, and reproduction commands.

Other exact finite artifacts include:

- `collatz_anchored_exact_18.tsv` — anchored maximal densities;
- `collatz_binary_ternary_correlation_17.json` and
  `collatz_binary_ternary_correlation_22.json` — dynamically coupled binary and
  ternary residue statistics;
- `collatz_diophantine_windows_200000.json` — finite first-crossing safety
  thresholds through 200,000 steps.

## Requirements

- Python 3.10 or newer;
- [`python-docx`](https://python-docx.readthedocs.io/) for manuscript creation;
- a C++20 compiler for the accelerated exact searches;
- Lean 4 and Lake for the formal companion. The configured toolchain is listed
  in `NivenProof/lean-toolchain`, and the project uses Mathlib.

## Rebuild the manuscript

```bash
python3 -m pip install python-docx
python3 build_collatz_manuscript.py
```

This writes
`output/binary_scaling_accelerated_collatz.docx`. To regenerate the PDF with a
local LibreOffice installation:

```bash
libreoffice --headless --convert-to pdf \
  --outdir output output/binary_scaling_accelerated_collatz.docx
```

## Check the Lean companion

From the project root:

```bash
cd NivenProof
lake update                    # needed only when dependencies are absent
lake env lean ../output/CollatzLocal.lean
```

The companion formalizes the elementary arithmetic core. It intentionally
does not assert termination, universal descent, absence of nontrivial cycles,
or the Collatz conjecture. The large finite scan and the analytic external
results cited by the manuscript are also not formalized in Lean.

## Reproduce selected finite experiments

### Reference least-representative scan

```bash
python3 collatz_L_records.py \
  --max-horizon 100 --max-start 10000000 \
  --json collatz_L_records_test.json
```

### Faster C++ scan

```bash
clang++ -O3 -std=c++20 -pthread \
  collatz_L_records_fast.cpp -o collatz_L_records_fast

./collatz_L_records_fast \
  --lo 1 --hi 10000000 --horizon 400 --threads 8 \
  --output collatz_L_interval_test.tsv
```

The full scan to \(10^{11}\) is computationally expensive. Use the contiguous
interval recipe in `collatz_L_records_report.md` rather than starting it
unintentionally.

### Origin-sensitive exact maximum

```bash
clang++ -O3 -std=c++20 \
  collatz_anchored_exact.cpp -o collatz_anchored_exact

./collatz_anchored_exact --max-r 18 \
  --output collatz_anchored_exact_test.tsv
```

### Binary/ternary residue coupling

```bash
python3 collatz_binary_ternary_correlation.py \
  --depth 17 --json collatz_binary_ternary_correlation_test.json
```

### Diophantine safety windows

```bash
python3 collatz_diophantine_windows.py \
  --max-r 200000 --json collatz_diophantine_windows_test.json
```

### Common-modulus Fourier calculation

```bash
python3 collatz_fourier_survivors.py
```

All certification-critical comparisons in the record search use integer
arithmetic. Floating-point values in reports are descriptive summaries, not
the basis of the certificates.

## Project map

| Path | Purpose |
|---|---|
| `output/binary_scaling_accelerated_collatz.{docx,pdf}` | Current manuscript |
| `output/CollatzLocal.lean` | Lean 4 arithmetic companion |
| `build_collatz_manuscript.py` | Reproducible Word manuscript builder |
| `collatz_L_records.py` | Reference exact ordered-start scanner |
| `collatz_L_records_fast.cpp` | Parallel high-range exact scanner |
| `collatz_L_merge_intervals.py` | Merge and replay interval certificates |
| `collatz_fourier_survivors.py` | Exact finite cylinder/Fourier analysis |
| `collatz_anchored_exact.cpp` | Origin-sensitive maximal-density calculation |
| `collatz_binary_ternary_correlation.py` | Coupled \(2\)-adic/\(3\)-adic residues |
| `collatz_diophantine_windows.py` | Exact finite power-gap thresholds |
| `collatz_analytic_directions_report.md` | Interpretation of the new calculations |

## Mathematical scope

The central unresolved target remains pointwise and Archimedean: prove that no
fixed positive integer can realize an infinite aperiodic noncrossing valuation
word. Exponentially small density, extensive finite verification, and exact
local control all constrain a hypothetical counterexample, but none of them
alone proves that the exceptional set is empty.

