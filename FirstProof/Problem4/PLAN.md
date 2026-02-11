# First Proof — Problem 4: Plan

## The Problem

Is it true that for monic real-rooted polynomials p, q of degree n:

$$\frac{1}{\Phi_n(p \boxplus_n q)} \ge \frac{1}{\Phi_n(p)} + \frac{1}{\Phi_n(q)}$$

where $\Phi_n(p) = \sum_i \left(\sum_{j \ne i} \frac{1}{\lambda_i - \lambda_j}\right)^2$ and $\boxplus_n$ is the finite free additive convolution?

This would be a **Finite Free Stam Inequality** — the polynomial analog of Stam's inequality from information theory.

## Critical Finding: This Appears to be an OPEN Problem

Gemini's hints suggested the proof was already in the literature (Marcus's "Section 8", Theorem 8.19 of Mingo-Speicher, etc.). After investigating:

- **arXiv:1504.08057 is WRONG** — it's about viscoplastic fluid flow (Treskatis et al.), not free probability. Gemini hallucinated this reference entirely.
- **Mingo-Speicher Theorem 19 (eq 8.19)** gives the **infinite/operator** version of the Free Stam Inequality (for Voiculescu's Φ*). This is the limit as n→∞, NOT the finite polynomial version.
- **Marcus arXiv:2108.07054** develops finite free probability theory but does NOT appear to contain a finite Stam inequality.
- **MSS arXiv:1504.00350** defines the ⊞_d convolution and proves real-rootedness, but does NOT prove this inequality.
- Web searches for "finite free Stam inequality" or "finite free Fisher information" with polynomial convolutions return no established results.

**Conclusion:** Problem 4 IS the open research question of whether the finite free Stam inequality holds. The answer is known to the problem's author (Spielman/Srivastava) but has not been published. Answers will be released Feb 13, 2026.

## Background from Literature

### The infinite version (Mingo-Speicher Ch. 8)
- **Theorem 19 (p. 216):** Free Fisher information Φ* satisfies:
  1. Superadditivity (eq 8.17)
  2. Free Cramér-Rao inequality (eq 8.18)
  3. **Free Stam inequality (eq 8.19):** $\frac{1}{\Phi^*(x_1+y_1,\ldots)} \geq \frac{1}{\Phi^*(x_1,\ldots)} + \frac{1}{\Phi^*(y_1,\ldots)}$
  4. Lower semicontinuity (eq 8.20)
- **Theorem 22 (p. 217):** Additivity of Φ* under freeness
- Proof uses conjugate systems and free cumulants (Voiculescu [187])

### The finite convolution (MSS arXiv:1504.00350)
- **Definition 1.1 (p. 2):** The symmetric additive convolution ⊞_d defined by coefficient formula:
  $c_k = \sum_{i+j=k} \frac{(d-i)!(d-j)!}{d!(d-k)!} a_i b_j$
  This is EXACTLY the formula in Problem 4.
- **Compact form:** $(p \boxplus_d q)(x) = \hat{p}(D)\hat{q}(D)x^d$
- **Random matrix representation (Def 2.1, p. 5):** $[p \boxplus_d q](x) = \mathbb{E}_Q\{\det[xI - A - QBQ^T]\}$
- Preserves real-rootedness (Theorem in [4])

### Marcus arXiv:2108.07054 — "Polynomial convolutions and (finite) free probability"
- Introduces finite free probability formally
- §2: Polynomial convolutions (⊞_d as expected characteristic polynomial)
- §4: Connection to free probability R-transform and S-transform
- §5: Finite freeness and majorization inequalities
- §6: Finite versions of free probability laws and limit theorems

## Proof Ideas

The connection $\Phi_n(p) = \sum_i (p''(\lambda_i)/(2p'(\lambda_i)))^2$ links Φ_n to derivatives of the polynomial at its roots.

The random matrix representation $p \boxplus_n q = \mathbb{E}_Q[\det(xI - A - QBQ^T)]$ might allow a proof via:
1. Jensen's inequality or convexity arguments on the expected characteristic polynomial
2. Majorization inequalities (Marcus §5)
3. Direct computation for small n (Aristotle proved n=2 case as equality!)

## Aristotle Results

- **Informal submission** (986ddc71): Budget exhausted. 930 lines of partial progress.
  - Proved n=1 and n=2 cases (n=2 is equality via discriminant additivity)
  - Partial progress on n=3 via reduced cubics
- **Formal submission** (577136c7): Failed to find a proof.

## Sources

### Downloaded and split into pages

| Source | Pages dir | Notes |
|--------|-----------|-------|
| MSS "Finite Free Convolutions" (arXiv:1504.00350) | `sources/mss-pages/` (37pp) | Definition of ⊞_d, real-rootedness |
| Marcus "Polynomial convolutions and finite free probability" (arXiv:2108.07054) | `sources/marcus-poly-conv-pages/` (44pp) | Finite free probability theory |
| Mingo & Speicher "Free Probability and Random Matrices" (2017) | `sources/mingo-speicher-pages/` (342pp) | Ch 8: free Fisher info, Stam ineq |

### Key pages to read
- MSS pp 1-2: Definition 1.1 (⊞_d coefficient formula)
- MSS pp 5-6: Random matrix representation (Def 2.1)
- Marcus pp 1-5: Introduction, convolutions, organization
- Mingo-Speicher pp 208-213: §8.3 Conjugate variables and Φ*
- **Mingo-Speicher p 216: Theorem 19 (Free Stam Inequality)**
- Mingo-Speicher pp 217-218: Theorem 22 (additivity ↔ freeness)

### Deleted (wrong paper)
- ~~arXiv:1504.08057~~ — viscoplastic fluid flow, NOT free probability. Gemini hallucinated this.

## Files

| File | Description |
|------|-------------|
| `/tmp/first-proof-problem4.md` | Markdown statement of the problem |
| `/tmp/first-proof-problem4.txt` | Natural language statement (sent to Aristotle) |
| `/tmp/first-proof-problem4-formal.lean` | Formal Lean statement (compiles on v4.24.0 and v4.28.0) |
| `/tmp/first-proof-problem4-informal-result.lean` | Aristotle partial result (informal, 930 lines) |
| `/tmp/first-proof-problem4-formal-result.lean` | Aristotle result (formal, failed) |
| `/tmp/arxiv-2602.05192/First_Proof.tex` | Original LaTeX source |
