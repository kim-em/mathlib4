# First Proof — Problem 4

**Source:** [arXiv:2602.05192](https://arxiv.org/abs/2602.05192) (Abouzaid, Blumberg, Hairer, Kileel, Kolda, Nelson, Spielman, Srivastava, Ward, Weinberger, Williams)

---

Let $p(x)$ and $q(x)$ be two monic polynomials of degree $n$:

$$p(x) = \sum_{k=0}^n a_k x^{n-k} \quad \text{and} \quad q(x) = \sum_{k=0}^n b_k x^{n-k}$$

where $a_0 = b_0 = 1$. Define $p \boxplus_n q(x)$ to be the polynomial

$$(p \boxplus_n q)(x) = \sum_{k=0}^n c_k x^{n-k}$$

where the coefficients $c_k$ are given by the formula:

$$c_k = \sum_{i+j=k} \frac{(n-i)!\,(n-j)!}{n!\,(n-k)!}\, a_i\, b_j$$

for $k = 0, 1, \dots, n$.

For a monic polynomial $p(x) = \prod_{i \le n}(x - \lambda_i)$, define

$$\Phi_n(p) := \sum_{i \le n}\left(\sum_{j \neq i} \frac{1}{\lambda_i - \lambda_j}\right)^2$$

and $\Phi_n(p) := \infty$ if $p$ has a multiple root.

**Question:** Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of degree $n$, then

$$\frac{1}{\Phi_n(p \boxplus_n q)} \ge \frac{1}{\Phi_n(p)} + \frac{1}{\Phi_n(q)}?$$
