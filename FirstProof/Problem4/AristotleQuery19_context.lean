/-
Merged context file combining results from AristotleQuery14 and AristotleQuery15.

AristotleQuery14 (uuid: 91d4e07a-5cd0-4936-99d3-1ca4562be8c8):
  General infrastructure — boxplus, Phi, invPhi, ff_kappa_additive, boxplus_comp_add_C,
  boxplus_comm, Phi_derivative_form, roots_card_eq_natDegree, cumulant algebra.

AristotleQuery15 (uuid: 77c4d757-db33-4da8-9744-3f320343261b):
  n=2 proof (finite_free_stam_inequality_n2), shift invariance, centering lemma,
  boxplus_monomials, boxplus_deriv_at_zero.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators Real Nat Classical Pointwise
open Polynomial BigOperators Finset Classical

/-
Definitions of boxplus convolution, Phi functional, and inverse Phi functional from the context.
-/
def boxplus_coeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) / (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

def boxplus (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  Finset.sum (range (n + 1)) (fun k => C (boxplus_coeff n p q k) * X ^ (n - k))

def Phi (p : ℝ[X]) : ℝ :=
  let roots := p.roots.toFinset
  ∑ r_i ∈ roots, (∑ r_j ∈ roots.erase r_i, 1 / (r_i - r_j))^2

def invPhi (p : ℝ[X]) : ℝ :=
  if p.roots.Nodup ∧ p.roots.card > 1 then
    1 / Phi p
  else 0

def is_centered (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = n ∧ p.coeff (n - 1) = 0

/-
The boxplus convolution commutes with translation on the left argument (equality version).
-/
lemma boxplus_comp_add_C_left (n : ℕ) (p q : ℝ[X]) (c : ℝ)
    (hp : p.natDegree = n) (hq : q.natDegree = n) :
    boxplus n (p.comp (X + C c)) q = (boxplus n p q).comp (X + C c) := by
      refine' Polynomial.funext _;
      intro r;
      -- We'll use the fact that $p(x+c)$ has coefficients given by the binomial theorem.
      have h_coeff : ∀ i ≤ n, (p.comp (.X + (.C c))).coeff (n - i) = ∑ j ∈ Finset.range (i + 1), Nat.choose (n - j) (n - i) * c ^ (i - j) * p.coeff (n - j) := by
        intro i hi
        have h_coeff : (p.comp (.X + (.C c))).coeff (n - i) = ∑ j ∈ Finset.range (n + 1), p.coeff j * Nat.choose j (n - i) * c ^ (j - (n - i)) := by
          rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
          norm_num [ Polynomial.coeff_X_add_C_pow ];
          simp +decide [ mul_assoc, mul_comm, mul_left_comm, hp ];
        rw [ h_coeff, ← Finset.sum_flip ];
        rw [ ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ hi ) ) ];
        · refine' Finset.sum_congr rfl fun x hx => _;
          grind;
        · simp +zetaDelta at *;
          exact fun x hx₁ hx₂ => Or.inl <| Or.inr <| Nat.choose_eq_zero_of_lt <| by omega;
      -- Substitute the expression for the coefficients of $p(x+c)$ into the definition of $boxplus$.
      have h_boxplus_subst : ∀ k ≤ n, boxplus_coeff n (p.comp (.X + (.C c))) q k = ∑ j ∈ Finset.range (k + 1), boxplus_coeff n p q j * Nat.choose (n - j) (n - k) * c^(k - j) := by
        unfold boxplus_coeff;
        intro k hk; rw [ Finset.sum_congr rfl fun i hi => by rw [ h_coeff i ( by linarith [ Finset.mem_range.mp hi ] ) ] ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
        rw [ Finset.sum_sigma', Finset.sum_sigma' ];
        refine' Finset.sum_bij ( fun x hx => ⟨ k - x.1 + x.2, x.2 ⟩ ) _ _ _ _ <;> simp_all +decide [ Nat.choose_succ_succ, add_comm ];
        · exact fun a ha₁ ha₂ => ⟨ by omega, by omega ⟩;
        · grind;
        · exact fun b hb₁ hb₂ => ⟨ k - ( b.fst - b.snd ), b.snd, ⟨ by omega, by omega ⟩, by ext <;> norm_num ; omega ⟩;
        · intro a ha₁ ha₂; rw [ show a.fst - a.snd = k - ( a.snd + ( k - a.fst ) ) by omega ] ; ring;
          rw [ Nat.cast_choose, Nat.cast_choose ] <;> try omega;
          field_simp;
          rw [ show n - ( a.snd + ( k - a.fst ) ) - ( n - k ) = n - a.snd - ( n - a.fst ) by omega ] ; ring;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ k ∈ Finset.range (n + 1), (∑ j ∈ Finset.range (k + 1), boxplus_coeff n p q j * Nat.choose (n - j) (n - k) * c^(k - j)) * (r^(n - k)) = ∑ j ∈ Finset.range (n + 1), boxplus_coeff n p q j * (∑ k ∈ Finset.Ico j (n + 1), Nat.choose (n - j) (n - k) * c^(k - j) * r^(n - k)) := by
        simp +decide only [mul_assoc, sum_mul, Finset.mul_sum _ _ _];
        rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ];
      -- Let's simplify the inner sum $\sum_{k=j}^{n} \binom{n-j}{n-k} c^{k-j} r^{n-k}$.
      have h_inner_sum : ∀ j ≤ n, ∑ k ∈ Finset.Ico j (n + 1), Nat.choose (n - j) (n - k) * c^(k - j) * r^(n - k) = (r + c)^(n - j) := by
        intro j hj; rw [ add_pow ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.sum_Ico_eq_sum_range ] ;
        rw [ ← Finset.sum_flip ];
        simp +decide [ Nat.sub_sub, add_comm, tsub_tsub_cancel_of_le hj ];
        rw [ Nat.sub_add_comm hj ];
        refine' Finset.sum_congr rfl fun x hx => _ ; rw [ show n - ( j + ( n - ( j + x ) ) ) = x by rw [ tsub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show j + x ≤ n from by linarith [ Finset.mem_range.mp hx, Nat.sub_add_cancel hj ] ) ] ] ; ring;
      unfold boxplus; simp_all +decide [ Polynomial.eval_finset_sum ] ;
      exact Eq.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_boxplus_subst x ( Finset.mem_range_succ_iff.mp hx ) ] ) ( h_fubini.trans ( Finset.sum_congr rfl fun x hx => by rw [ h_inner_sum x ( Finset.mem_range_succ_iff.mp hx ) ] ) )

/-
The boxplus convolution is commutative.
-/
lemma boxplus_comm (n : ℕ) (p q : ℝ[X]) :
    boxplus n p q = boxplus n q p := by
      -- By definition of `boxplus`, we know that it is symmetric.
      have h_symm : ∀ k, boxplus_coeff n p q k = boxplus_coeff n q p k := by
        intro k
        unfold boxplus_coeff
        simp [mul_comm, mul_assoc, mul_left_comm];
        rw [ ← Finset.sum_flip ];
        exact Finset.sum_congr rfl fun x hx => by rw [ tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ; ring;
      unfold boxplus; aesop;

/-
For all n, the boxplus convolution commutes with translation (equality version).
-/
theorem boxplus_comp_add_C (n : ℕ) (p q : ℝ[X]) (c d : ℝ)
    (hp : p.natDegree = n) (hq : q.natDegree = n) :
    boxplus n (p.comp (X + C c)) (q.comp (X + C d)) = (boxplus n p q).comp (X + C (c + d)) := by
      -- By definition of boxplus, we can rewrite the left-hand side.
      have h_lhs : boxplus n (p.comp (X + C c)) (q.comp (X + C d)) = (boxplus n (p.comp (X + C c)) q).comp (X + C d) := by
        rw [ boxplus_comm ];
        rw [ boxplus_comp_add_C_left ];
        · rw [ boxplus_comm ];
        · exact hq;
        · rw [ Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, hp, mul_one ];
      rw [ h_lhs ];
      rw [ boxplus_comp_add_C_left ];
      · norm_num [ Polynomial.comp_assoc ];
        ring;
      · exact hp;
      · exact hq

/-
For a monic real-rooted polynomial, the number of roots equals the degree.
-/
lemma roots_card_eq_natDegree (p : ℝ[X])
    (h_splits : p.Splits (RingHom.id ℝ)) (h_monic : p.Monic) :
    p.roots.card = p.natDegree := by
  rw [Polynomial.splits_iff_card_roots] at h_splits
  exact h_splits

/-
Phi in terms of derivatives evaluated at roots.
-/
lemma Phi_derivative_form (p : ℝ[X])
    (h_splits : p.Splits (RingHom.id ℝ))
    (h_nodup : p.roots.Nodup) :
    Phi p = ∑ r ∈ p.roots.toFinset, (p.derivative.derivative.eval r / (2 * p.derivative.eval r))^2 := by
      refine' Finset.sum_congr rfl fun r hr => _;
      -- Let $q(x) = \frac{p(x)}{x - r}$.
      obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ, p = (Polynomial.X - Polynomial.C r) * q ∧ q.eval r ≠ 0 := by
        obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ, p = (Polynomial.X - Polynomial.C r) * q := by
          exact Polynomial.dvd_iff_isRoot.mpr ( by aesop );
        by_cases h : q.eval r = 0 <;> simp_all +decide [ Polynomial.splits_mul, Polynomial.splits_X_sub_C ];
        rw [ Polynomial.roots_mul ] at h_nodup <;> aesop;
      -- Since $q(x)$ is a polynomial with roots $r_j$ for $j \neq r$, we can write $q(x) = c \prod_{j \neq r} (x - r_j)$ for some constant $c$.
      obtain ⟨c, hc⟩ : ∃ c : ℝ, q = Polynomial.C c * ∏ r_j ∈ p.roots.toFinset.erase r, (Polynomial.X - Polynomial.C r_j) := by
        -- Since $q$ is a polynomial with roots $r_j$ for $j \neq i$, we can write $q$ as a product of linear factors corresponding to these roots.
        have hq_factor : q = Polynomial.C (q.leadingCoeff) * ∏ r_j ∈ q.roots.toFinset, (Polynomial.X - Polynomial.C r_j) := by
          convert Polynomial.eq_prod_roots_of_splits_id _;
          · rw [ ← Multiset.toFinset_eq ];
            rfl;
            rw [ hq.1, Polynomial.roots_mul ] at h_nodup <;> aesop;
          · simp_all +decide [ Polynomial.splits_mul_iff ];
        -- Since $q$ is a polynomial with roots $r_j$ for $j \neq i$, we have $q.roots.toFinset = p.roots.toFinset.erase r$.
        have hq_roots : q.roots.toFinset = p.roots.toFinset.erase r := by
          rw [ hq.1, Polynomial.roots_mul ] <;> norm_num [ hq.2 ];
          exact ⟨ Polynomial.X_sub_C_ne_zero _, by rintro rfl; simp +decide at hq ⟩;
        exact ⟨ q.leadingCoeff, hq_roots ▸ hq_factor ⟩;
      -- By definition of $q$, we know that $q'(r) = c \sum_{j \neq r} \prod_{k \neq r, j} (r - r_k)$.
      have hq'_eval : Polynomial.eval r (Polynomial.derivative q) = c * ∑ r_j ∈ p.roots.toFinset.erase r, (∏ r_k ∈ p.roots.toFinset.erase r \ {r_j}, (r - r_k)) := by
        rw [ hc, Polynomial.derivative_mul, Polynomial.derivative_C ] ; norm_num;
        erw [ Polynomial.derivative_prod ];
        erw [ Polynomial.eval_finset_sum ] ; norm_num [ Polynomial.eval_prod ];
        simp +decide [ Finset.sdiff_singleton_eq_erase, Polynomial.eval_multiset_prod ];
        exact Or.inl rfl;
      -- By definition of $q$, we know that $q(r) = c \prod_{j \neq r} (r - r_j)$.
      have hq_eval : Polynomial.eval r q = c * ∏ r_j ∈ p.roots.toFinset.erase r, (r - r_j) := by
        simp +decide [ hc, Polynomial.eval_prod ];
      -- By definition of $q$, we know that $\sum_{j \neq r} \frac{1}{r - r_j} = \frac{q'(r)}{q(r)}$.
      have h_sum_inv : ∑ r_j ∈ p.roots.toFinset.erase r, (1 / (r - r_j)) = Polynomial.eval r (Polynomial.derivative q) / Polynomial.eval r q := by
        rw [ hq'_eval, hq_eval, eq_div_iff ];
        · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          refine' Finset.sum_congr rfl fun x hx => _;
          field_simp;
          rw [ Finset.prod_eq_prod_diff_singleton_mul hx, mul_div_assoc ] ; norm_num [ sub_ne_zero.mpr ( show r ≠ x from by rintro rfl; exact Finset.notMem_erase _ _ hx ) ];
        · exact hq_eval ▸ hq.2;
      rw [ h_sum_inv, hq.1 ] ; norm_num [ Polynomial.derivative_mul, Polynomial.derivative_prod ] ; ring;

/-
The scaled coefficients of the boxplus convolution are the binomial convolution of the scaled coefficients.
-/
def scaled_coeff (n : ℕ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  p.coeff (n - k) / (Nat.choose n k)

lemma scaled_coeff_boxplus (n : ℕ) (p q : ℝ[X]) (k : ℕ) (hk : k ≤ n) :
  scaled_coeff n (boxplus n p q) k = ∑ i ∈ range (k + 1), (Nat.choose k i) * scaled_coeff n p i * scaled_coeff n q (k - i) := by
    -- Expand both sides using the definitions of `scaled_coeff` and `boxplus`.
    unfold scaled_coeff boxplus
    -- Simplify the expression.
    simp [scaled_coeff, boxplus] at *;
    rw [ Finset.sum_eq_single ( k : ℕ ) ];
    · unfold boxplus_coeff;
      simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Nat.cast_choose ];
      refine Finset.sum_congr rfl fun i hi => ?_;
      rw [ Nat.cast_choose, Nat.cast_choose, Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hi ];
      · field_simp;
      · exact le_trans ( Nat.sub_le _ _ ) hk;
    · grind;
    · exact fun h => False.elim <| h <| Finset.mem_range.mpr <| Nat.lt_succ_of_le hk

/-
The 4th finite free cumulant is additive for centered polynomials of degree n >= 4.
-/
def kappa_4 (n : ℕ) (p : ℝ[X]) : ℝ :=
  p.coeff (n - 4) - (n - 2) * (n - 3) / (2 * n * (n - 1)) * (p.coeff (n - 2))^2

lemma kappa_4_additive (n : ℕ) (p q : ℝ[X])
    (hp : is_centered n p) (hq : is_centered n q) (hn : n ≥ 4) :
    kappa_4 n (boxplus n p q) = kappa_4 n p + kappa_4 n q := by
      -- By definition of $kappa_4$, we have
      unfold kappa_4;
      -- Let's simplify the expression using the definition of `boxplus`.
      have h_boxplus : (boxplus n p q).coeff (n - 4) = p.coeff (n - 4) * q.coeff n + p.coeff (n - 2) * q.coeff (n - 2) * ((n - 2) * (n - 3) / (n * (n - 1) : ℝ)) + p.coeff n * q.coeff (n - 4) ∧
                       (boxplus n p q).coeff (n - 2) = p.coeff (n - 2) * q.coeff n + p.coeff n * q.coeff (n - 2) := by
                         constructor <;> unfold boxplus <;> norm_num [ Polynomial.coeff_X_pow ];
                         · rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr ( by linarith : 4 < n + 1 ) ) ];
                           rw [ Finset.sum_eq_add ( 2 ) ( 0 ) ] <;> norm_num;
                           · rcases n with ( _ | _ | _ | _ | n ) <;> norm_num [ boxplus_coeff ] at *;
                             simp +arith +decide [ Finset.sum_range_succ', Nat.factorial ];
                             field_simp;
                             have := hp.2.2; have := hq.2.2; simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; ring;
                           · intros; omega;
                           · intros; omega;
                         · rw [ Finset.sum_eq_add ( 2 ) ( 0 ) ] <;> norm_num [ boxplus_coeff ];
                           · rcases n with ( _ | _ | _ | n ) <;> norm_num [ Finset.sum_range_succ' ] at *;
                             simp_all +decide [ Nat.factorial_ne_zero, Nat.succ_sub_succ, mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv ];
                             cases hp ; cases hq ; aesop;
                           · intros; omega;
                           · grind;
      rcases hp with ⟨ hp₁, hp₂, hp₃ ⟩ ; rcases hq with ⟨ hq₁, hq₂, hq₃ ⟩ ; simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ] ; ring;
      grind

/-
Definition of finite free cumulants.
-/
/--
The k-th finite free cumulant of a sequence of coefficients c.
Defined by the recurrence: c_k = sum_{i=1}^k binom(k-1, i-1) c_{k-i} kappa_i.
Rearranged: kappa_k = c_k - sum_{i=1}^{k-1} binom(k-1, i-1) c_{k-i} kappa_i.
Indices in my definition:
cumulant c (k+1) = c(k+1) - sum_{i=0}^{k-1} binom(k, i) c(k-i) * cumulant c (i+1).
Let K = k+1.
kappa_K = c_K - sum_{j=1}^{K-1} binom(K-1, j-1) c_{K-j} kappa_j.
Let j = i+1. i = j-1.
sum_{i=0}^{K-2} binom(K-1, i) c_{K-(i+1)} kappa_{i+1}.
My definition has sum_{i=0}^{k-1} ... wait.
range k goes 0 to k-1.
So i goes 0 to k-1.
Term is binom(k, i) * c(k-i) * cumulant c (i+1).
This matches K=k+1, j=i+1.
binom(K-1, j-1) = binom(k, i).
c_{K-j} = c_{k+1-(i+1)} = c_{k-i}.
kappa_j = cumulant c (i+1).
So the definition matches.
-/
def cumulant (c : ℕ → ℝ) : ℕ → ℝ
| 0 => 0
| k + 1 => c (k + 1) - ∑ i ∈ (range k).attach, (Nat.choose k i.1) * c (k - i.1) * cumulant c (i.1 + 1)
termination_by k => k
decreasing_by
  simp_wf
  have h : i.val < k := Finset.mem_range.mp i.property
  omega

/--
The finite free cumulant of a polynomial p at index k.
-/
def kappa (n : ℕ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  cumulant (fun i => scaled_coeff n p i) k

/-
Product rule for the sequence derivative of a binomial convolution.
-/
def binom_conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (Nat.choose n i) * a i * b (n - i)

def seq_deriv (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1)

lemma seq_deriv_binom_conv (a b : ℕ → ℝ) (n : ℕ) :
    seq_deriv (binom_conv a b) n = binom_conv (seq_deriv a) b n + binom_conv a (seq_deriv b) n := by
      -- Apply Pascal's identity to split the sum into two parts.
      have h_split : ∑ k ∈ Finset.range (n + 2), Nat.choose (n + 1) k * a k * b (n + 1 - k) = ∑ k ∈ Finset.range (n + 2), Nat.choose n k * a k * b (n + 1 - k) + ∑ k ∈ Finset.range (n + 1), Nat.choose n k * a (k + 1) * b (n - k) := by
        rw [ Finset.sum_range_succ', Finset.sum_range_succ ];
        rw [ Finset.sum_range_succ' ] ; simp +decide [ Finset.sum_range_succ, Nat.choose_succ_succ ] ; ring;
        simpa only [ Finset.sum_add_distrib ] using by ring;
      convert h_split using 1;
      unfold binom_conv seq_deriv; norm_num [ Finset.sum_range_succ ] ; ring;
      rw [ add_right_comm ] ; refine' congr_arg₂ _ rfl ( Finset.sum_congr rfl fun x hx => _ ) ; rw [ Nat.add_sub_assoc ( by linarith [ Finset.mem_range.mp hx ] ) ] ;

/-
Definitions of finite free cumulants, binomial convolution, and sequence derivative (renamed to avoid conflicts).
-/
/--
The k-th finite free cumulant of a sequence of coefficients c.
Defined by the recurrence: c_k = sum_{i=1}^k binom(k-1, i-1) c_{k-i} kappa_i.
-/
def ff_cumulant (c : ℕ → ℝ) : ℕ → ℝ
| 0 => 0
| k + 1 => c (k + 1) - ∑ i ∈ (range k).attach, (Nat.choose k i.1) * c (k - i.1) * ff_cumulant c (i.1 + 1)
termination_by k => k
decreasing_by
  simp_wf
  have h : i.val < k := Finset.mem_range.mp i.property
  omega

/--
The finite free cumulant of a polynomial p at index k.
-/
def ff_kappa (n : ℕ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  ff_cumulant (fun i => scaled_coeff n p i) k

def ff_binom_conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (Nat.choose n i) * a i * b (n - i)

def ff_seq_deriv (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1)

/-
Product rule for the sequence derivative of a binomial convolution.
-/
lemma ff_seq_deriv_binom_conv (a b : ℕ → ℝ) (n : ℕ) :
    ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_seq_deriv a) b n + ff_binom_conv a (ff_seq_deriv b) n := by
      apply seq_deriv_binom_conv

/-
Commutativity of binomial convolution.
-/
lemma ff_binom_conv_comm (a b : ℕ → ℝ) (n : ℕ) :
    ff_binom_conv a b n = ff_binom_conv b a n := by
      convert Finset.sum_bij ( fun i hi => n - i ) _ _ _ _ <;> simp +decide [ Nat.choose_symm_add ];
      · exact fun i hi => Nat.lt_succ_of_le ( Nat.sub_le _ _ );
      · intros; omega;
      · exact fun b hb => ⟨ n - b, by omega, by omega ⟩;
      · exact fun i hi => by rw [ Nat.choose_symm ( Nat.le_of_lt_succ hi ), tsub_tsub_cancel_of_le ( Nat.le_of_lt_succ hi ) ] ; ring;

/-
Associativity of binomial convolution.
-/
lemma ff_binom_conv_assoc (a b c : ℕ → ℝ) (n : ℕ) :
    ff_binom_conv (ff_binom_conv a b) c n = ff_binom_conv a (ff_binom_conv b c) n := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ k ∈ Finset.range (n + 1), (∑ j ∈ Finset.range (k + 1), (Nat.choose n k : ℝ) * (Nat.choose k j : ℝ) * (a j) * (b (k - j))) * (c (n - k)) = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1), (Nat.choose n i : ℝ) * (Nat.choose (n - i) j : ℝ) * (a i) * (b j) * (c (n - i - j)) := by
        simp +decide only [sum_mul, sum_sigma'];
        refine' Finset.sum_bij ( fun x hx => ⟨ x.snd, x.fst - x.snd ⟩ ) _ _ _ _ <;> simp_all +decide [ Nat.sub_sub ];
        · exact fun x hx₁ hx₂ => ⟨ by linarith, by omega ⟩;
        · grind;
        · exact fun b hb₁ hb₂ => ⟨ b.fst + b.snd, b.fst, ⟨ by omega, by omega ⟩, by aesop ⟩;
        · intro x hx₁ hx₂; rw [ Nat.cast_choose, Nat.cast_choose, Nat.cast_choose, Nat.cast_choose ] <;> try omega;
          field_simp;
          rw [ show n - x.snd - ( x.fst - x.snd ) = n - x.fst by omega ] ; ring;
          rw [ Nat.add_sub_of_le ( by linarith ) ] ; ring;
      convert h_fubini using 1;
      · unfold ff_binom_conv; simp +decide [ Finset.sum_mul ] ;
        simp +decide only [mul_assoc, Finset.mul_sum _ _ _, sum_mul];
      · unfold ff_binom_conv;
        simp +decide only [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _]

/-
Definition of shifted cumulant.
-/
def ff_shifted_cumulant (c : ℕ → ℝ) (n : ℕ) : ℝ := ff_cumulant c (n + 1)

/-
The sequence derivative is the binomial convolution of the sequence and its shifted cumulants (assuming c(0)=1).
-/
lemma ff_seq_deriv_eq_binom_conv_shifted_cumulant (c : ℕ → ℝ) (n : ℕ) (hc0 : c 0 = 1) :
    ff_seq_deriv c n = ff_binom_conv c (ff_shifted_cumulant c) n := by
      have h_split : ∑ j ∈ Finset.range (n + 1), (Nat.choose n j) * c j * ff_shifted_cumulant c (n - j) = ∑ j ∈ Finset.range (n + 1), (Nat.choose n j) * c (n - j) * ff_shifted_cumulant c j := by
        rw [ ← Finset.sum_flip ];
        exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ;
      unfold ff_binom_conv ff_seq_deriv;
      unfold ff_shifted_cumulant at *;
      rw [ h_split, Finset.sum_range_succ ];
      rw [ eq_comm, ff_cumulant ];
      rw [ ← Finset.sum_attach ] ; aesop

/-
Distributivity of binomial convolution over addition.
-/
lemma ff_binom_conv_add (a b c : ℕ → ℝ) (n : ℕ) :
    ff_binom_conv a (b + c) n = ff_binom_conv a b n + ff_binom_conv a c n := by
      simp +decide only [ff_binom_conv, Pi.add_apply, mul_add, sum_add_distrib]

/-
Left cancellation for binomial convolution.
-/
lemma ff_binom_conv_cancel_left (a b c : ℕ → ℝ) (ha0 : a 0 ≠ 0)
    (h : ff_binom_conv a b = ff_binom_conv a c) : b = c := by
      funext n;
      induction' n using Nat.strong_induction_on with n ih;
      replace h := congr_fun h n; simp_all +decide [ ff_binom_conv ] ;
      rw [ Finset.sum_range_succ', Finset.sum_range_succ' ] at h;
      rw [ Finset.sum_congr rfl fun i hi => by rw [ ih _ ( by { rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_range.mp hi ] } ) ] ] at h ; aesop

/-
Additivity of shifted cumulants under binomial convolution.
-/
lemma ff_shifted_cumulant_additive (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ff_shifted_cumulant (ff_binom_conv a b) = ff_shifted_cumulant a + ff_shifted_cumulant b := by
      -- Apply the lemma that states the sequence derivative of the binomial convolution of two sequences is the sum of the binomial convolutions of the sequence derivatives.
      have h_seq_deriv : ∀ n, ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_binom_conv a b) (ff_shifted_cumulant a + ff_shifted_cumulant b) n := by
        intros n
        have h_seq_deriv : ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_binom_conv a b) (ff_shifted_cumulant a + ff_shifted_cumulant b) n := by
          have h_seq_deriv : ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_seq_deriv a) b n + ff_binom_conv a (ff_seq_deriv b) n := by
            exact?
          rw [ h_seq_deriv, ff_binom_conv_add ];
          rw [ show ff_seq_deriv a = fun n => ff_binom_conv a ( ff_shifted_cumulant a ) n from funext fun n => ff_seq_deriv_eq_binom_conv_shifted_cumulant a n ha0, show ff_seq_deriv b = fun n => ff_binom_conv b ( ff_shifted_cumulant b ) n from funext fun n => ff_seq_deriv_eq_binom_conv_shifted_cumulant b n hb0 ];
          rw [ ff_binom_conv_assoc, ff_binom_conv_assoc ];
          rw [ show ff_binom_conv ( ff_shifted_cumulant a ) b = ff_binom_conv b ( ff_shifted_cumulant a ) from funext fun n => ff_binom_conv_comm _ _ _, show ff_binom_conv ( ff_binom_conv a b ) ( ff_shifted_cumulant b ) = ff_binom_conv a ( ff_binom_conv b ( ff_shifted_cumulant b ) ) from funext fun n => ff_binom_conv_assoc _ _ _ _ ];
        exact h_seq_deriv;
      apply ff_binom_conv_cancel_left;
      case a => exact ff_binom_conv a b;
      · unfold ff_binom_conv; aesop;
      · ext n;
        rw [ ← h_seq_deriv, ← ff_seq_deriv_eq_binom_conv_shifted_cumulant ];
        unfold ff_binom_conv; aesop;

#check ff_shifted_cumulant_additive

/-
Additivity of shifted cumulants under binomial convolution (v2).
-/
lemma ff_shifted_cumulant_additive_v2 (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ff_shifted_cumulant (ff_binom_conv a b) = ff_shifted_cumulant a + ff_shifted_cumulant b := by
      convert ff_shifted_cumulant_additive a b using 1;
      aesop

/-
Congruence lemma for finite free cumulants.
-/
lemma ff_cumulant_congr (a b : ℕ → ℝ) (n : ℕ) (h : ∀ k, k ≤ n → a k = b k) :
    ff_cumulant a n = ff_cumulant b n := by
      -- By definition of `ff_cumulant`, if `a k = b k` for all `k ≤ n`, then `ff_cumulant a n = ff_cumulant b n`.
      have h_def : ∀ n, (∀ k ≤ n, a k = b k) → ff_cumulant a n = ff_cumulant b n := by
        intro n hn;
        induction' n using Nat.strong_induction_on with n ih;
        rcases n with ( _ | n );
        · unfold ff_cumulant; aesop;
        · unfold ff_cumulant;
          grind;
      exact h_def n h

/-
Finite free cumulants are additive for k <= n.
-/
theorem ff_kappa_additive (n : ℕ) (p q : ℝ[X])
    (hp : p.Monic) (hq : q.Monic) (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    ∀ k, k ≤ n → ff_kappa n (boxplus n p q) k = ff_kappa n p k + ff_kappa n q k := by
      have h_linear : ∀ (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1), ∀ k ≤ n, ff_cumulant (ff_binom_conv a b) k = ff_cumulant a k + ff_cumulant b k := by
        intros a b ha0 hb0 k hk_le_n
        have h_shifted_cumulant_additive : ff_shifted_cumulant (ff_binom_conv a b) = ff_shifted_cumulant a + ff_shifted_cumulant b := by
          exact?;
        induction' k with k ih;
        · unfold ff_cumulant; aesop;
        · convert congr_fun h_shifted_cumulant_additive k using 1;
      intros k hk;
      -- By definition of scaled coefficients, we know that the scaled coefficients of the boxplus convolution are the binomial convolution of the scaled coefficients of p and q.
      have h_scaled_coeff : ∀ k ≤ n, scaled_coeff n (boxplus n p q) k = ff_binom_conv (fun i => scaled_coeff n p i) (fun i => scaled_coeff n q i) k := by
        intros k hk;
        convert scaled_coeff_boxplus n p q k hk using 1;
      convert h_linear _ _ _ _ k hk using 1;
      · exact ff_cumulant_congr _ _ _ fun i hi => h_scaled_coeff i ( by linarith );
      · unfold scaled_coeff;
        have := hp.coeff_natDegree; aesop;
      · unfold scaled_coeff; aesop;

/-
Finite free cumulants are additive under binomial convolution.
-/
lemma ff_cumulant_additive (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ∀ k, ff_cumulant (ff_binom_conv a b) k = ff_cumulant a k + ff_cumulant b k := by
  intro k
  cases k
  · simp [ff_cumulant]
  · rename_i n
    have h := ff_shifted_cumulant_additive_v2 a b ha0 hb0
    have h_n := congr_fun h n
    unfold ff_shifted_cumulant at h_n
    exact h_n

/-
Phi and invPhi are invariant under translation.
-/
lemma Phi_comp_add_C (p : ℝ[X]) (c : ℝ) :
  Phi (p.comp (X + C c)) = Phi p := by
  unfold Phi
  rw [ show ( p.comp ( Polynomial.X + Polynomial.C c ) |> Polynomial.roots |> Multiset.toFinset ) = Finset.image ( fun r => r - c ) ( p.roots.toFinset ) from ?_ ];
  · rw [ Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun x hx => _;
      rw [ show ( Finset.image ( fun r => r - c ) p.roots.toFinset ).erase ( x - c ) = Finset.image ( fun r => r - c ) ( p.roots.toFinset.erase x ) from ?_, Finset.sum_image ] <;> aesop;
    · exact fun x hx y hy hxy => sub_left_inj.mp hxy;
  · ext; simp [Finset.mem_image];
    rw [ Polynomial.comp_eq_zero_iff ] ; aesop

lemma invPhi_comp_add_C (p : ℝ[X]) (c : ℝ) :
  invPhi (p.comp (X + C c)) = invPhi p := by
  unfold invPhi
  simp [Phi_comp_add_C];
  have h_roots : (p.comp (Polynomial.X + Polynomial.C c)).roots = Multiset.map (fun r => r - c) p.roots := by
    ext x;
    have h_roots_eq : Polynomial.rootMultiplicity x (p.comp (Polynomial.X + Polynomial.C c)) = Polynomial.rootMultiplicity (x + c) p := by
      rw [ Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.rootMultiplicity_eq_natTrailingDegree ];
      norm_num [ Polynomial.comp_assoc, add_assoc ];
    rw [ Multiset.count_map ];
    rw [ show ( Multiset.filter ( fun a => x = a - c ) p.roots ) = Multiset.filter ( fun a => a = x + c ) p.roots by congr; ext; constructor <;> intro <;> linarith ] ; rw [ Multiset.filter_eq' ] ; aesop;
  by_cases h : Multiset.Nodup p.roots <;> simp_all +decide [ Multiset.nodup_map_iff_inj_on ];
  exact fun h1 h2 => False.elim <| h <| Multiset.Nodup.of_map _ h1

/-
Finite free cumulants are additive for k <= n (v2).
-/
theorem ff_kappa_additive_v2 (n : ℕ) (p q : ℝ[X])
    (hp : p.Monic) (hq : q.Monic) (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    ∀ k, k ≤ n → ff_kappa n (boxplus n p q) k = ff_kappa n p k + ff_kappa n q k := by
      convert ff_kappa_additive n p q hp hq hp_deg hq_deg using 1

-- ============================================================================
-- Results from AristotleQuery15 (new, not duplicated in AristotleQuery14)
-- ============================================================================

/-
The w-th derivative of the boxplus convolution at 0 is related to the derivatives of the input
polynomials at 0 by a convolution-like formula involving factorials.
-/
lemma boxplus_deriv_at_zero (n : ℕ) (p q : ℝ[X]) (w : ℕ)
  (hp_deg : p.natDegree ≤ n) (hq_deg : q.natDegree ≤ n) :
  (Polynomial.derivative^[w] (boxplus n p q)).eval 0 =
  (1 / Nat.factorial n) * ∑ u ∈ range (n + w + 1),
    let v := n + w - u
    (Polynomial.derivative^[u] p).eval 0 * (Polynomial.derivative^[v] q).eval 0 := by
      by_cases hw : n < w;
      · rw [ Polynomial.iterate_derivative_eq_zero ];
        · rw [ Finset.sum_eq_zero ] ; aesop;
          intro x hx; by_cases hx' : x ≤ n <;> simp_all +decide [ Polynomial.iterate_derivative_eq_zero ] ;
          · exact Or.inr ( by rw [ Polynomial.iterate_derivative_eq_zero ( by omega ) ] ; norm_num );
          · exact Or.inl ( by rw [ Polynomial.iterate_derivative_eq_zero ( by linarith ) ] ; norm_num );
        · refine' lt_of_le_of_lt ( Polynomial.natDegree_sum_le _ _ ) _;
          refine' lt_of_le_of_lt ( Finset.sup_le _ ) _;
          exacts [ n, fun k hk => le_trans ( Polynomial.natDegree_C_mul_X_pow_le _ _ ) ( Nat.sub_le _ _ ), by linarith ];
      · -- By definition of boxplus, we can write its w-th derivative at 0.
        have h_deriv : (Polynomial.derivative^[w] (boxplus n p q)).eval 0 =
          (Nat.factorial w) * (boxplus_coeff n p q (n - w)) := by
            -- By definition of $boxplus$, we know that its $w$-th derivative at $0$ is given by the sum of the $w$-th derivatives of its terms.
            have h_deriv_term : ∀ k ∈ Finset.range (n + 1), Polynomial.eval 0 ((Polynomial.derivative^[w] (Polynomial.C (boxplus_coeff n p q k) * Polynomial.X ^ (n - k)))) = if k = n - w then (Nat.factorial w) * (boxplus_coeff n p q (n - w)) else 0 := by
              intro k hk; split_ifs <;> simp_all +decide [ Polynomial.coeff_iterate_derivative ] ;
              · rw [ Nat.sub_sub_self hw ] ; norm_num [ Polynomial.eval, Polynomial.coeff_iterate_derivative ] ; ring;
                rw [ Nat.descFactorial_self ];
              · by_cases h : n - k < w <;> simp_all +decide [ Polynomial.eval, Polynomial.coeff_iterate_derivative ];
                · exact Or.inr ( ne_of_gt h );
                · omega;
            rw [ show boxplus n p q = ∑ k ∈ Finset.range ( n + 1 ), Polynomial.C ( boxplus_coeff n p q k ) * Polynomial.X ^ ( n - k ) from ?_ ];
            · convert Finset.sum_congr rfl h_deriv_term using 1;
              · induction' ( Finset.range ( n + 1 ) ) using Finset.induction <;> aesop;
              · simp +zetaDelta at *;
                exact fun h => absurd h ( by omega );
            · exact?;
        -- By definition of $boxplus_coeff$, we can rewrite the sum.
        have h_sum : ∑ u ∈ Finset.range (n + w + 1), (Polynomial.eval 0 ((Polynomial.derivative^[u] p))) * (Polynomial.eval 0 ((Polynomial.derivative^[n + w - u] q))) =
          ∑ i ∈ Finset.range (n - w + 1), (Nat.factorial (n - i) * Nat.factorial (w + i) : ℝ) *
            (p.coeff (n - i)) * (q.coeff (w + i)) := by
              have h_sum : ∑ u ∈ Finset.range (n + w + 1), (Polynomial.eval 0 ((Polynomial.derivative^[u] p))) * (Polynomial.eval 0 ((Polynomial.derivative^[n + w - u] q))) =
                ∑ u ∈ Finset.range (n + 1), (Nat.factorial u * Nat.factorial (n + w - u) : ℝ) * (p.coeff u) * (q.coeff (n + w - u)) := by
                  have h_sum : ∀ u ∈ Finset.range (n + w + 1), (Polynomial.eval 0 ((Polynomial.derivative^[u] p))) * (Polynomial.eval 0 ((Polynomial.derivative^[n + w - u] q))) =
                    (if u ≤ n then (Nat.factorial u * Nat.factorial (n + w - u) : ℝ) * (p.coeff u) * (q.coeff (n + w - u)) else 0) := by
                      intro u hu; split_ifs <;> simp_all +decide [ Polynomial.eval, Polynomial.coeff_iterate_derivative ] ;
                      · simp +decide [ Nat.descFactorial_self, mul_assoc, mul_comm, mul_left_comm ];
                      · exact Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith;
                  rw [ Finset.sum_congr rfl h_sum, Finset.sum_ite ];
                  norm_num [ Finset.sum_filter ];
                  rw [ ← Finset.sum_range_add_sum_Ico _ ( by linarith : n + 1 ≤ n + w + 1 ) ];
                  rw [ Finset.sum_congr rfl fun x hx => if_pos <| by linarith [ Finset.mem_range.mp hx ], Finset.sum_congr rfl fun x hx => if_neg <| by linarith [ Finset.mem_Ico.mp hx ] ] ; norm_num;
              rw [ h_sum, ← Finset.sum_flip ];
              rw [ ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ ( Nat.sub_le n w ) ) ) ];
              · refine' Finset.sum_congr rfl fun x hx => _;
                rw [ show n + w - ( n - x ) = w + x by rw [ tsub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show x ≤ n from by linarith [ Finset.mem_range.mp hx, Nat.sub_le n w ] ) ] ];
              · norm_num +zetaDelta at *;
                exact fun x hx₁ hx₂ => Or.inr <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by omega;
        simp_all +decide [ boxplus_coeff ];
        rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ Nat.sub_sub_self ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hw ] ) ] ; ring;
        rw [ show n - ( n - w - i ) = w + i by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show w ≤ n from hw, Nat.sub_add_cancel <| show i ≤ n - w from Finset.mem_range_succ_iff.mp hi ] ] ; norm_num [ Nat.factorial_ne_zero, mul_assoc, mul_comm, mul_left_comm ]

/-
The boxplus convolution of two monomials X^u and X^v is a monomial X^(u+v-n) scaled by a factor
involving factorials, provided u+v >= n. Otherwise it is zero.
-/
lemma boxplus_monomials (n u v : ℕ) (hu : u ≤ n) (hv : v ≤ n) :
  boxplus n (X^u) (X^v) =
  if u + v < n then 0
  else C ((Nat.factorial u * Nat.factorial v : ℝ) / (Nat.factorial n * Nat.factorial (u + v - n))) * X^(u + v - n) := by
    -- Assume $n+1 \leq u+v$. In this case $n-k \leq k \implies k \geq \frac{n-1}{2}$.
    by_cases huv : u + v < n
    -- Case 1
    -- If $u+v < n$, then for any $k$, either $u > n-i$ or $v > n-j$, making the term zero.
    have h_zero : ∀ k ∈ Finset.range (n + 1), boxplus_coeff n (.X ^ u) (.X ^ v) k = 0 := by
      intro k hk
      simp [boxplus_coeff, huv];
      simp_all +decide [ Finset.sum_ite ];
      exact Or.inl fun x hx₁ hx₂ hx₃ => by omega;
    exact if_pos huv ▸ Finset.sum_eq_zero fun k hk => by aesop;
    -- Case 2
    -- In this case, the boxplus convolution of $X^u$ and $X^v$ is a monomial $X^{u+v-n}$ scaled by a factor involving factorials.
    have h_monomial : ∀ k, k ∈ Finset.range (n + 1) → (boxplus_coeff n (Polynomial.X ^ u) (Polynomial.X ^ v) k) = if k = 2 * n - u - v then (u.factorial * v.factorial : ℝ) / (n.factorial * (u + v - n).factorial) else 0 := by
      intro k hk
      simp [boxplus_coeff];
      split_ifs <;> simp_all +decide [ Finset.sum_ite ];
      · rw [ show n - ( 2 * n - u - v ) = u + v - n by omega ];
        rw [ Finset.card_eq_one.mpr ] ; aesop;
        use n - u;
        grind;
      · contrapose! huv; omega;
    simp_all +decide [ boxplus ];
    rw [ Finset.sum_eq_single ( 2 * n - u - v ) ];
    · rw [ h_monomial ];
      · rw [ show n - ( 2 * n - u - v ) = u + v - n by omega ] ; aesop;
      · omega;
    · aesop;
    · exact fun h => False.elim <| h <| Finset.mem_range.mpr <| by omega;

/-
Translation covariance holds for monomials: boxplus of (X+c)^u and X^v is the shifted boxplus
of X^u and X^v.
-/
lemma boxplus_comp_add_C_left_monomials (n u v : ℕ) (c : ℝ)
  (hu : u ≤ n) (hv : v ≤ n) :
  boxplus n ((X + C c)^u) (X^v) = (boxplus n (X^u) (X^v)).comp (X + C c) := by
    -- By linearity of boxplus, we can expand both sides.
    have h_expand : boxplus n ((Polynomial.X + (Polynomial.C c)) ^ u) (Polynomial.X ^ v) = Finset.sum (Finset.range (u + 1)) (fun k => Polynomial.C ((Nat.choose u k : ℝ) * c ^ (u - k)) * boxplus n (Polynomial.X ^ k) (Polynomial.X ^ v)) := by
      -- Apply the linearity of boxplus to split the polynomial into a sum of monomials.
      have h_linear : ∀ p q : Polynomial ℝ, boxplus n (p + q) (Polynomial.X ^ v) = boxplus n p (Polynomial.X ^ v) + boxplus n q (Polynomial.X ^ v) := by
        unfold boxplus;
        unfold boxplus_coeff; norm_num [ Finset.sum_add_distrib ] ;
        intro p q; rw [ ← Finset.sum_add_distrib ] ; congr; ext; simp +decide [ Finset.sum_add_distrib, mul_add ] ;
        simp +decide [ Finset.sum_ite, Finset.filter_congr, Finset.filter_eq', Finset.filter_ne', Polynomial.coeff_mul ];
        rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; aesop;
      have h_expand : ∀ (p : Polynomial ℝ), boxplus n p (Polynomial.X ^ v) = ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff k) * boxplus n (Polynomial.X ^ k) (Polynomial.X ^ v) := by
        intro p
        have h_sum : boxplus n p (Polynomial.X ^ v) = ∑ k ∈ Finset.range (p.natDegree + 1), boxplus n (Polynomial.C (p.coeff k) * Polynomial.X ^ k) (Polynomial.X ^ v) := by
          -- By definition of polynomial multiplication and the linearity of boxplus, we can expand both sides.
          have h_expand : p = ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k := by
            conv_lhs => rw [ p.as_sum_range_C_mul_X_pow ] ;
          conv_lhs => rw [ h_expand ];
          induction' ( Finset.range ( p.natDegree + 1 ) ) using Finset.induction <;> norm_num at *;
          · specialize h_linear 0 ( Polynomial.X ^ v ) ; norm_num at h_linear ; linear_combination' h_linear;
          · grind;
        -- By definition of boxplus, we can factor out the constant coefficient.
        have h_factor : ∀ k : ℕ, boxplus n (Polynomial.C (p.coeff k) * Polynomial.X ^ k) (Polynomial.X ^ v) = Polynomial.C (p.coeff k) * boxplus n (Polynomial.X ^ k) (Polynomial.X ^ v) := by
          intro k
          simp [boxplus];
          simp +decide [ boxplus_coeff, Finset.mul_sum _ _ _ ];
          simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp +decide [ *, mul_assoc, mul_left_comm ] ;
        aesop;
      rw [ h_expand ];
      norm_num [ Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.coeff_X_add_C_pow ];
      ac_rfl;
    -- By definition of boxplus, we know that boxplus n (Polynomial.X ^ k) (Polynomial.X ^ v) is zero unless k + v ≥ n.
    have h_boxplus_nonzero : ∀ k ∈ Finset.range (u + 1), boxplus n (Polynomial.X ^ k) (Polynomial.X ^ v) = if k + v < n then 0 else Polynomial.C ((Nat.factorial k * Nat.factorial v : ℝ) / (Nat.factorial n * Nat.factorial (k + v - n))) * Polynomial.X ^ (k + v - n) := by
      exact fun k hk => boxplus_monomials n k v ( by linarith [ Finset.mem_range.mp hk ] ) ( by linarith [ Finset.mem_range.mp hk ] );
    by_cases h : u + v < n <;> simp_all +decide [ Polynomial.eval_finset_sum ];
    · exact Finset.sum_eq_zero fun x hx => if_pos <| by linarith [ Finset.mem_range.mp hx ] ;
    · -- By simplifying, we can see that both sides are equal.
      have h_simp : ∀ j ∈ Finset.range (u + v - n + 1), ∑ k ∈ Finset.Icc (n - v) u, (Nat.choose u k : ℝ) * c ^ (u - k) * (Nat.factorial k * Nat.factorial v : ℝ) / (Nat.factorial n * Nat.factorial (k + v - n)) * (if k + v - n = j then 1 else 0) = (Nat.factorial u * Nat.factorial v : ℝ) / (Nat.factorial n * Nat.factorial (u + v - n)) * (Nat.choose (u + v - n) j : ℝ) * c ^ (u + v - n - j) := by
        intro j hj
        have h_simp : ∑ k ∈ Finset.Icc (n - v) u, (Nat.choose u k : ℝ) * c ^ (u - k) * (Nat.factorial k * Nat.factorial v : ℝ) / (Nat.factorial n * Nat.factorial (k + v - n)) * (if k + v - n = j then 1 else 0) = (Nat.choose u (n - v + j) : ℝ) * c ^ (u - (n - v + j)) * (Nat.factorial (n - v + j) * Nat.factorial v : ℝ) / (Nat.factorial n * Nat.factorial j) := by
          rw [ Finset.sum_eq_single ( n - v + j ) ] <;> norm_num;
          · grind;
          · intros; omega;
          · exact fun h₁ h₂ => Or.inl <| Or.inl <| Or.inl <| Nat.choose_eq_zero_of_lt h₁;
        rw [ h_simp, Nat.cast_choose, Nat.cast_choose ];
        · field_simp;
          rw [ show u + v - n - j = u - ( n - v + j ) by omega ] ; ring;
        · linarith [ Finset.mem_range.mp hj ];
        · linarith [ Finset.mem_range.mp hj, Nat.sub_add_cancel hv, Nat.sub_add_cancel h ];
      refine' Polynomial.funext fun x => _;
      simp_all +decide [ Polynomial.eval_finset_sum ];
      convert Finset.sum_congr rfl fun j hj => congr_arg ( fun y => y * x ^ j ) ( h_simp j <| Finset.mem_range.mp hj ) using 1;
      · simp +decide [ Finset.sum_ite, Finset.sum_mul _ _ _ ];
        rw [ ← Finset.sum_subset ( show Finset.Icc ( n - v ) u ⊆ Finset.range ( u + 1 ) from fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) ];
        · rw [ Finset.sum_sigma' ];
          refine' Finset.sum_bij ( fun x hx => ⟨ x + v - n, x ⟩ ) _ _ _ _ <;> simp +decide;
          · exact fun a ha₁ ha₂ => ⟨ by omega, ha₁, ha₂ ⟩;
          · exact fun b hb₁ hb₂ hb₃ hb₄ => ⟨ b.snd, ⟨ hb₂, hb₃ ⟩, by aesop ⟩;
          · intro a ha₁ ha₂; rw [ if_neg ( by linarith ) ] ; norm_num ; ring;
        · intro k hk₁ hk₂; split_ifs <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ] ;
      · rw [ if_neg ( by linarith ) ] ; simp +decide [ Polynomial.eval_finset_sum ] ; ring;
        rw [ add_comm, add_pow ] ; ring;
        simp +decide only [mul_assoc, Finset.mul_sum _ _ _]

/-
The boxplus convolution commutes with translation of the first argument for any polynomials
of degree at most n (inequality version, needed for invPhi_boxplus_shift_invariance).
-/
lemma boxplus_comp_add_C_left_le (n : ℕ) (p q : ℝ[X]) (c : ℝ)
  (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
  boxplus n (p.comp (X + C c)) q = (boxplus n p q).comp (X + C c) := by
    -- By linearity of `boxplus`, we can expand both sides as sums of `boxplus` operations on monomials.
    have h_expand : ∀ (p q : ℝ[X]) (c : ℝ), p.natDegree ≤ n → q.natDegree ≤ n → (boxplus n (p.comp (Polynomial.X + Polynomial.C c)) q) = ∑ u ∈ Finset.range (n + 1), (p.coeff u) • ∑ v ∈ Finset.range (n + 1), (q.coeff v) • (boxplus n ((Polynomial.X + Polynomial.C c)^u) (Polynomial.X^v)) := by
      intros p q c hp hq
      have h_expand : boxplus n (p.comp (Polynomial.X + Polynomial.C c)) q = ∑ u ∈ Finset.range (n + 1), (p.coeff u) • boxplus n ((Polynomial.X + Polynomial.C c)^u) q := by
        rw [ show p.comp ( Polynomial.X + Polynomial.C c ) = ∑ u ∈ Finset.range ( n + 1 ), p.coeff u • ( Polynomial.X + Polynomial.C c ) ^ u from ?_ ];
        · unfold boxplus;
          simp +decide [ boxplus_coeff, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_left_comm, Finset.sum_add_distrib ];
          simp +decide [ Finset.smul_sum, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Polynomial.smul_eq_C_mul ];
          rw [ Finset.sum_comm ];
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm;
        · rw [ Polynomial.comp, Polynomial.eval₂_eq_sum_range' ];
          exacts [ Finset.sum_congr rfl fun _ _ => by rw [ Polynomial.smul_eq_C_mul ], Nat.lt_succ_of_le hp ];
      have h_expand_q : ∀ (p q : ℝ[X]) (c : ℝ), p.natDegree ≤ n → q.natDegree ≤ n → boxplus n p q = ∑ v ∈ Finset.range (n + 1), (q.coeff v) • boxplus n p (Polynomial.X^v) := by
        intros p q c hp hq
        have h_expand_q : q = ∑ v ∈ Finset.range (n + 1), (q.coeff v) • Polynomial.X^v := by
          conv_lhs => rw [ Polynomial.as_sum_range' q ( n + 1 ) ( by linarith ) ];
          norm_num [ Polynomial.smul_eq_C_mul, ← Polynomial.C_mul_X_pow_eq_monomial ];
        conv_lhs => rw [ h_expand_q ];
        unfold boxplus;
        simp +decide [ boxplus_coeff, Finset.mul_sum _ _ _, Finset.sum_mul ];
        simp +decide [ Finset.smul_sum, Finset.sum_smul, Polynomial.smul_eq_C_mul ];
        rw [ Finset.sum_comm ];
        refine' Finset.sum_congr rfl fun x hx => _;
        rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; simp +contextual [ Finset.sum_ite ];
        intro y hy; rw [ Finset.sum_eq_single ( n - ( x - y ) ) ] <;> simp +contextual [ Nat.sub_sub_self ( show x - y ≤ n from Nat.sub_le_of_le_add <| by linarith [ Finset.mem_range.mp hx ] ) ] ;
        · rw [ if_pos ( Nat.lt_succ_of_le ( Nat.sub_le _ _ ) ) ] ; norm_num ; ring;
        · exact fun b hb hb' => Or.inr fun h => False.elim <| hb' <| h.symm ▸ rfl;
        · exact fun h => absurd h ( by omega );
      convert h_expand using 2;
      rw [ h_expand_q _ _ c ( by exact le_trans ( Polynomial.natDegree_pow_le ) ( by simpa using by linarith [ Finset.mem_range.mp ‹_› ] ) ) hq ];
    have h_expand_rhs : ∀ (p q : ℝ[X]) (c : ℝ), p.natDegree ≤ n → q.natDegree ≤ n → (boxplus n p q).comp (Polynomial.X + Polynomial.C c) = ∑ u ∈ Finset.range (n + 1), (p.coeff u) • ∑ v ∈ Finset.range (n + 1), (q.coeff v) • (boxplus n (Polynomial.X^u) (Polynomial.X^v)).comp (Polynomial.X + Polynomial.C c) := by
      intros p q c hp hq
      have h_expand_rhs : (boxplus n p q) = ∑ u ∈ Finset.range (n + 1), (p.coeff u) • ∑ v ∈ Finset.range (n + 1), (q.coeff v) • (boxplus n (Polynomial.X^u) (Polynomial.X^v)) := by
        convert h_expand p q 0 hp hq using 1 ; norm_num [ Polynomial.smul_eq_C_mul ];
        norm_num [ Polynomial.smul_eq_C_mul ];
      simp +decide [ h_expand_rhs, Polynomial.smul_eq_C_mul ];
    rw [ h_expand p q c hp hq, h_expand_rhs p q c hp hq ];
    refine' Finset.sum_congr rfl fun u hu => congr_arg _ ( Finset.sum_congr rfl fun v hv => congr_arg _ <| _ );
    convert boxplus_comp_add_C_left_monomials n u v c ( Finset.mem_range_succ_iff.mp hu ) ( Finset.mem_range_succ_iff.mp hv ) using 1

/-
The boxplus convolution is fully translation covariant (inequality version,
needed for invPhi_boxplus_shift_invariance).
-/
lemma boxplus_comp_add_C_le (n : ℕ) (p q : ℝ[X]) (c d : ℝ)
  (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
  boxplus n (p.comp (X + C c)) (q.comp (X + C d)) = (boxplus n p q).comp (X + C (c + d)) := by
    -- By commutativity and left-translation covariance, we can rewrite the left-hand side.
    have h_lhs : (boxplus n (p.comp (.X + (.C c))) (q.comp (.X + (.C d)))) = (boxplus n (q.comp (.X + (.C d))) (p.comp (.X + (.C c)))) := by
      apply boxplus_comm;
    -- By left-translation covariance, we can rewrite the right-hand side.
    have h_rhs : (boxplus n (q.comp (.X + (.C d))) (p.comp (.X + (.C c)))) = ((boxplus n q (p.comp (.X + (.C c)))).comp (.X + (.C d))) := by
      apply_rules [ boxplus_comp_add_C_left_le ];
      rw [ Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C ] ; linarith;
    -- By left-translation covariance, we can rewrite the right-hand side further.
    have h_rhs'' : (boxplus n (p.comp (.X + (.C c)))) q = ((boxplus n p q).comp (.X + (.C c))) := by
      exact?;
    rw [ h_lhs, h_rhs, ← boxplus_comm ];
    rw [ h_rhs'', Polynomial.comp_assoc ];
    norm_num [ Polynomial.comp_assoc ];
    exact congr_arg _ ( by ring )

/-
The Finite Free Stam Inequality holds with equality for n=2.
-/
lemma finite_free_stam_inequality_n2 (p q : ℝ[X])
    (hp : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hp_monic : p.Monic) (hp_deg : p.natDegree = 2)
    (hq : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = 2)
    (hpq : (boxplus 2 p q).Splits (RingHom.id ℝ))
    (hpq_nodup : (boxplus 2 p q).roots.Nodup) :
    invPhi (boxplus 2 p q) ≥ invPhi p + invPhi q := by
      -- By definition of $p$ and $q$, we know that their roots are distinct and real.
      obtain ⟨r1, r2, hr⟩ : ∃ r1 r2 : ℝ, r1 ≠ r2 ∧ p.roots = {r1, r2} := by
        simp_all +decide [ Polynomial.splits_iff_card_roots ];
        rw [ Multiset.card_eq_two ] at hp ; aesop
      obtain ⟨s1, s2, hs⟩ : ∃ s1 s2 : ℝ, s1 ≠ s2 ∧ q.roots = {s1, s2} := by
        -- Since $q$ is a monic polynomial of degree 2 with distinct real roots, its roots must be exactly two distinct real numbers.
        have hq_roots : q.roots.card = 2 := by
          rw [ Polynomial.splits_iff_card_roots ] at hq ; aesop;
        rw [ Multiset.card_eq_two ] at hq_roots; aesop;
      obtain ⟨t1, t2, ht⟩ : ∃ t1 t2 : ℝ, t1 ≠ t2 ∧ (boxplus 2 p q).roots = {t1, t2} := by
        have h_deg : (boxplus 2 p q).natDegree = 2 := by
          refine' Polynomial.natDegree_eq_of_degree_eq_some _;
          refine' Polynomial.degree_eq_of_le_of_coeff_ne_zero _ _ <;> norm_num [ boxplus ];
          · exact le_trans ( Polynomial.degree_sum_le _ _ ) ( Finset.sup_le fun i hi => Polynomial.degree_C_mul_X_pow_le _ _ |> le_trans <| WithBot.coe_le_coe.mpr <| Nat.sub_le _ _ );
          · norm_num [ Finset.sum_range_succ', boxplus_coeff ];
            exact ⟨ by rw [ ← hp_deg, Polynomial.coeff_natDegree ] ; aesop_cat, by rw [ ← hq_deg, Polynomial.coeff_natDegree ] ; aesop_cat ⟩;
        have h_card : Multiset.card (boxplus 2 p q).roots = 2 := by
          rw [ Polynomial.splits_iff_card_roots ] at hpq ; aesop;
        rw [ Multiset.card_eq_two ] at h_card; aesop;
      -- By definition of $p$ and $q$, we know that their roots are distinct and real, so we can write them as $p(x) = (x - r1)(x - r2)$ and $q(x) = (x - s1)(x - s2)$.
      have hp_eq : p = (Polynomial.X - Polynomial.C r1) * (Polynomial.X - Polynomial.C r2) := by
        rw [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp_monic ] <;> aesop
      have hq_eq : q = (Polynomial.X - Polynomial.C s1) * (Polynomial.X - Polynomial.C s2) := by
        rw [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq_monic ] <;> aesop
      have hbox_eq : boxplus 2 p q = (Polynomial.X - Polynomial.C t1) * (Polynomial.X - Polynomial.C t2) := by
        convert Polynomial.eq_prod_roots_of_monic_of_splits_id _ _ using 1;
        · norm_num [ ht ];
        · unfold boxplus;
          unfold boxplus_coeff; norm_num [ Finset.sum_range_succ', hp_deg, hq_deg ] ;
          rw [ Polynomial.Monic, Polynomial.leadingCoeff_add_of_degree_lt ] <;> norm_num [ hp_deg, hq_deg, hp_eq, hq_eq ];
          · norm_num [ mul_sub, Polynomial.coeff_X, Polynomial.coeff_C ];
          · norm_num [ mul_sub, Polynomial.coeff_X, Polynomial.coeff_C ];
            erw [ Polynomial.degree_lt_iff_coeff_zero ] ; norm_num;
            rintro ( _ | _ | m ) <;> simp +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
        · assumption;
      -- By definition of $Phi$, we know that $invPhi(p) = \frac{(r1 - r2)^2}{2}$ and $invPhi(q) = \frac{(s1 - s2)^2}{2}$.
      have h_invPhi_p : invPhi p = (r1 - r2)^2 / 2 := by
        unfold invPhi;
        unfold Phi; norm_num [ hr, hs, hp_deg, hq_deg ] ; ring;
        rw [ inv_inv ] ; ring
      have h_invPhi_q : invPhi q = (s1 - s2)^2 / 2 := by
        unfold invPhi;
        unfold Phi; norm_num [ hs, hq_eq ] ; ring;
        rw [ show ( - ( Polynomial.X * Polynomial.C s1 ) - Polynomial.X * Polynomial.C s2 + Polynomial.X ^ 2 + Polynomial.C s1 * Polynomial.C s2 : Polynomial ℝ ) = ( Polynomial.X - Polynomial.C s1 ) * ( Polynomial.X - Polynomial.C s2 ) by ring, Polynomial.roots_mul ] <;> norm_num [ hs ];
        · grind;
        · exact ⟨ Polynomial.X_sub_C_ne_zero _, Polynomial.X_sub_C_ne_zero _ ⟩
      have h_invPhi_box : invPhi (boxplus 2 p q) = (t1 - t2)^2 / 2 := by
        unfold invPhi;
        unfold Phi; norm_num [ ht ] ; ring;
        rw [ inv_inv ] ; ring;
      -- By definition of $boxplus$, we know that $t1 + t2 = r1 + r2 + s1 + s2$ and $t1 * t2 = r1 * r2 + s1 * s2 + (r1 + r2) * (s1 + s2) / 2$.
      have h_sum : t1 + t2 = r1 + r2 + s1 + s2 := by
        unfold boxplus at *; simp_all +decide [ Polynomial.coeff_X, Polynomial.coeff_C, mul_sub ] ;
        unfold boxplus_coeff at hbox_eq; norm_num [ Finset.sum_range_succ', Polynomial.coeff_X, Polynomial.coeff_C ] at hbox_eq; have := congr_arg ( Polynomial.eval 0 ) hbox_eq; norm_num at this; have := congr_arg ( Polynomial.eval 1 ) hbox_eq; norm_num at this; have := congr_arg ( Polynomial.eval ( -1 ) ) hbox_eq; norm_num at this; linarith;
      have h_prod : t1 * t2 = r1 * r2 + s1 * s2 + (r1 + r2) * (s1 + s2) / 2 := by
        unfold boxplus at hbox_eq; norm_num [ hp_eq, hq_eq ] at hbox_eq;
        norm_num [ Finset.sum_range_succ, boxplus_coeff ] at hbox_eq;
        norm_num [ mul_sub, Polynomial.coeff_X, Polynomial.coeff_C ] at hbox_eq; have := congr_arg ( Polynomial.eval 0 ) hbox_eq; norm_num at this; have := congr_arg ( Polynomial.eval 1 ) hbox_eq; norm_num at this; linarith;
      rw [ ← eq_sub_iff_add_eq' ] at h_sum ; subst_vars ; nlinarith [ sq_nonneg ( r1 - r2 - ( s1 - s2 ) ), sq_nonneg ( r1 - r2 + ( s1 - s2 ) ) ] ;

/-
The invPhi of the boxplus convolution is invariant under shifting the input polynomials.
-/
lemma invPhi_boxplus_shift_invariance (n : ℕ) (p q : ℝ[X]) (c d : ℝ)
  (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
  invPhi (boxplus n p q) = invPhi (boxplus n (p.comp (X + C c)) (q.comp (X + C d))) := by
    rw [ boxplus_comp_add_C_le n p q c d hp hq ];
    -- By definition of invPhi, we have:
    unfold invPhi
    simp [Polynomial.comp_assoc];
    -- By definition of polynomial composition, the roots of $(boxplus n p q).comp (X + (C c + C d))$ are the roots of $boxplus n p q$ shifted by $-(c + d)$.
    have h_roots_comp : (boxplus n p q).comp (Polynomial.X + (Polynomial.C c + Polynomial.C d)) = Polynomial.comp (boxplus n p q) (Polynomial.X + Polynomial.C (c + d)) := by
      norm_num [ Polynomial.C_add ];
    rw [ h_roots_comp, show ( Polynomial.roots ( ( boxplus n p q |> Polynomial.comp ) ( Polynomial.X + Polynomial.C ( c + d ) ) ) ) = ( Polynomial.roots ( boxplus n p q ) |> Multiset.map fun x => x - ( c + d ) ) from ?_, Multiset.card_map ];
    · unfold Phi;
      split_ifs <;> simp_all +decide [ Multiset.nodup_map_iff_inj_on ];
      · -- By definition of polynomial composition, the roots of $(boxplus n p q).comp (X + (C c + C d))$ are the roots of $boxplus n p q$ shifted by $-(c + d)$. Hence, we can rewrite the sums.
        have h_roots_comp : ((boxplus n p q).comp (Polynomial.X + (Polynomial.C c + Polynomial.C d))).roots.toFinset = Finset.image (fun x => x - (c + d)) ((boxplus n p q).roots.toFinset) := by
          ext; simp [Finset.mem_image];
          rw [ Polynomial.comp_eq_zero_iff ] ; aesop;
        rw [ h_roots_comp, Finset.sum_image ];
        · refine' Finset.sum_congr rfl fun x hx => _;
          rw [ Finset.sum_image ] <;> aesop;
        · exact fun x hx y hy hxy => by simpa using hxy;
      · rw [ Multiset.nodup_iff_count_le_one ] at *;
        simp +zetaDelta at *;
        obtain ⟨ x, hx ⟩ := ‹∃ x, 1 < Polynomial.rootMultiplicity x ( boxplus n p q ) ›; specialize ‹ ( ∀ a : ℝ, Multiset.count a ( Multiset.map ( fun x => x - ( c + d ) ) ( boxplus n p q |> Polynomial.roots ) ) ≤ 1 ) ∧ 1 < ( boxplus n p q |> Polynomial.roots |> Multiset.card ) ›; have := ‹ ( ∀ a : ℝ, Multiset.count a ( Multiset.map ( fun x => x - ( c + d ) ) ( boxplus n p q |> Polynomial.roots ) ) ≤ 1 ) ∧ 1 < ( boxplus n p q |> Polynomial.roots |> Multiset.card ) ›.1 ( x - ( c + d ) ) ; simp_all +decide [ Multiset.count_map ] ;
        simp_all +decide [ Multiset.filter_eq, Polynomial.rootMultiplicity_eq_zero ];
        linarith;
    · ext x;
      have h_root_multiplicity : Polynomial.rootMultiplicity x ((boxplus n p q).comp (Polynomial.X + Polynomial.C (c + d))) = Polynomial.rootMultiplicity (x + (c + d)) (boxplus n p q) := by
        rw [ Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.rootMultiplicity_eq_natTrailingDegree ];
        norm_num [ add_assoc, Polynomial.comp_assoc ];
      rw [ Multiset.count_map ];
      rw [ show ( Multiset.filter ( fun a => x = a - ( c + d ) ) ( boxplus n p q |> Polynomial.roots ) ) = Multiset.filter ( fun a => a = x + ( c + d ) ) ( boxplus n p q |> Polynomial.roots ) by congr; ext; constructor <;> intro <;> linarith ] ; rw [ Multiset.filter_eq' ] ; aesop

/-
Any monic polynomial of positive degree can be shifted to have zero trace (second highest
coefficient).
-/
lemma exists_shift_centered (n : ℕ) (p : ℝ[X]) (hn : n > 0)
  (hp_monic : p.Monic) (hp_deg : p.natDegree = n) :
  ∃ c : ℝ, (p.comp (X + C c)).coeff (n - 1) = 0 := by
    -- The coefficient of $X^{n-1}$ in $p(X+c)$ is given by the Taylor expansion formula or binomial expansion.
    have h_coeff : ∀ c : ℝ, p.comp (Polynomial.X + Polynomial.C c) = Finset.sum (Finset.range (n + 1)) (fun k => Polynomial.C (p.coeff k) * (Polynomial.X + Polynomial.C c)^k) := by
      intro c; nth_rw 1 [ p.as_sum_range_C_mul_X_pow ] ; simp +decide [ ← Polynomial.C_mul_X_pow_eq_monomial, hp_deg ] ;
    -- By comparing coefficients, we can see that the coefficient of $X^{n-1}$ in $p(X+c)$ is given by $n c + a_{n-1}$.
    have h_coeff_n_minus_1 : ∀ c : ℝ, (p.comp (Polynomial.X + Polynomial.C c)).coeff (n - 1) = n * c + p.coeff (n - 1) := by
      intro c; rw [ h_coeff c ] ; simp +decide [ Polynomial.coeff_X_add_C_pow ] ;
      rw [ Finset.sum_eq_add ( n - 1 ) n ] <;> norm_num [ Nat.choose_succ_succ, hn ];
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_succ_succ, add_comm ];
        · rw [ ← hp_deg, hp_monic.coeff_natDegree ] ; ring;
        · simp_all +decide [ add_comm 1, Nat.choose_succ_succ, Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ] ; ring;
      · omega;
      · intro k hk₁ hk₂ hk₃; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ] ;
        · interval_cases k <;> contradiction;
        · exact Or.inr <| Or.inr <| Nat.choose_eq_zero_of_lt <| lt_of_le_of_ne ( by omega ) hk₂;
      · exact fun h => absurd h ( by omega );
    exact ⟨ -p.coeff ( n - 1 ) / n, by rw [ h_coeff_n_minus_1, mul_div_cancel₀ _ ( by positivity ) ] ; ring ⟩

-- ============================================================================
-- n=3 proof infrastructure and result (from Query 4)
-- ============================================================================

/-
Cauchy-Schwarz type inequality: (b1+b2)²/(u1+u2)² ≤ b1²/u1² + b2²/u2².
-/
lemma n3_inequality (b1 b2 u1 u2 : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) :
  (b1 + b2)^2 / (u1 + u2)^2 ≤ b1^2 / u1^2 + b2^2 / u2^2 := by
  rw [ div_add_div, div_le_div_iff₀ ] <;> try positivity;
  have h_am_gm : (b1 * u2)^2 + (b2 * u1)^2 ≥ 2 * b1 * b2 * u1 * u2 := by
    linarith [ sq_nonneg ( b1 * u2 - b2 * u1 ) ];
  nlinarith [ sq_nonneg ( u1 - u2 ), mul_pos hu1 hu2, mul_le_mul_of_nonneg_left h_am_gm ( sq_nonneg u1 ), mul_le_mul_of_nonneg_left h_am_gm ( sq_nonneg u2 ) ]

/-
Formula for Phi of a reduced cubic polynomial X³ + aX + b.
-/
lemma Phi_deg3_reduced_eq (a b : ℝ)
  (h_real : (X^3 + C a * X + C b).Splits (RingHom.id ℝ))
  (h_nodup : (X^3 + C a * X + C b).roots.Nodup) :
  Phi (X^3 + C a * X + C b) = 18 * a^2 / (-4 * a^3 - 27 * b^2) := by
    obtain ⟨r1, r2, r3, hr⟩ : ∃ r1 r2 r3 : ℝ, r1 + r2 + r3 = 0 ∧ r1 * r2 + r2 * r3 + r3 * r1 = a ∧ r1 * r2 * r3 = -b ∧ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 := by
      obtain ⟨r1, r2, r3, hr⟩ : ∃ r1 r2 r3 : ℝ, r1 ∈ (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots ∧ r2 ∈ (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots ∧ r3 ∈ (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots ∧ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 := by
        have h_card : Multiset.card (Polynomial.roots (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b)) = 3 := by
          rw [ Polynomial.splits_iff_card_roots ] at h_real;
          rw [ h_real, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ];
        rcases x : Polynomial.roots _ with ⟨ _ | ⟨ r1, _ | ⟨ r2, _ | ⟨ r3, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all +decide;
      use r1, r2, r3;
      norm_num at hr;
      grind;
    have h_roots : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots = {r1, r2, r3} := by
      rw [ show ( Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial ℝ ) = ( Polynomial.X - Polynomial.C r1 ) * ( Polynomial.X - Polynomial.C r2 ) * ( Polynomial.X - Polynomial.C r3 ) by exact Polynomial.funext fun x => by norm_num; linear_combination hr.1 * x^2 - hr.2.1 * x + hr.2.2.1 ];
      rw [ Polynomial.roots_mul ( by exact mul_ne_zero ( mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ) ) ( Polynomial.X_sub_C_ne_zero _ ) ), Polynomial.roots_mul ( by exact mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ) ), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; tauto;
    unfold Phi;
    simp_all +decide [ Finset.sum ];
    rw [ show a = r1 * r2 + r2 * r3 + r3 * r1 by linarith, show b = -r1 * r2 * r3 by linarith ];
    rw [ inv_add_inv, inv_add_inv, inv_add_inv ] <;> try cases lt_or_gt_of_ne hr.2.2.2.1 <;> cases lt_or_gt_of_ne hr.2.2.2.2.1 <;> cases lt_or_gt_of_ne hr.2.2.2.2.2 <;> nlinarith;
    rw [ div_pow, div_pow, div_pow, div_add_div, div_add_div ];
    · rw [ div_eq_div_iff ];
      · grind +ring;
      · simp +decide [ sub_eq_iff_eq_add, hr ];
        tauto;
      · grind;
    · exact pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) );
    · exact mul_ne_zero ( pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ) ) ( pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ) );
    · exact pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) );
    · exact pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) )

lemma cubic_distinct_real_roots_implies_a_neg (a b : ℝ)
  (h_roots : (X^3 + C a * X + C b).roots.toFinset.card = 3) :
  a < 0 := by
    by_contra h_contra; push_neg at h_contra; (
    have h_increasing : StrictMono (fun x : ℝ => x^3 + a * x + b) := by
      exact fun x y hxy => by norm_num; nlinarith [ sq_nonneg ( x^2 - y^2 ), pow_pos ( sub_pos.mpr hxy ) 3, mul_le_mul_of_nonneg_left hxy.le h_contra ] ;
    exact absurd h_roots ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_one.mpr ( by intros x hx y hy; exact h_increasing.injective <| by aesop ) ) ( by norm_num ) ) ));

lemma boxplus_deg3_reduced_eq (p q : ℝ[X])
  (hp_monic : p.Monic) (hq_monic : q.Monic)
  (hp_deg : p.natDegree = 3) (hq_deg : q.natDegree = 3)
  (hp_red : p.coeff 2 = 0) (hq_red : q.coeff 2 = 0) :
  boxplus 3 p q = X^3 + C (p.coeff 1 + q.coeff 1) * X + C (p.coeff 0 + q.coeff 0) := by
    unfold boxplus;
    simp_all +decide [ Finset.sum_range_succ, boxplus_coeff ];
    simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
    ring

/-
The n=3 case of the Finite Free Stam Inequality for reduced cubics.
-/
theorem conjecture_n_3_reduced (a1 b1 a2 b2 : ℝ)
  (h_real1 : (X^3 + C a1 * X + C b1).Splits (RingHom.id ℝ))
  (h_nodup1 : (X^3 + C a1 * X + C b1).roots.Nodup)
  (h_real2 : (X^3 + C a2 * X + C b2).Splits (RingHom.id ℝ))
  (h_nodup2 : (X^3 + C a2 * X + C b2).roots.Nodup)
  (h_real3 : (X^3 + C (a1+a2) * X + C (b1+b2)).Splits (RingHom.id ℝ))
  (h_nodup3 : (X^3 + C (a1+a2) * X + C (b1+b2)).roots.Nodup) :
  invPhi (X^3 + C (a1+a2) * X + C (b1+b2)) ≥
  invPhi (X^3 + C a1 * X + C b1) + invPhi (X^3 + C a2 * X + C b2) := by
  have hPhi_def : ∀ (a b : ℝ) (h_real : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b).Splits (RingHom.id ℝ)) (h_nodup : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots.Nodup), invPhi (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) = - (2 / 9) * a - (3 / 2) * (b / a) ^ 2 := by
    intros a b h_real h_nodup
    rw [invPhi];
    split_ifs <;> simp_all +decide [ Polynomial.splits_iff_card_roots ];
    · convert congr_arg ( fun x : ℝ => x⁻¹ ) ( Phi_deg3_reduced_eq a b ?_ ?_ ) using 1;
      · grind;
      · rw [ Polynomial.splits_iff_card_roots ] ; aesop;
      · tauto;
    · by_cases ha : a = 0 <;> simp_all +decide [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ];
  have h_ineq : ∀ (a1 a2 b1 b2 : ℝ), a1 < 0 → a2 < 0 → a1 + a2 < 0 → ((b1 + b2) / (a1 + a2))^2 ≤ (b1 / a1)^2 + (b2 / a2)^2 := by
    intros a1 a2 b1 b2 ha1 ha2 ha1a2
    have h_ineq : ((b1 + b2)^2 / (a1 + a2)^2) ≤ (b1^2 / a1^2) + (b2^2 / a2^2) := by
      have := n3_inequality b1 b2 ( -a1 ) ( -a2 ) ( by linarith ) ( by linarith ) ; ring_nf at *; linarith;
    simpa only [ div_pow ] using h_ineq;
  have h_ineq_applied : a1 < 0 ∧ a2 < 0 ∧ a1 + a2 < 0 := by
    have h_card : (Polynomial.X ^ 3 + Polynomial.C a1 * Polynomial.X + Polynomial.C b1).roots.toFinset.card = 3 ∧ (Polynomial.X ^ 3 + Polynomial.C a2 * Polynomial.X + Polynomial.C b2).roots.toFinset.card = 3 ∧ (Polynomial.X ^ 3 + Polynomial.C (a1 + a2) * Polynomial.X + Polynomial.C (b1 + b2)).roots.toFinset.card = 3 := by
      have h_card : ∀ (p : Polynomial ℝ), p.Splits (RingHom.id ℝ) → p.roots.Nodup → p.natDegree = 3 → p.roots.toFinset.card = 3 := by
        intros p hp hp_nodup hp_deg
        have h_card : p.roots.toFinset.card = p.natDegree := by
          rw [ Multiset.toFinset_card_of_nodup hp_nodup ];
          exact?;
        rw [h_card, hp_deg];
      refine ⟨ h_card _ h_real1 h_nodup1 ?_, h_card _ h_real2 h_nodup2 ?_, h_card _ h_real3 h_nodup3 ?_ ⟩ <;> erw [ Polynomial.natDegree_add_C ] <;> erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a1 = 0 <;> by_cases hb : a2 = 0 <;> norm_num [ ha, hb ];
      exact lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) ( by by_cases ha : a1 + a2 = 0 <;> simp +decide [ ha ] );
    exact ⟨ cubic_distinct_real_roots_implies_a_neg a1 b1 h_card.1, cubic_distinct_real_roots_implies_a_neg a2 b2 h_card.2.1, cubic_distinct_real_roots_implies_a_neg ( a1 + a2 ) ( b1 + b2 ) h_card.2.2 ⟩;
  rw [ hPhi_def _ _ h_real1 h_nodup1, hPhi_def _ _ h_real2 h_nodup2, hPhi_def _ _ h_real3 h_nodup3 ] ; linarith [ h_ineq a1 a2 b1 b2 h_ineq_applied.1 h_ineq_applied.2.1 h_ineq_applied.2.2 ] ;

/-
Centered boxplus preserves centering.
-/
lemma boxplus_centered_is_centered (n : ℕ) (p q : ℝ[X])
  (hp : is_centered n p) (hq : is_centered n q) :
  is_centered n (boxplus n p q) := by
  refine' ⟨ _, _, _ ⟩;
  · have h_leading_coeff : Polynomial.coeff (boxplus n p q) n = 1 := by
      unfold boxplus;
      simp +zetaDelta at *;
      rw [ Finset.sum_eq_single 0 ] <;> norm_num;
      · unfold boxplus_coeff;
        simp +decide [ ← hp.2.1, ← hq.2.1, hp.1.coeff_natDegree, hq.1.coeff_natDegree, Nat.factorial_ne_zero ];
        rw [ hp.2.1, hq.2.1.symm, hq.1.coeff_natDegree ];
      · intros; omega;
    rwa [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
    refine' Polynomial.degree_eq_of_le_of_coeff_ne_zero _ _;
    · refine' le_trans ( Polynomial.degree_sum_le _ _ ) _;
      exact Finset.sup_le fun i hi => le_trans ( Polynomial.degree_C_mul_X_pow_le _ _ ) ( WithBot.coe_le_coe.mpr ( Nat.sub_le _ _ ) );
    · aesop;
  · have h_deg : (boxplus n p q).natDegree ≤ n := by
      exact le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le fun i hi => Polynomial.natDegree_C_mul_X_pow_le _ _ |> le_trans <| by aesop );
    refine' le_antisymm h_deg ( Polynomial.le_natDegree_of_ne_zero _ );
    unfold boxplus;
    simp +zetaDelta at *;
    rw [ Finset.sum_eq_single 0 ] <;> norm_num;
    · unfold boxplus_coeff; norm_num [ hp.1.leadingCoeff, hq.1.leadingCoeff ];
      exact ⟨ ⟨ Nat.factorial_ne_zero _, by rw [ ← hp.2.1, hp.1.coeff_natDegree ] ; aesop ⟩, by rw [ ← hq.2.1, hq.1.coeff_natDegree ] ; aesop ⟩;
    · intros; omega;
  · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ];
    · unfold is_centered at * ; aesop;
    · have := hp.2.2; have := hq.2.2; unfold boxplus; norm_num [ Polynomial.coeff_eq_zero_of_natDegree_lt, hp.1, hq.1, hp.2.1, hq.2.1 ] ;
      unfold boxplus_coeff; norm_num [ Finset.sum_range_succ', ‹p.coeff 0 = 0›, ‹q.coeff 0 = 0› ] ;
    · unfold is_centered at *;
      unfold boxplus; simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt, Finset.sum_range_succ' ] ;
      unfold boxplus_coeff; simp_all +decide [ Finset.sum_range_succ', Nat.factorial_ne_zero ] ;
      exact Finset.sum_eq_zero fun x hx => if_neg ( by omega )

/-
For centered polys of degree n ≥ 2, the (n-2)-th coefficient is additive under boxplus.
-/
lemma boxplus_centered_coeff_add (n : ℕ) (p q : ℝ[X])
  (hp : is_centered n p) (hq : is_centered n q) :
  (boxplus n p q).coeff (n - 2) = p.coeff (n - 2) + q.coeff (n - 2) := by
  have h_coeff : (boxplus n p q).coeff (n - 2) = ∑ i ∈ Finset.range (2 + 1), (Nat.factorial (n - i) * Nat.factorial (n - (2 - i))) / (Nat.factorial n * Nat.factorial (n - 2) : ℝ) * p.coeff (n - i) * q.coeff (n - (2 - i)) := by
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ ];
    · unfold is_centered at * ; aesop;
    · unfold boxplus; norm_num [ Finset.sum_range_succ' ] ; ring;
      unfold boxplus_coeff; norm_num [ Finset.sum_range_succ ] ; ring;
      cases hp ; cases hq ; aesop;
    · unfold boxplus;
      simp +decide [ Finset.sum_range_succ', Polynomial.coeff_C, Polynomial.coeff_X_pow ];
      rw [ Finset.sum_eq_zero ] <;> norm_num +decide [ Nat.factorial_ne_zero ];
      · unfold boxplus_coeff; norm_num [ Nat.factorial_succ, Finset.sum_range_succ' ] ; ring;
        field_simp;
        grind;
      · intros; omega;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ' ];
  · cases hp ; cases hq ; aesop;
  · cases hp ; cases hq ; aesop;
  · simp_all +decide [ Nat.factorial_ne_zero, mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv ];
    simp_all +decide [ is_centered, Nat.factorial_succ ];
    have := hp.1.coeff_natDegree; have := hq.1.coeff_natDegree; aesop;

-- ============================================================================
-- The main theorem (to be proved)
-- ============================================================================

theorem finite_free_stam_inequality (n : ℕ) (hn : n ≥ 2)
    (p q : ℝ[X])
    (hp : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n)
    (hpq : (boxplus n p q).Splits (RingHom.id ℝ))
    (hpq_nodup : (boxplus n p q).roots.Nodup) :
    invPhi (boxplus n p q) ≥ invPhi p + invPhi q := by
  sorry
