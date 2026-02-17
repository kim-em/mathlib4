/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0880c091-bf67-40cd-992c-4e3445d0ff9c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Merged context file combining results from multiple Aristotle queries.

Sources:
  AristotleQuery23 (uuid: 1c13b089-f516-4cd6-9c14-39f2fd984344):
    Base file -- cumulant algebra, shift invariance, n=2 proof, n=3 general proof.
  AristotleQuery19 (merged Q14 + Q15 + Q4):
    Additional items: ff_kappa_additive_v2, boxplus_deriv_at_zero,
    boxplus_centered_is_centered, boxplus_centered_coeff_add.
  AristotleQuery25 (uuid: 3789cf67-3fe8-409f-9581-8aeccf8f7aea):
    Additional items: power_sum_add, sum_residues_eq_zero_of_deg_le,
    dvd_pow_two_of_isRoot_of_isRoot_derivative, roots_mul_deriv_nodup,
    natDegree_derivative_eq_natDegree_sub_one, splits_derivative,
    deg_P_plus_two_le_deg_Q, Phi_eq_sum_roots_deriv.
  AristotleQuery28 (uuid: 3fa7f60c-b216-4518-a554-74058622e9f9):
    Additional items: Phi_symmetric_quartic_formula, Phi_eq_Phi_symmetric_quartic_formula,
    invPhi_symmetric_quartic_formula, invPhi_eq_invPhi_symmetric_quartic_formula,
    f_aux, f_aux_second_deriv, f_aux_increasing, f_aux_decreasing,
    invPhi_sym_param, invPhi_sym_param_eq, invPhi_sym_param_arg_diff.
  AristotleQ32 (uuid: 50080d30-c798-4bd9-aa5e-b0ee4db8ff0f):
    Additional items: shift_to_center_amount, shifted_to_center,
    shifted_to_center_is_centered, shifted_to_center_properties,
    finite_free_stam_inequality_centered_sufficient,
    boxplus_centered_coeff_n_sub_2, Phi_quadratic_centered,
    Phi_cubic_centered_formula, boxplus_centered_cubic_coeff_0,
    invPhi_cubic_centered_formula, invPhi_eq_invPhi_cubic_centered_formula,
    algebraic_stam_inequality_n3, cubic_discriminant_neg_of_nodup_splits,
    finite_free_stam_inequality_centered_n3,
    quadratic_centered_coeff_neg, finite_free_stam_inequality_centered_n2,
    boxplus_symmetric_quartic_coeffs, boxplus_symmetric_quartic_is_symmetric,
    g_aux, g_aux_second_deriv, g_aux_convex_on,
    F_aux, F_aux_eq_a_mul_g_aux, h_aux, F_aux_eq_neg_a_mul_h_aux.
  AristotleQ33 (uuid: 9be88ef5-0a93-42c5-9554-69c37b62aaee):
    Additional items: f_aux_concave, f_aux_ineq_easy_case, f_aux_ineq_case2_easy,
    poly_diff, poly_diff_symmetry, poly_diff_subst.

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

/-
Definitions of boxplus convolution, Phi functional, and inverse Phi functional from the context.
-/
open scoped BigOperators Real Nat Classical Pointwise

open Polynomial BigOperators Finset Classical

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
Lemmas about boxplus and Phi from the context.
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

lemma roots_card_eq_natDegree (p : ℝ[X])
    (h_splits : p.Splits (RingHom.id ℝ)) (h_monic : p.Monic) :
    p.roots.card = p.natDegree := by
  rw [Polynomial.splits_iff_card_roots] at h_splits
  exact h_splits

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
Definition of scaled coefficients and their relation to boxplus convolution.
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
Definition of the 4th finite free cumulant and its additivity for centered polynomials.
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
Definitions of cumulants, binomial convolution, and sequence derivative, along with the product rule for sequence derivative.
-/
def cumulant (c : ℕ → ℝ) : ℕ → ℝ
| 0 => 0
| k + 1 => c (k + 1) - ∑ i ∈ (range k).attach, (Nat.choose k i.1) * c (k - i.1) * cumulant c (i.1 + 1)
termination_by k => k
decreasing_by
  simp_wf
  have h : i.val < k := Finset.mem_range.mp i.property
  omega

def kappa (n : ℕ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  cumulant (fun i => scaled_coeff n p i) k

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
Definitions of finite free cumulants, binomial convolution, and sequence derivative.
-/
def ff_cumulant (c : ℕ → ℝ) : ℕ → ℝ
| 0 => 0
| k + 1 => c (k + 1) - ∑ i ∈ (range k).attach, (Nat.choose k i.1) * c (k - i.1) * ff_cumulant c (i.1 + 1)
termination_by k => k
decreasing_by
  simp_wf
  have h : i.val < k := Finset.mem_range.mp i.property
  omega

def ff_kappa (n : ℕ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  ff_cumulant (fun i => scaled_coeff n p i) k

def ff_binom_conv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (Nat.choose n i) * a i * b (n - i)

def ff_seq_deriv (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1)

/-
Product rule for the sequence derivative of a binomial convolution (ff_ version).
-/
lemma ff_seq_deriv_binom_conv (a b : ℕ → ℝ) (n : ℕ) :
    ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_seq_deriv a) b n + ff_binom_conv a (ff_seq_deriv b) n := by
      apply seq_deriv_binom_conv

/-
Commutativity of binomial convolution (ff_ version).
-/
lemma ff_binom_conv_comm (a b : ℕ → ℝ) (n : ℕ) :
    ff_binom_conv a b n = ff_binom_conv b a n := by
      convert Finset.sum_bij ( fun i hi => n - i ) _ _ _ _ <;> simp +decide [ Nat.choose_symm_add ];
      · exact fun i hi => Nat.lt_succ_of_le ( Nat.sub_le _ _ );
      · intros; omega;
      · exact fun b hb => ⟨ n - b, by omega, by omega ⟩;
      · exact fun i hi => by rw [ Nat.choose_symm ( Nat.le_of_lt_succ hi ), tsub_tsub_cancel_of_le ( Nat.le_of_lt_succ hi ) ] ; ring;

/-
Associativity of binomial convolution (ff_ version).
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
Definition of shifted cumulant and its relation to sequence derivative.
-/
def ff_shifted_cumulant (c : ℕ → ℝ) (n : ℕ) : ℝ := ff_cumulant c (n + 1)

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
Distributivity of binomial convolution over addition (ff_ version).
-/
lemma ff_binom_conv_add (a b c : ℕ → ℝ) (n : ℕ) :
    ff_binom_conv a (b + c) n = ff_binom_conv a b n + ff_binom_conv a c n := by
      -- By definition of ff_binom_conv, we can expand both sides.
      simp [ff_binom_conv];
      simpa only [ mul_add, Finset.sum_add_distrib ]

/-
Left cancellation for binomial convolution (ff_ version).
-/
lemma ff_binom_conv_cancel_left (a b c : ℕ → ℝ) (ha0 : a 0 ≠ 0)
    (h : ff_binom_conv a b = ff_binom_conv a c) : b = c := by
      funext n;
      induction' n using Nat.strong_induction_on with n ih;
      replace h := congr_fun h n; simp_all +decide [ ff_binom_conv ] ;
      rw [ Finset.sum_range_succ', Finset.sum_range_succ' ] at h;
      rw [ Finset.sum_congr rfl fun i hi => by rw [ ih _ ( by { rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_range.mp hi ] } ) ] ] at h ; aesop

/-
Additivity of shifted cumulants under binomial convolution (ff_ version).
-/
lemma ff_shifted_cumulant_additive (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ff_shifted_cumulant (ff_binom_conv a b) = ff_shifted_cumulant a + ff_shifted_cumulant b := by
      -- Apply the lemma that states the sequence derivative of the binomial convolution of two sequences is the sum of the binomial convolutions of the sequence derivatives.
      have h_seq_deriv : ∀ n, ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_binom_conv a b) (ff_shifted_cumulant a + ff_shifted_cumulant b) n := by
        intros n
        have h_seq_deriv : ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_binom_conv a b) (ff_shifted_cumulant a + ff_shifted_cumulant b) n := by
          have h_seq_deriv : ff_seq_deriv (ff_binom_conv a b) n = ff_binom_conv (ff_seq_deriv a) b n + ff_binom_conv a (ff_seq_deriv b) n := by
            exact ff_seq_deriv_binom_conv a b n
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

/-
Additivity of shifted cumulants under binomial convolution (ff_ version, v2).
-/
lemma ff_shifted_cumulant_additive_v2 (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1) :
    ff_shifted_cumulant (ff_binom_conv a b) = ff_shifted_cumulant a + ff_shifted_cumulant b := by
      convert ff_shifted_cumulant_additive a b ha0 hb0 using 1

/-
Congruence lemma for finite free cumulants.
-/
lemma ff_cumulant_congr (a b : ℕ → ℝ) (n : ℕ) (h : ∀ k, k ≤ n → a k = b k) :
    ff_cumulant a n = ff_cumulant b n := by
      induction' n using Nat.case_strong_induction_on with n ih;
      · unfold ff_cumulant; aesop;
      · unfold ff_cumulant;
        exact congrArg₂ _ ( h _ le_rfl ) ( Finset.sum_congr rfl fun i hi => by rw [ h _ ( Nat.sub_le_of_le_add <| by linarith [ Finset.mem_range.mp i.2 ] ), ih _ ( by linarith [ Finset.mem_range.mp i.2 ] ) fun k hk => h _ <| by linarith [ Finset.mem_range.mp i.2 ] ] )

/-
Finite free cumulants are additive for k <= n.
-/
theorem ff_kappa_additive (n : ℕ) (p q : ℝ[X])
    (hp : p.Monic) (hq : q.Monic) (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    ∀ k, k ≤ n → ff_kappa n (boxplus n p q) k = ff_kappa n p k + ff_kappa n q k := by
      have h_linear : ∀ (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1), ∀ k ≤ n, ff_cumulant (ff_binom_conv a b) k = ff_cumulant a k + ff_cumulant b k := by
        intros a b ha0 hb0 k hk_le_n
        have h_shifted_cumulant_additive : ff_shifted_cumulant (ff_binom_conv a b) = ff_shifted_cumulant a + ff_shifted_cumulant b := by
          exact ff_shifted_cumulant_additive_v2 a b ha0 hb0
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
Finite free cumulants are additive under binomial convolution (ff_ version).
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
Phi is invariant under translation.
-/
lemma Phi_comp_add_C (p : ℝ[X]) (c : ℝ) :
  Phi (p.comp (X + C c)) = Phi p := by
    -- By definition of polynomial composition, the roots of $p(x+c)$ are $r_i - c$ where $r_i$ are the roots of $p(x)$.
    have h_roots : (p.comp (Polynomial.X + Polynomial.C c)).roots.toFinset = Finset.image (fun r => r - c) p.roots.toFinset := by
      ext; simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C];
      rw [ Polynomial.comp_eq_zero_iff ] ; aesop;
    unfold Phi;
    rw [ h_roots, Finset.sum_image ] <;> norm_num;
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ show ( Multiset.map ( fun r => r - c ) p.roots ).toFinset.erase ( x - c ) = Finset.image ( fun r => r - c ) ( p.roots.toFinset.erase x ) from ?_, Finset.sum_image ] <;> aesop

/-
invPhi is invariant under translation.
-/
lemma invPhi_comp_add_C (p : ℝ[X]) (c : ℝ) :
  invPhi (p.comp (X + C c)) = invPhi p := by
    unfold invPhi;
    rw [ show ( Polynomial.comp p ( Polynomial.X + Polynomial.C c ) |> Polynomial.roots ) = Multiset.map ( fun x => x - c ) ( p.roots ) from ?_ ];
    · by_cases h : Multiset.Nodup p.roots ∧ 1 < Multiset.card p.roots <;> simp_all +decide [ Multiset.nodup_map_iff_of_injective, Function.Injective ];
      · exact?;
      · grind;
    · ext x;
      rw [ Multiset.count_map ];
      rw [ show ( Polynomial.comp p ( Polynomial.X + Polynomial.C c ) |> Polynomial.roots ) = Multiset.map ( fun y => y - c ) ( p.roots ) from ?_ ];
      · rw [ Multiset.count_map ];
      · ext y; simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C];
        have h_mult : Polynomial.rootMultiplicity y (p.comp (Polynomial.X + Polynomial.C c)) = Polynomial.rootMultiplicity (y + c) p := by
          rw [ Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.rootMultiplicity_eq_natTrailingDegree ];
          norm_num [ add_assoc, Polynomial.comp_assoc ];
        rw [ Multiset.count_map ];
        rw [ show ( Multiset.filter ( fun a => y = a - c ) p.roots ) = Multiset.filter ( fun a => a = y + c ) p.roots by congr; ext; constructor <;> intro <;> linarith ] ; rw [ Multiset.filter_eq' ] ; aesop

/-
The boxplus convolution of two monomials X^u and X^v is a monomial X^(u+v-n) scaled by a factor involving factorials, provided u+v >= n. Otherwise it is zero.
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
Translation covariance holds for monomials: boxplus of (X+c)^u and X^v is the shifted boxplus of X^u and X^v.
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
Any monic polynomial of positive degree can be shifted to have zero trace (second highest coefficient).
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

/-
The boxplus convolution commutes with translation of the first argument for any polynomials of degree at most n.
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
The boxplus convolution is fully translation covariant (inequality version).
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
      apply boxplus_comp_add_C_left_le n p q c hp hq
    rw [ h_lhs, h_rhs, ← boxplus_comm ];
    rw [ h_rhs'', Polynomial.comp_assoc ];
    norm_num [ Polynomial.comp_assoc ];
    exact congr_arg _ ( by ring )

/-
Cauchy-Schwarz type inequality for n=3 case.
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

/-
A reduced cubic with 3 distinct real roots must have a negative linear coefficient.
-/
lemma cubic_distinct_real_roots_implies_a_neg (a b : ℝ)
  (h_roots : (X^3 + C a * X + C b).roots.toFinset.card = 3) :
  a < 0 := by
    by_contra h_contra; push_neg at h_contra; (
    have h_increasing : StrictMono (fun x : ℝ => x^3 + a * x + b) := by
      exact fun x y hxy => by norm_num; nlinarith [ sq_nonneg ( x^2 - y^2 ), pow_pos ( sub_pos.mpr hxy ) 3, mul_le_mul_of_nonneg_left hxy.le h_contra ] ;
    exact absurd h_roots ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_one.mpr ( by intros x hx y hy; exact h_increasing.injective <| by aesop ) ) ( by norm_num ) ) ));

/-
Explicit formula for boxplus of reduced cubic polynomials.
-/
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
The Finite Free Stam Inequality holds for reduced cubic polynomials.
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
    -- By definition of $Phi$, we know that
    have hPhi_def : ∀ a b : ℝ, (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots.Nodup → (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots.toFinset.card = 3 → invPhi (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b) = -2 / 9 * a - 3 / 2 * (b / a)^2 := by
      intros a b h_nodup h_card
      have h_a_neg : a < 0 := by
        exact?
      have hPhi : Phi (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b) = 18 * a^2 / (-4 * a^3 - 27 * b^2) := by
        apply_rules [ Phi_deg3_reduced_eq ];
        rw [ Polynomial.splits_iff_card_roots ];
        rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp_all +decide;
        exact le_antisymm ( le_trans ( Polynomial.card_roots' _ ) ( by erw [ Polynomial.natDegree_add_C ] ; erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> aesop ) ) ( by exact_mod_cast h_card ▸ Multiset.toFinset_card_le _ )
      have h_invPhi : invPhi (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b) = 1 / (18 * a^2 / (-4 * a^3 - 27 * b^2)) := by
        rw [ ← hPhi, invPhi ];
        rw [ if_pos ⟨ h_nodup, by linarith [ Multiset.toFinset_card_le ( Polynomial.roots ( Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b ) ) ] ⟩ ]
      rw [h_invPhi]
      field_simp [hPhi]
      ring;
    -- By definition of $Phi$, we know that the roots of the polynomials are distinct and real.
    have h_roots_distinct_real : ∀ a b : ℝ, (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots.Nodup → (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots.toFinset.card = 3 → a < 0 := by
      exact?;
    have h_card_roots : (Polynomial.X^3 + Polynomial.C a1 * Polynomial.X + Polynomial.C b1).roots.toFinset.card = 3 ∧ (Polynomial.X^3 + Polynomial.C a2 * Polynomial.X + Polynomial.C b2).roots.toFinset.card = 3 ∧ (Polynomial.X^3 + Polynomial.C (a1 + a2) * Polynomial.X + Polynomial.C (b1 + b2)).roots.toFinset.card = 3 := by
      have h_card_roots : ∀ p : Polynomial ℝ, p.natDegree = 3 → p.Splits (RingHom.id ℝ) → p.roots.Nodup → p.roots.toFinset.card = 3 := by
        intros p hp_deg hp_splits hp_nodup
        have h_card_roots : p.roots.toFinset.card = p.natDegree := by
          rw [ Multiset.toFinset_card_of_nodup hp_nodup ];
          exact?
        rw [h_card_roots, hp_deg];
      refine' ⟨ h_card_roots _ _ h_real1 h_nodup1, h_card_roots _ _ h_real2 h_nodup2, h_card_roots _ _ h_real3 h_nodup3 ⟩;
      · rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha1 : a1 = 0 <;> simp +decide [ ha1 ];
      · rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha2 : a2 = 0 <;> simp +decide [ ha2 ];
      · rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases h : a1 + a2 = 0 <;> simp +decide [ h ];
        exact lt_of_le_of_lt ( Polynomial.natDegree_mul_le .. ) ( by by_cases ha1 : a1 = 0 <;> by_cases ha2 : a2 = 0 <;> simp +decide [ * ] );
    rw [ hPhi_def a1 b1 h_nodup1 h_card_roots.1, hPhi_def a2 b2 h_nodup2 h_card_roots.2.1, hPhi_def ( a1 + a2 ) ( b1 + b2 ) h_nodup3 h_card_roots.2.2 ];
    have := n3_inequality ( b1 ) ( b2 ) ( -a1 ) ( -a2 ) ( by linarith [ h_roots_distinct_real a1 b1 h_nodup1 h_card_roots.1 ] ) ( by linarith [ h_roots_distinct_real a2 b2 h_nodup2 h_card_roots.2.1 ] );
    ring_nf at this ⊢;
    field_simp;
    rw [ show ( a1 + a2 ) ^ 2 = ( a1 * a2 * 2 + a1 ^ 2 + a2 ^ 2 ) by ring ] ; ring_nf at * ; linarith

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
invPhi of boxplus is invariant under shifting the input polynomials.
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
The degree of p(x+c) is the same as the degree of p(x).
-/
lemma natDegree_comp_X_add_C (p : ℝ[X]) (c : ℝ) :
  (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

/-
The roots of p(x+c) are the roots of p(x) shifted by -c.
-/
lemma roots_comp_X_add_C (p : ℝ[X]) (c : ℝ) :
  (p.comp (X + C c)).roots = p.roots.map (fun r => r - c) := by
    ext x;
    have h_root_shift : Polynomial.rootMultiplicity x (p.comp (Polynomial.X + Polynomial.C c)) = Polynomial.rootMultiplicity (x + c) p := by
      rw [ Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.rootMultiplicity_eq_natTrailingDegree ];
      norm_num [ add_assoc, Polynomial.comp_assoc ];
    rw [ Multiset.count_map ];
    rw [ show ( Multiset.filter ( fun a => x = a - c ) p.roots ) = Multiset.filter ( fun a => a = x + c ) p.roots by congr; ext; constructor <;> intro <;> linarith ] ; rw [ Multiset.filter_eq' ] ; aesop

/-
The Finite Free Stam Inequality holds for n=3.
-/
theorem finite_free_stam_inequality_n3 (p q : ℝ[X])
    (hp : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hp_monic : p.Monic) (hp_deg : p.natDegree = 3)
    (hq : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = 3)
    (hpq : (boxplus 3 p q).Splits (RingHom.id ℝ))
    (hpq_nodup : (boxplus 3 p q).roots.Nodup) :
    invPhi (boxplus 3 p q) ≥ invPhi p + invPhi q := by
      -- Apply the conjecture_n_3_reduced lemma to the reduced cubic polynomials.
      have := @conjecture_n_3_reduced;
      norm_num +zetaDelta at *;
      obtain ⟨c, hc⟩ : ∃ c : ℝ, (p.comp (X + C c)).coeff 2 = 0 := by
        have := exists_shift_centered 3 p ( by norm_num ) hp_monic hp_deg; aesop;
      obtain ⟨d, hd⟩ : ∃ d : ℝ, (q.comp (X + C d)).coeff 2 = 0 := by
        convert exists_shift_centered 3 q ( by norm_num ) hq_monic hq_deg using 1;
      -- By definition of $pc$ and $qd$, we know that $pc = X^3 + a1*X + b1$ and $qd = X^3 + a2*X + b2$ for some $a1, b1, a2, b2$.
      obtain ⟨a1, b1, ha1⟩ : ∃ a1 b1 : ℝ, p.comp (X + C c) = Polynomial.X^3 + Polynomial.C a1 * Polynomial.X + Polynomial.C b1 := by
        use (p.comp (X + C c)).coeff 1, (p.comp (X + C c)).coeff 0;
        conv_lhs => rw [ Polynomial.as_sum_range_C_mul_X_pow ( p.comp ( Polynomial.X + Polynomial.C c ) ) ] ; simp +decide [ Finset.sum_range_succ', Polynomial.natDegree_comp, Polynomial.natDegree_add_eq_left_of_natDegree_lt, hp_deg ] ;
        simp_all +decide [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
        norm_num [ Finset.sum_range_succ', Polynomial.coeff_X_add_C_pow ] at *;
        rw [ ← hp_deg, hp_monic.coeff_natDegree ] ; norm_num
      obtain ⟨a2, b2, ha2⟩ : ∃ a2 b2 : ℝ, q.comp (X + C d) = Polynomial.X^3 + Polynomial.C a2 * Polynomial.X + Polynomial.C b2 := by
        simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_comp, Polynomial.natDegree_add_eq_left_of_natDegree_lt ];
        norm_num [ Polynomial.comp, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ', hq_deg ] at hd ⊢;
        norm_num [ Polynomial.coeff_X, Polynomial.coeff_C, add_mul, pow_succ' ] at hd ⊢;
        norm_num [ hq_monic ] at hd ⊢;
        exact ⟨ q.coeff 1 + d * d * 3 + q.coeff 2 * d * 2, q.coeff 0 + d * d * d + q.coeff 2 * d * d + q.coeff 1 * d, by exact Polynomial.funext fun x => by norm_num; rw [ show q.coeff 2 = -d * 3 by linarith ] ; ring ⟩;
      -- By definition of $pc$ and $qd$, we know that $pc boxplus qd = X^3 + (a1 + a2)X + (b1 + b2)$.
      have h_boxplus : boxplus 3 (p.comp (X + C c)) (q.comp (X + C d)) = Polynomial.X^3 + Polynomial.C (a1 + a2) * Polynomial.X + Polynomial.C (b1 + b2) := by
        convert boxplus_deg3_reduced_eq _ _ _ _ _ _ _ _ using 1 <;> norm_num [ ha1, ha2 ];
        · rw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha1 : a1 = 0 <;> simp +decide [ ha1 ];
        · rw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha2 : a2 = 0 <;> simp +decide [ ha2 ];
        · rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha1 : a1 = 0 <;> simp +decide [ ha1 ];
        · rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha2 : a2 = 0 <;> simp +decide [ ha2 ];
      have h_splits : Polynomial.Splits (RingHom.id ℝ) (Polynomial.X^3 + Polynomial.C a1 * Polynomial.X + Polynomial.C b1) ∧ Polynomial.Splits (RingHom.id ℝ) (Polynomial.X^3 + Polynomial.C a2 * Polynomial.X + Polynomial.C b2) ∧ Polynomial.Splits (RingHom.id ℝ) (Polynomial.X^3 + Polynomial.C (a1 + a2) * Polynomial.X + Polynomial.C (b1 + b2)) := by
        have h_splits : Polynomial.Splits (RingHom.id ℝ) (p.comp (X + C c)) ∧ Polynomial.Splits (RingHom.id ℝ) (q.comp (X + C d)) ∧ Polynomial.Splits (RingHom.id ℝ) (boxplus 3 (p.comp (X + C c)) (q.comp (X + C d))) := by
          refine' ⟨ _, _, _ ⟩;
          · exact?;
          · exact?;
          · convert hpq.comp_X_add_C ( c + d ) using 1;
            convert boxplus_comp_add_C 3 p q c d _ _ using 1 <;> norm_num [ hp_deg, hq_deg ];
        aesop;
      have h_nodup : (Polynomial.X^3 + Polynomial.C a1 * Polynomial.X + Polynomial.C b1).roots.Nodup ∧ (Polynomial.X^3 + Polynomial.C a2 * Polynomial.X + Polynomial.C b2).roots.Nodup ∧ (Polynomial.X^3 + Polynomial.C (a1 + a2) * Polynomial.X + Polynomial.C (b1 + b2)).roots.Nodup := by
        have h_nodup : (p.comp (X + C c)).roots.Nodup ∧ (q.comp (X + C d)).roots.Nodup ∧ (boxplus 3 (p.comp (X + C c)) (q.comp (X + C d))).roots.Nodup := by
          have h_nodup : (p.comp (X + C c)).roots.Nodup ∧ (q.comp (X + C d)).roots.Nodup := by
            have h_nodup : ∀ (p : ℝ[X]) (c : ℝ), p.roots.Nodup → (p.comp (X + C c)).roots.Nodup := by
              intros p c hp_nodup
              have h_roots : (p.comp (X + C c)).roots = p.roots.map (fun r => r - c) := by
                exact?;
              rw [ h_roots, Multiset.nodup_map_iff_inj_on ] ; aesop;
              exact hp_nodup;
            exact ⟨ h_nodup p c hp_nodup, h_nodup q d hq_nodup ⟩;
          have h_nodup : (boxplus 3 (p.comp (X + C c)) (q.comp (X + C d))).roots.Nodup := by
            have h_shift : boxplus 3 (p.comp (X + C c)) (q.comp (X + C d)) = (boxplus 3 p q).comp (X + C (c + d)) := by
              convert boxplus_comp_add_C 3 p q c d _ _ using 1 <;> norm_num [ hp_deg, hq_deg ]
            rw [ h_shift, roots_comp_X_add_C ];
            exact Multiset.Nodup.map ( fun x => by aesop ) hpq_nodup;
          tauto;
        aesop;
      convert this a1 b1 a2 b2 h_splits.1 h_nodup.1 h_splits.2.1 h_nodup.2.1 ( by simpa using h_splits.2.2 ) ( by simpa using h_nodup.2.2 ) using 1;
      · rw [ ← ha1, ← ha2, invPhi_comp_add_C, invPhi_comp_add_C ];
      · convert invPhi_boxplus_shift_invariance 3 p q c d ( by linarith ) ( by linarith ) using 1;
        rw [ h_boxplus ] ; norm_num [ add_mul, add_assoc ]

-- ============================================================================
-- Additional results from AristotleQuery19 (not present in AristotleQuery23)
-- ============================================================================

/-
Finite free cumulants are additive for k <= n (v2).
-/
theorem ff_kappa_additive_v2 (n : ℕ) (p q : ℝ[X])
    (hp : p.Monic) (hq : q.Monic) (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    ∀ k, k ≤ n → ff_kappa n (boxplus n p q) k = ff_kappa n p k + ff_kappa n q k := by
      convert ff_kappa_additive n p q hp hq hp_deg hq_deg using 1

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
-- Additional results from AristotleQuery25
-- ============================================================================

/-
Definition of power sums and proof of additivity for non-zero polynomials.
-/
def power_sum (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  (p.roots.map (fun r => r ^ k)).sum

lemma power_sum_add (p q : Polynomial ℝ) (k : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) :
    power_sum (p * q) k = power_sum p k + power_sum q k := by
  simp [power_sum]
  rw [Polynomial.roots_mul]
  · simp only [Multiset.map_add, Multiset.sum_add]
  · exact mul_ne_zero hp hq

/-
The sum of P(r)/Q'(r) over the roots r of Q is zero if deg(P) + 2 <= deg(Q).
-/
lemma sum_residues_eq_zero_of_deg_le (P Q : Polynomial ℝ)
    (h_deg : P.natDegree + 2 ≤ Q.natDegree)
    (h_splits : Q.Splits (RingHom.id ℝ))
    (h_nodup : Q.roots.Nodup) :
    (Q.roots.map (fun r => P.eval r / Q.derivative.eval r)).sum = 0 := by
  -- By the properties of the derivative and roots, we can express $P(x)$ as a sum of its partial fractions at the roots of $Q(x)$.
  have h_partial_fractions : ∀ x, x ∉ Q.roots → P.eval x / Q.eval x = ∑ r ∈ Q.roots.toFinset, (P.eval r) / (Q.derivative.eval r) * (1 / (x - r)) := by
    -- Since $Q$ splits into linear factors over the reals and has distinct roots, we can write it as $Q(x) = c \prod_{r \in Q.roots} (x - r)$ for some constant $c$.
    obtain ⟨c, hc⟩ : ∃ c : ℝ, Q = Polynomial.C c * Finset.prod Q.roots.toFinset (fun r => Polynomial.X - Polynomial.C r) := by
      use Q.leadingCoeff;
      convert Polynomial.eq_prod_roots_of_splits_id h_splits using 1;
      rw [ ← Multiset.toFinset_eq ] ; aesop;
    -- By the properties of the derivative and roots, we can express $P(x)$ as a sum of its partial fractions at the roots of $Q(x)$ using the fact that $Q(x)$ splits into linear factors over the reals.
    have h_partial_fractions : ∀ x, x ∉ Q.roots → P.eval x / Q.eval x = ∑ r ∈ Q.roots.toFinset, (P.eval r) / (Q.derivative.eval r) * (1 / (x - r)) := by
      intro x hx
      have h_eval : P.eval x = ∑ r ∈ Q.roots.toFinset, (P.eval r) * (∏ s ∈ Q.roots.toFinset \ {r}, (x - s)) / (∏ s ∈ Q.roots.toFinset \ {r}, (r - s)) := by
        have h_eval : P = Finset.sum Q.roots.toFinset (fun r => Polynomial.C (P.eval r / (∏ s ∈ Q.roots.toFinset \ {r}, (r - s))) * (∏ s ∈ Q.roots.toFinset \ {r}, (Polynomial.X - Polynomial.C s))) := by
          refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
          exact Q.roots.toFinset;
          · refine' lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) ( max_lt _ _ );
            · refine' lt_of_le_of_lt ( Polynomial.degree_le_natDegree ) _;
              rw [ hc, Polynomial.natDegree_C_mul ] at h_deg <;> norm_num at *;
              · linarith;
              · rintro rfl; norm_num at *;
            · refine' lt_of_le_of_lt ( Polynomial.degree_sum_le _ _ ) ( Finset.sup_lt_iff _ |>.2 _ );
              · exact WithBot.bot_lt_coe _;
              · intro r hr; rw [ Polynomial.degree_mul, Polynomial.degree_prod, Finset.sum_congr rfl fun s hs => Polynomial.degree_X_sub_C _ ] ; norm_num [ Finset.card_sdiff, hr ] ;
                exact lt_of_le_of_lt ( add_le_add ( Polynomial.degree_C_le ) le_rfl ) ( by norm_cast; linarith [ Finset.card_pos.mpr ⟨ r, hr ⟩, Nat.sub_add_cancel ( Finset.card_pos.mpr ⟨ r, hr ⟩ ) ] );
          · intro r hr; rw [ Polynomial.eval_finset_sum, Finset.sum_eq_single r ] <;> norm_num [ hr ];
            · simp +decide [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero ];
            · intro b hb hb' hb''; rw [ Polynomial.eval_prod ] ; simp +decide [ Finset.prod_eq_zero_iff, sub_eq_zero, hb'' ] ;
              exact Or.inr ⟨ ⟨ hb, by simpa using Polynomial.isRoot_of_mem_roots ( Multiset.mem_toFinset.mp hr ) ⟩, Ne.symm hb'' ⟩;
        conv_lhs => rw [ h_eval ];
        simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib ]
      -- By the properties of the derivative and roots, we can express $Q'(x)$ as a sum of its partial fractions at the roots of $Q(x)$.
      have h_deriv : ∀ r ∈ Q.roots.toFinset, Q.derivative.eval r = c * (∏ s ∈ Q.roots.toFinset \ {r}, (r - s)) := by
        intro r hr
        have h_deriv : Q.derivative.eval r = Polynomial.eval r (Polynomial.derivative (Polynomial.C c * Finset.prod Q.roots.toFinset (fun s => Polynomial.X - Polynomial.C s))) := by
          rw [ ← hc ];
        rw [ h_deriv, Finset.prod_eq_prod_diff_singleton_mul hr ] ; norm_num [ Polynomial.derivative_prod ] ; ring;
        norm_num [ Polynomial.eval_prod ];
      -- By the properties of the derivative and roots, we can express $Q(x)$ as a product of its roots.
      have h_prod : Q.eval x = c * (∏ r ∈ Q.roots.toFinset, (x - r)) := by
        simpa [ Polynomial.eval_prod ] using congr_arg ( Polynomial.eval x ) hc;
      rw [ h_eval, h_prod, Finset.sum_div _ _ _ ];
      refine Finset.sum_congr rfl fun r hr => ?_;
      rw [ h_deriv r hr, Finset.prod_eq_prod_diff_singleton_mul hr ] ; ring;
      field_simp;
      convert mul_div_mul_right _ _ ( show ( ∏ s ∈ Q.roots.toFinset \ { r }, ( x - s ) ) ≠ 0 from Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero_of_ne <| by rintro rfl; exact hx <| by simpa using Finset.mem_sdiff.mp hs |>.1 ) using 1 ; ring;
    assumption;
  -- Consider the limit of the partial fraction decomposition as $x$ goes to infinity.
  have h_limit : Filter.Tendsto (fun x : ℝ => (∑ r ∈ Q.roots.toFinset, (P.eval r) / (Q.derivative.eval r) * (1 / (x - r))) * x) Filter.atTop (nhds (∑ r ∈ Q.roots.toFinset, (P.eval r) / (Q.derivative.eval r))) := by
    -- Each term in the sum $\sum_{r \in Q.roots.toFinset} \frac{P(r)}{Q'(r)} \cdot \frac{x}{x - r}$ tends to $\frac{P(r)}{Q'(r)}$ as $x$ goes to infinity.
    have h_term_limit : ∀ r ∈ Q.roots.toFinset, Filter.Tendsto (fun x : ℝ => (P.eval r) / (Q.derivative.eval r) * (x / (x - r))) Filter.atTop (nhds ((P.eval r) / (Q.derivative.eval r))) := by
      intro r hr
      have : Filter.Tendsto (fun x : ℝ => x / (x - r)) Filter.atTop (nhds 1) := by
        erw [ Metric.tendsto_nhds ];
        exact fun ε ε_pos => Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹ * ( |r| + 1 ) ⌉₊ + |r| + 1, fun x hx => abs_lt.mpr ⟨ by cases abs_cases r <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( |r| + 1 ) ), mul_inv_cancel₀ ( ne_of_gt ε_pos ), div_mul_cancel₀ x ( by linarith : ( x - r ) ≠ 0 ) ], by cases abs_cases r <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( |r| + 1 ) ), mul_inv_cancel₀ ( ne_of_gt ε_pos ), div_mul_cancel₀ x ( by linarith : ( x - r ) ≠ 0 ) ] ⟩ ⟩;
      simpa using this.const_mul _;
    simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using tendsto_finset_sum _ h_term_limit |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, hx.ne' ] );
  -- Since $P(x)/Q(x)$ tends to zero as $x$ goes to infinity, the limit of the partial fraction decomposition must also be zero.
  have h_zero_limit : Filter.Tendsto (fun x : ℝ => P.eval x / Q.eval x * x) Filter.atTop (nhds 0) := by
    field_simp;
    have := Polynomial.div_tendsto_zero_of_degree_lt ( P * Polynomial.X ) Q;
    by_cases hP : P = 0 <;> by_cases hQ : Q = 0 <;> simp_all +decide [ Polynomial.degree_eq_natDegree ];
    exact this ( mod_cast by linarith );
  convert tendsto_nhds_unique h_limit ( h_zero_limit.congr' _ ) using 1;
  · rw [ ← Multiset.toFinset_eq ] ; aesop;
  · filter_upwards [ Filter.eventually_gt_atTop ( ∑ r ∈ Q.roots.toFinset, |r| ) ] with x hx;
    rw [ h_partial_fractions x ];
    intro hx';
    exact hx.not_le ( Finset.single_le_sum ( fun r _ => abs_nonneg r ) ( by aesop ) |> le_trans ( le_abs_self _ ) )

/-
If p(a) = 0 and p'(a) = 0, then (x-a)^2 divides p(x).
-/
lemma dvd_pow_two_of_isRoot_of_isRoot_derivative {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (a : R) (h1 : p.IsRoot a) (h2 : p.derivative.IsRoot a) :
    (Polynomial.X - Polynomial.C a)^2 ∣ p := by
  obtain ⟨ q, rfl ⟩ := Polynomial.dvd_iff_isRoot.mpr h1; simp_all +decide [ sq, Polynomial.derivative_mul ] ;
  exact mul_dvd_mul_left _ ( Polynomial.dvd_iff_isRoot.mpr h2 )

/-
If p has distinct roots and p' has distinct roots, then p * p' has distinct roots.
-/
lemma roots_mul_deriv_nodup (p : ℝ[X])
    (h_splits : p.Splits (RingHom.id ℝ))
    (h_nodup : p.roots.Nodup)
    (h_deriv_nodup : p.derivative.roots.Nodup) :
    (p * p.derivative).roots.Nodup := by
      by_cases h : Polynomial.derivative p = 0 <;> simp_all +decide [ Polynomial.splits_iff_card_roots ];
      rw [ Polynomial.roots_mul ];
      · -- Since $p$ and $p'$ have no common roots, their roots are disjoint.
        have h_disjoint : Disjoint (p.roots.toFinset) ((Polynomial.derivative p).roots.toFinset) := by
          rw [ Finset.disjoint_left ] ; intro x hx hx' ; simp_all +decide [ Polynomial.IsRoot ];
          have := Polynomial.dvd_iff_isRoot.mpr hx.2; obtain ⟨ q, rfl ⟩ := this; simp_all +decide [ Polynomial.derivative_mul ] ;
          rw [ Polynomial.roots_mul ] at h_nodup <;> aesop;
        rw [ Multiset.nodup_add ] ; aesop;
      · aesop

/-
The degree of the derivative is deg(p) - 1 for real polynomials with deg(p) > 0.
-/
lemma natDegree_derivative_eq_natDegree_sub_one (p : ℝ[X]) (hp : p.natDegree > 0) :
    p.derivative.natDegree = p.natDegree - 1 := by
      rw [ Polynomial.natDegree_eq_of_degree_eq_some ] ; aesop;

/-
If a real polynomial splits, its derivative also splits.
-/
lemma splits_derivative (p : ℝ[X]) (h_splits : p.Splits (RingHom.id ℝ)) :
    p.derivative.Splits (RingHom.id ℝ) := by
  by_cases h : p.natDegree = 0 <;> simp_all +decide [ Polynomial.splits_iff_card_roots ];
  · rw [ Polynomial.eq_C_of_natDegree_eq_zero h ] ; aesop;
  · -- Since $p$ is a polynomial with real coefficients and $p$ splits into linear factors over the reals, by Rolle's theorem, between any two consecutive roots of $p$, there is at least one root of $p'$.
    have h_rolle : Multiset.card (Polynomial.derivative p).roots ≥ Multiset.card p.roots - 1 := by
      norm_num +zetaDelta at *;
      exact?;
    refine' le_antisymm _ _;
    · exact Polynomial.card_roots' _;
    · refine' le_trans _ ( h_rolle.trans' ( Nat.sub_le_sub_right h_splits.ge _ ) );
      exact Polynomial.natDegree_derivative_le _

/-
Helper lemma for degree inequality.
-/
lemma deg_P_plus_two_le_deg_Q (p : ℝ[X]) (hp : p.natDegree ≥ 2) :
    (p.derivative.derivative ^ 2).natDegree + 2 ≤ (p * p.derivative).natDegree := by
  have h_deg_p_pos : p.natDegree > 0 := by omega
  have h_deg_deriv : p.derivative.natDegree = p.natDegree - 1 :=
    natDegree_derivative_eq_natDegree_sub_one p h_deg_p_pos
  have h_deg_deriv_pos : p.derivative.natDegree > 0 := by
    rw [h_deg_deriv]
    omega
  have h_deg_deriv2 : p.derivative.derivative.natDegree = p.natDegree - 2 := by
    rw [natDegree_derivative_eq_natDegree_sub_one p.derivative h_deg_deriv_pos]
    rw [h_deg_deriv]
    omega
  have h_deg_P : (p.derivative.derivative ^ 2).natDegree = 2 * (p.natDegree - 2) := by
    rw [Polynomial.natDegree_pow, h_deg_deriv2]
  have h_deg_Q : (p * p.derivative).natDegree = 2 * p.natDegree - 1 := by
    rw [Polynomial.natDegree_mul]
    · rw [h_deg_deriv]
      omega
    · exact Polynomial.ne_zero_of_natDegree_gt h_deg_p_pos
    · exact Polynomial.ne_zero_of_natDegree_gt h_deg_deriv_pos
  rw [h_deg_P, h_deg_Q]
  omega

/-
Proof of the alternative formula for Phi using residues.
-/
lemma Phi_eq_sum_roots_deriv (p : ℝ[X])
    (h_splits : p.Splits (RingHom.id ℝ))
    (h_nodup : p.roots.Nodup)
    (h_deg : p.natDegree ≥ 2)
    (h_deriv_nodup : p.derivative.roots.Nodup) :
    Phi p = -1/4 * (p.derivative.roots.map (fun μ => p.derivative.derivative.eval μ / p.eval μ)).sum := by
      have := @Phi_derivative_form p h_splits h_nodup;
      have := @sum_residues_eq_zero_of_deg_le ( Polynomial.derivative ( Polynomial.derivative p ) ^ 2 ) ( p * Polynomial.derivative p ) ?_ ?_ ?_ <;> norm_num at *;
      · rw [ Polynomial.roots_mul ] at this;
        · simp_all +decide [ Finset.sum_add_distrib, Multiset.sum_map_mul_right, div_eq_mul_inv ];
          rw [ show ( Multiset.map ( fun x => Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ^ 2 * ( Polynomial.eval x ( Polynomial.derivative p ) * Polynomial.eval x ( Polynomial.derivative p ) + Polynomial.eval x p * Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ) ⁻¹ ) p.roots ).sum = ( Multiset.map ( fun x => Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ^ 2 * ( Polynomial.eval x ( Polynomial.derivative p ) * Polynomial.eval x ( Polynomial.derivative p ) ) ⁻¹ ) p.roots ).sum from ?_ ] at this;
          · rw [ show ( Multiset.map ( fun x => Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ^ 2 * ( Polynomial.eval x ( Polynomial.derivative p ) * Polynomial.eval x ( Polynomial.derivative p ) ) ⁻¹ ) p.roots ).sum = ( ∑ x ∈ p.roots.toFinset, ( Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ^ 2 * ( Polynomial.eval x ( Polynomial.derivative p ) * Polynomial.eval x ( Polynomial.derivative p ) ) ⁻¹ ) ) from ?_ ] at this;
            · rw [ show ( Multiset.map ( fun x => Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ^ 2 * ( Polynomial.eval x ( Polynomial.derivative p ) * Polynomial.eval x ( Polynomial.derivative p ) + Polynomial.eval x p * Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ) ⁻¹ ) ( Polynomial.derivative p |> Polynomial.roots ) ).sum = ( Multiset.map ( fun x => Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ^ 2 * ( Polynomial.eval x p * Polynomial.eval x ( Polynomial.derivative ( Polynomial.derivative p ) ) ) ⁻¹ ) ( Polynomial.derivative p |> Polynomial.roots ) ).sum from ?_ ] at this;
              · convert congr_arg ( fun x : ℝ => x / 4 ) ( eq_neg_of_add_eq_zero_left this ) using 1 <;> ring;
                · rw [ Finset.sum_mul _ _ _ ];
                · field_simp;
              · refine' congr_arg _ ( Multiset.map_congr rfl fun x hx => _ );
                aesop;
            · rw [ ← Multiset.toFinset_eq ];
              exact?;
              assumption;
          · refine' congr_arg _ ( Multiset.map_congr rfl fun x hx => _ );
            aesop;
        · norm_num +zetaDelta at *;
          exact ⟨ by aesop_cat, by exact fun h => by rw [ Polynomial.eq_C_of_derivative_eq_zero h ] at h_deg h_splits h_nodup; aesop_cat ⟩;
      · have := @deg_P_plus_two_le_deg_Q p h_deg;
        aesop;
      · exact Polynomial.splits_mul _ h_splits ( splits_derivative _ h_splits );
      · convert roots_mul_deriv_nodup p h_splits h_nodup h_deriv_nodup using 1

-- ============================================================================
-- Additional results from AristotleQuery28
-- ============================================================================

/-
The Phi functional for a symmetric quartic polynomial $X^4 + aX^2 + c$ is given by the formula $\frac{-a(12c + a^2)}{2c(a^2 - 4c)}$.
-/
def Phi_symmetric_quartic_formula (a c : ℝ) : ℝ :=
  -a * (12 * c + a^2) / (2 * c * (a^2 - 4 * c))

theorem Phi_eq_Phi_symmetric_quartic_formula (a c : ℝ)
    (h_discr : a^2 - 4 * c > 0) (h_c : c > 0) (h_a : a < 0) :
    let p := X^4 + C a * X^2 + C c
    p.roots.Nodup → p.Splits (RingHom.id ℝ) →
    Phi p = Phi_symmetric_quartic_formula a c := by
      unfold Phi;
      field_simp;
      -- Let $y_1, y_2$ be the roots of $y^2 + ay + c = 0$.
      obtain ⟨y1, y2, hy1, hy2⟩ : ∃ y1 y2 : ℝ, y1 + y2 = -a ∧ y1 * y2 = c ∧ y1 > 0 ∧ y2 > 0 ∧ y1 ≠ y2 := by
        exact ⟨ ( -a + Real.sqrt ( a^2 - 4 * c ) ) / 2, ( -a - Real.sqrt ( a^2 - 4 * c ) ) / 2, by ring, by linarith [ Real.mul_self_sqrt h_discr.le ], by nlinarith [ Real.sqrt_nonneg ( a^2 - 4 * c ), Real.mul_self_sqrt h_discr.le ], by nlinarith [ Real.sqrt_nonneg ( a^2 - 4 * c ), Real.mul_self_sqrt h_discr.le ], by nlinarith [ Real.sqrt_nonneg ( a^2 - 4 * c ), Real.mul_self_sqrt h_discr.le ] ⟩;
      -- The roots of $p$ are $\pm \sqrt{y_1}, \pm \sqrt{y_2}$.
      have h_roots : (Polynomial.X ^ 4 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C c).roots.toFinset = {Real.sqrt y1, -Real.sqrt y1, Real.sqrt y2, -Real.sqrt y2} := by
        ext;
        constructor <;> intro h <;> simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ];
        · -- By definition of $y1$ and $y2$, we know that $x^2 = y1$ or $x^2 = y2$.
          have h_sq : (‹ℝ› ^ 2 = y1) ∨ (‹ℝ› ^ 2 = y2) := by
            grind;
          rcases h_sq with ( h_sq | h_sq ) <;> [ exact Or.imp id ( Or.inl ) ( eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [ h_sq, Real.sq_sqrt <| by linarith ] ) ; exact Or.inr <| Or.inr <| eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [ h_sq, Real.sq_sqrt <| by linarith ] ];
        · rcases h with ( rfl | rfl | rfl | rfl ) <;> exact ⟨ ne_of_apply_ne ( fun p => p.coeff 4 ) <| by norm_num [ Polynomial.coeff_X, Polynomial.coeff_C ], by nlinarith [ Real.mul_self_sqrt hy2.2.1.le, Real.mul_self_sqrt hy2.2.2.1.le ] ⟩;
      rw [ h_roots, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton ] <;> norm_num;
      · rw [ Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton ] <;> norm_num;
        · rw [ Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton ] <;> norm_num;
          · rw [ Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton ] <;> norm_num;
            · rw [ Finset.erase_insert_of_ne, Finset.erase_insert_of_ne ] <;> norm_num;
              · rw [ Finset.sum_insert, Finset.sum_insert ] <;> norm_num;
                · rw [ Finset.erase_eq_of_notMem ] <;> norm_num;
                  · rw [ show a = - ( y1 + y2 ) by linarith, show c = y1 * y2 by linarith ] ; ring;
                    unfold Phi_symmetric_quartic_formula;
                    rw [ show ( -Real.sqrt y1 - Real.sqrt y2 ) = - ( Real.sqrt y1 + Real.sqrt y2 ) by ring, show ( -Real.sqrt y1 + Real.sqrt y2 ) = - ( Real.sqrt y1 - Real.sqrt y2 ) by ring, inv_neg, inv_neg ] ; ring;
                    rw [ show ( Real.sqrt y1 - Real.sqrt y2 ) = ( y1 - y2 ) / ( Real.sqrt y1 + Real.sqrt y2 ) by rw [ eq_div_iff <| by nlinarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ] ] ; linarith [ Real.mul_self_sqrt hy2.2.1.le, Real.mul_self_sqrt hy2.2.2.1.le ] ] ; norm_num ; ring;
                    rw [ show ( Real.sqrt y1 + Real.sqrt y2 ) ⁻¹ = ( Real.sqrt y1 - Real.sqrt y2 ) / ( y1 - y2 ) by rw [ inv_eq_one_div, div_eq_div_iff ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> nlinarith [ Real.mul_self_sqrt hy2.2.1.le, Real.mul_self_sqrt hy2.2.2.1.le, Real.sqrt_nonneg y1, Real.sqrt_nonneg y2 ] ] ; ring;
                    norm_num [ ne_of_gt ( Real.sqrt_pos.mpr hy2.2.1 ), ne_of_gt ( Real.sqrt_pos.mpr hy2.2.2.1 ) ] ; ring;
                    field_simp;
                    rw [ div_add_div, div_add_div, div_add_div, div_eq_div_iff ] <;> try nlinarith [ Real.mul_self_sqrt hy2.2.1.le, Real.mul_self_sqrt hy2.2.2.1.le ];
                    · grind;
                    · simp_all +decide [ ne_of_gt, le_of_lt ];
                      exact ⟨ by cases lt_or_gt_of_ne hy2.2.2.2 <;> nlinarith, by nlinarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ] ⟩;
                    · exact mul_ne_zero ( mul_ne_zero ( by linarith ) ( by linarith ) ) ( by nlinarith [ mul_self_pos.mpr ( sub_ne_zero.mpr hy2.2.2.2 ) ] );
                    · exact mul_ne_zero ( mul_ne_zero ( by cases lt_or_gt_of_ne hy2.2.2.2 <;> nlinarith ) ( pow_ne_zero 2 ( Real.sqrt_ne_zero'.mpr hy2.2.1 ) ) ) ( pow_ne_zero 2 ( Real.sqrt_ne_zero'.mpr hy2.2.2.1 ) );
                    · grind;
                  · linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ];
                · exact fun _ => by linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ] ;
                · exact ⟨ by linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ], fun _ => by rw [ Real.sqrt_inj ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> linarith ⟩;
              · rw [ Real.sqrt_inj ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> linarith;
              · linarith [ Real.sqrt_pos.2 hy2.2.1 ];
            · linarith [ Real.sqrt_pos.2 hy2.2.2.1 ];
            · exact ⟨ by linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ], by rw [ Real.sqrt_inj ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> linarith ⟩;
            · grind;
          · linarith [ Real.sqrt_pos.2 hy2.2.2.1 ];
          · exact ⟨ by linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ], by rw [ Real.sqrt_inj ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> linarith ⟩;
          · grind;
        · linarith [ Real.sqrt_pos.2 hy2.2.2.1 ];
        · exact ⟨ by linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ], by rw [ Real.sqrt_inj ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> linarith ⟩;
        · grind;
      · linarith [ Real.sqrt_pos.2 hy2.2.2.1 ];
      · exact ⟨ by linarith [ Real.sqrt_pos.2 hy2.2.1, Real.sqrt_pos.2 hy2.2.2.1 ], by rw [ Real.sqrt_inj ] <;> cases lt_or_gt_of_ne hy2.2.2.2 <;> linarith ⟩;
      · grind

/-
The inverse Phi functional for a symmetric quartic polynomial matches the explicit formula.
-/
def invPhi_symmetric_quartic_formula (a c : ℝ) : ℝ :=
  if a < 0 ∧ c > 0 ∧ a^2 > 4 * c then
    (2 * c * (a^2 - 4 * c)) / (-a * (12 * c + a^2))
  else 0

theorem invPhi_eq_invPhi_symmetric_quartic_formula (a c : ℝ)
    (h_discr : a^2 - 4 * c > 0) (h_c : c > 0) (h_a : a < 0) :
    let p := X^4 + C a * X^2 + C c
    p.roots.Nodup → p.Splits (RingHom.id ℝ) →
    invPhi p = invPhi_symmetric_quartic_formula a c := by
      intro p hp hp';
      convert congr_arg _ (Phi_eq_Phi_symmetric_quartic_formula a c h_discr h_c h_a hp hp') using 1;
      all_goals norm_num [ invPhi ];
      rotate_right;
      use fun x => if x = 0 then 0 else 1 / x;
      · have h_card : p.natDegree = 4 := by
          rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ];
        rw [ Polynomial.splits_iff_card_roots ] at hp' ; aesop;
      · unfold Phi_symmetric_quartic_formula invPhi_symmetric_quartic_formula; aesop;

/-
Defining the auxiliary function $f(k) = \frac{2k(1-4k)}{12k+1}$.
-/
def f_aux (k : ℝ) : ℝ := (2 * k * (1 - 4 * k)) / (12 * k + 1)

/-
The second derivative of the auxiliary function $f(k)$ is $\frac{-64}{(12k+1)^3}$.
-/
lemma f_aux_second_deriv (k : ℝ) (hk : k > -1/12) :
    deriv (deriv f_aux) k = -64 / (12 * k + 1)^3 := by
      -- First, we need to find the first derivative of $f(k)$.
      have h_deriv : ∀ k > -1 / 12, deriv f_aux k = (deriv (fun k => (2 * k - 8 * k^2) / (12 * k + 1))) k := by
        exact fun k hk => by congr; ext; unfold f_aux; ring;
      -- Now, we need to find the second derivative of $f(k)$.
      have h_second_deriv : deriv (deriv f_aux) k = deriv (fun k => (2 - 16 * k) * (12 * k + 1) / (12 * k + 1)^2 - (2 * k - 8 * k^2) * 12 / (12 * k + 1)^2) k := by
        refine' Filter.EventuallyEq.deriv_eq _;
        filter_upwards [ lt_mem_nhds hk ] with x hx using by rw [ h_deriv x hx ] ; norm_num [ mul_comm, show x * 12 + 1 ≠ 0 from by linarith ] ; ring;
      norm_num [ h_second_deriv, mul_comm ];
      norm_num [ show k * 12 + 1 ≠ 0 by linarith ] ; ring;
      grind

/-
The auxiliary function $f(k)$ is increasing on the interval $(0, 1/12]$.
-/
lemma f_aux_increasing (x y : ℝ) (hx : 0 < x) (hy : y ≤ 1/12) (hxy : x ≤ y) :
    f_aux x ≤ f_aux y := by
      unfold f_aux; rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_self_nonneg ( y - x ), mul_nonneg hx.le ( sub_nonneg_of_le hxy ) ] ;

/-
The auxiliary function $f(k)$ is decreasing on the interval $[1/12, 1/4)$.
-/
lemma f_aux_decreasing (x y : ℝ) (hx : 1/12 ≤ x) (hy : y < 1/4) (hxy : x ≤ y) :
    f_aux y ≤ f_aux x := by
      unfold f_aux; rw [ div_le_div_iff₀ ] <;> try nlinarith;
      nlinarith [ mul_le_mul_of_nonneg_left hxy ( sub_nonneg_of_le hx ) ]

/-
Defining the inverse Phi functional for symmetric quartics in terms of parameters $A$ and $c$.
-/
def invPhi_sym_param (A c : ℝ) : ℝ :=
  (2 * c * (A^2 - 4 * c)) / (A * (12 * c + A^2))

/-
The inverse Phi functional can be expressed as $A \cdot f(c/A^2)$.
-/
lemma invPhi_sym_param_eq (A c : ℝ) (hA : A ≠ 0) :
    invPhi_sym_param A c = A * f_aux (c / A^2) := by
      unfold invPhi_sym_param f_aux; ring_nf; simp +decide [ hA, pow_three, mul_assoc, mul_left_comm, div_eq_mul_inv ] ; ring;
      grind

/-
The difference between the combined argument $K$ and the weighted average $k_{avg}$ is proportional to $1/6 - (k+k')$.
-/
lemma invPhi_sym_param_arg_diff (A A' c c' : ℝ) (hA : A > 0) (hA' : A' > 0) :
    let k := c / A^2
    let k' := c' / A'^2
    let K := (c + c' + A * A' / 6) / (A + A')^2
    let k_avg := (A * k + A' * k') / (A + A')
    K - k_avg = (A * A' / (A + A')^2) * (1/6 - (k + k')) := by
      -- Combine and simplify the fractions in the expression.
      field_simp
      ring

-- ============================================================================
-- Additional results from AristotleQ32 -- Centering infrastructure
-- ============================================================================

/-
Phi is invariant under shifts (alias for Phi_comp_add_C).
-/
lemma Phi_shift_invariance (p : ℝ[X]) (c : ℝ) :
    Phi (p.comp (X + C c)) = Phi p :=
  Phi_comp_add_C p c

/-
invPhi is invariant under shifts (alias for invPhi_comp_add_C).
-/
lemma invPhi_shift_invariance (p : ℝ[X]) (c : ℝ) :
    invPhi (p.comp (X + C c)) = invPhi p :=
  invPhi_comp_add_C p c

/-
Shifting a monic polynomial p by -p_{n-1}/n makes it centered.
-/
def shift_to_center_amount (n : ℕ) (p : ℝ[X]) : ℝ :=
  - p.coeff (n - 1) / n

def shifted_to_center (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p.comp (X + C (shift_to_center_amount n p))

lemma shifted_to_center_is_centered (n : ℕ) (p : ℝ[X])
    (hn : n ≠ 0) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) :
    is_centered n (shifted_to_center n p) := by
      refine' ⟨ _, _, _ ⟩;
      · convert hp_monic.comp_X_add_C _ using 1;
      · unfold shifted_to_center;
        rw [ Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, hp_deg ] ; aesop;
      · -- By definition of shifted_to_center, we have:
        have h_shift : shifted_to_center n p = p.comp (X + C (-p.coeff (n - 1) / n)) := by
          exact?;
        simp_all +decide [ Polynomial.comp, Polynomial.eval₂_eq_sum_range ];
        rcases n <;> simp_all +decide [ Polynomial.coeff_X_add_C_pow, Finset.sum_range_succ ];
        simp_all +decide [ Finset.sum_range, Nat.choose_eq_zero_of_lt ];
        rw [ div_mul_cancel₀ ] <;> first | positivity | rw [ ← hp_deg, hp_monic.coeff_natDegree ] ; ring;

/-
Shifting to center preserves real-rootedness and simple roots.
-/
lemma shifted_to_center_properties (n : ℕ) (p : ℝ[X])
    (hp_splits : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup) :
    (shifted_to_center n p).Splits (RingHom.id ℝ) ∧ (shifted_to_center n p).roots.Nodup := by
      unfold shifted_to_center;
      constructor;
      · exact?;
      · -- The roots of $p(x + c)$ are just the roots of $p$ shifted by $-c$.
        have h_roots_shift : (p.comp (Polynomial.X + Polynomial.C (shift_to_center_amount n p))).roots = Multiset.map (fun r => r - shift_to_center_amount n p) p.roots := by
          ext x;
          rw [ Multiset.count_map, eq_comm ];
          rw [ show ( Multiset.filter ( fun a => x = a - shift_to_center_amount n p ) p.roots ) = Multiset.filter ( fun a => a = x + shift_to_center_amount n p ) p.roots from ?_, Multiset.filter_eq' ] ; norm_num [ eq_comm ];
          · rw [ Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.rootMultiplicity_eq_natTrailingDegree ];
            norm_num [ Polynomial.comp_assoc ];
            rw [ add_assoc ];
          · exact Multiset.filter_congr fun y hy => by constructor <;> intro h <;> linarith;
        exact h_roots_shift.symm ▸ Multiset.Nodup.map ( fun x => by aesop ) hp_nodup

/-
It suffices to prove the Finite Free Stam Inequality for centered polynomials.
-/
lemma finite_free_stam_inequality_centered_sufficient (n : ℕ)
    (hn : n ≥ 2) :
    (∀ (p q : ℝ[X]),
      is_centered n p → is_centered n q →
      p.Splits (RingHom.id ℝ) → p.roots.Nodup →
      q.Splits (RingHom.id ℝ) → q.roots.Nodup →
      (boxplus n p q).Splits (RingHom.id ℝ) → (boxplus n p q).roots.Nodup →
      invPhi (boxplus n p q) ≥ invPhi p + invPhi q) →
    (∀ (p q : ℝ[X]),
      p.Monic → p.natDegree = n → p.Splits (RingHom.id ℝ) → p.roots.Nodup →
      q.Monic → q.natDegree = n → q.Splits (RingHom.id ℝ) → q.roots.Nodup →
      (boxplus n p q).Splits (RingHom.id ℝ) → (boxplus n p q).roots.Nodup →
      invPhi (boxplus n p q) ≥ invPhi p + invPhi q) := by
        intro h p q hp hp' hp'' hp''' hq hq' hq'' hq''' hq'''' hq''''';
        -- Let p_cent(x) = p(x + c_p) and q_cent(x) = q(x + c_q).
        set p_cent := shifted_to_center n p
        set q_cent := shifted_to_center n q;
        -- By the properties of the shifted polynomials, we have:
        have hp_cent : invPhi p_cent = invPhi p := by
          convert invPhi_shift_invariance p ( shift_to_center_amount n p ) using 1
        have hq_cent : invPhi q_cent = invPhi q := by
          apply invPhi_shift_invariance
        have hpq_cent : invPhi (boxplus n p_cent q_cent) = invPhi (boxplus n p q) := by
          have hpq_cent : boxplus n p_cent q_cent = (boxplus n p q).comp (X + C (shift_to_center_amount n p + shift_to_center_amount n q)) := by
            convert boxplus_comp_add_C n p q ( shift_to_center_amount n p ) ( shift_to_center_amount n q ) hp' hq' using 1;
          rw [ hpq_cent, invPhi_shift_invariance ];
        have hp_cent_centered : is_centered n p_cent := by
          apply shifted_to_center_is_centered n p (by linarith) hp hp'
        have hq_cent_centered : is_centered n q_cent := by
          apply shifted_to_center_is_centered n q (by linarith) hq hq'
        have hp_cent_splits : (p_cent).Splits (RingHom.id ℝ) := by
          have := shifted_to_center_properties n p hp'' hp''';
          exact this.1
        have hp_cent_nodup : (p_cent).roots.Nodup := by
          have := shifted_to_center_properties n p hp'' hp''' ; aesop;
        have hq_cent_splits : (q_cent).Splits (RingHom.id ℝ) := by
          exact shifted_to_center_properties n q hq'' hq''' |>.1
        have hq_cent_nodup : (q_cent).roots.Nodup := by
          convert shifted_to_center_properties n q hq'' hq''' |>.2 using 1
        have hpq_cent_splits : (boxplus n p_cent q_cent).Splits (RingHom.id ℝ) := by
          rw [ show boxplus n p_cent q_cent = ( boxplus n p q |> Polynomial.comp <| X + C ( shift_to_center_amount n p + shift_to_center_amount n q ) ) from ?_ ];
          · exact?;
          · convert boxplus_comp_add_C n p q ( shift_to_center_amount n p ) ( shift_to_center_amount n q ) hp' hq' using 1
        have hpq_cent_nodup : (boxplus n p_cent q_cent).roots.Nodup := by
          contrapose! hq''''';
          -- By the properties of the boxplus operation, we have:
          have hpq_cent_eq : boxplus n p_cent q_cent = (boxplus n p q).comp (X + C (shift_to_center_amount n p + shift_to_center_amount n q)) := by
            convert boxplus_comp_add_C n p q ( shift_to_center_amount n p ) ( shift_to_center_amount n q ) hp' hq' using 1;
          rw [ Multiset.nodup_iff_count_le_one ] at *;
          simp_all +decide [ Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C ];
          obtain ⟨ x, hx ⟩ := hq''''';
          use x + (shift_to_center_amount n p + shift_to_center_amount n q);
          rw [ Polynomial.rootMultiplicity_eq_natTrailingDegree ] at *;
          convert hx using 2 ; norm_num [ Polynomial.comp_assoc ] ; ring;
        linarith [ h p_cent q_cent hp_cent_centered hq_cent_centered hp_cent_splits hp_cent_nodup hq_cent_splits hq_cent_nodup hpq_cent_splits hpq_cent_nodup ]

-- ============================================================================
-- Additional results from AristotleQ32 -- Centered coefficient computations
-- ============================================================================

/-
For centered polynomials, (p ⊞ q)_{n-2} = p_{n-2} + q_{n-2}.
-/
lemma boxplus_centered_coeff_n_sub_2 (n : ℕ) (p q : ℝ[X])
    (hp : is_centered n p) (hq : is_centered n q) (hn : n ≥ 2) :
    (boxplus n p q).coeff (n - 2) = p.coeff (n - 2) + q.coeff (n - 2) := by
      rcases n with _ | _ | n <;> simp_all +decide [ Nat.succ_eq_add_one ];
      unfold is_centered at *;
      unfold boxplus; simp +decide [ Finset.sum_range_succ', hp.2.2, hq.2.2 ] ;
      rw [ Finset.sum_eq_zero ] <;> norm_num [ boxplus_coeff ] at *;
      · simp +arith +decide [ Finset.sum_range_succ', hp.2.1, hq.2.1 ];
        simp_all +decide [ Nat.factorial_ne_zero, mul_comm, mul_assoc, mul_left_comm ];
        have := hp.1.coeff_natDegree; have := hq.1.coeff_natDegree; aesop;
      · intros; omega;

/-
Phi(X^2 + c) = -1/(2c) for c < 0.
-/
lemma Phi_quadratic_centered (c : ℝ) (hc : c < 0) :
    let p := X^2 + C c
    Phi p = -1 / (2 * c) := by
      field_simp;
      rw [ show ( Polynomial.X ^ 2 + Polynomial.C c : Polynomial ℝ ) = ( Polynomial.X - Polynomial.C ( -Real.sqrt ( -c ) ) ) * ( Polynomial.X - Polynomial.C ( Real.sqrt ( -c ) ) ) by exact Polynomial.funext fun x => by norm_num; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ -c by linarith ) ] ];
      unfold Phi;
      erw [ Polynomial.roots_mul <| mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; norm_num;
      rw [ Finset.sum_pair ] <;> norm_num [ hc.ne ];
      · rw [ Finset.sum_eq_single ( Real.sqrt ( -c ) ), Finset.sum_pair ] <;> norm_num;
        · ring_nf; norm_num [ hc.le ];
        · linarith [ Real.sqrt_pos.2 ( neg_pos.2 hc ) ];
        · aesop;
        · exact fun h => by linarith [ Real.sqrt_pos.2 ( neg_pos.2 hc ) ] ;
      · linarith [ Real.sqrt_pos.2 ( neg_pos.2 hc ) ]

-- ============================================================================
-- Additional results from AristotleQ32 -- Centered cubic infrastructure
-- ============================================================================

/-
Phi(x^3 + ax + b) = -18a^2 / (27b^2 + 4a^3).
-/
def Phi_cubic_centered_formula (a b : ℝ) : ℝ :=
  -18 * a^2 / (27 * b^2 + 4 * a^3)

/-
For centered cubic polynomials, the constant term of p ⊞ q is the sum of the constant terms of p and q.
-/
lemma boxplus_centered_cubic_coeff_0 (p q : ℝ[X])
    (hp : is_centered 3 p) (hq : is_centered 3 q) :
    (boxplus 3 p q).coeff 0 = p.coeff 0 + q.coeff 0 := by
      unfold is_centered at *;
      unfold boxplus; norm_num [ Finset.sum_range_succ', hp, hq, Polynomial.coeff_zero_eq_eval_zero ] ; ring; (
      unfold boxplus_coeff; norm_num [ Polynomial.eval_eq_sum_range, Finset.sum_range_succ', hp, hq ] ; ring;
      have := hp.1.coeff_natDegree; have := hq.1.coeff_natDegree; aesop;)

/-
invPhi(x^3 + ax + b) = -3/2 (b/a)^2 - 2/9 a.
-/
def invPhi_cubic_centered_formula (a b : ℝ) : ℝ :=
  -3/2 * (b/a)^2 - 2/9 * a

lemma invPhi_eq_invPhi_cubic_centered_formula (a b : ℝ)
    (h_discr : 4 * a^3 + 27 * b^2 < 0) :
    let p := X^3 + C a * X + C b
    p.roots.Nodup → p.Splits (RingHom.id ℝ) →
    invPhi p = invPhi_cubic_centered_formula a b := by
      intro p h_nodup_splits h_roots_splits
      have h_phi : Phi p = -18 * a ^ 2 / (27 * b ^ 2 + 4 * a ^ 3) := by
        convert Phi_eq_sum_roots_deriv p h_roots_splits h_nodup_splits _ _ using 1;
        · -- The roots of $p'(x) = 3x^2 + a$ are $\mu = \pm \sqrt{-a/3}$.
          have h_roots_deriv : Polynomial.roots (Polynomial.derivative p) = {Real.sqrt (-a / 3), -Real.sqrt (-a / 3)} := by
            norm_num +zetaDelta at *;
            rw [ show ( Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C a : Polynomial ℝ ) = ( Polynomial.C 3 ) * ( Polynomial.X ^ 2 - Polynomial.C ( -a / 3 ) ) by exact Polynomial.funext fun x => by norm_num; ring, Polynomial.roots_C_mul ] <;> norm_num;
            rw [ show ( Polynomial.X ^ 2 - Polynomial.C ( -a / 3 ) : Polynomial ℝ ) = ( Polynomial.X - Polynomial.C ( Real.sqrt ( -a ) / Real.sqrt 3 ) ) * ( Polynomial.X - Polynomial.C ( - ( Real.sqrt ( -a ) / Real.sqrt 3 ) ) ) by exact Polynomial.funext fun x => by norm_num; ring_nf; norm_num ; rw [ Real.sq_sqrt <| by nlinarith [ sq_nonneg a ] ] ; ring, Polynomial.roots_mul <| by exact mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; norm_num;
          rw [ h_roots_deriv ] ; norm_num ; ring;
          norm_num [ p ] ; ring;
          field_simp;
          rw [ show ( Real.sqrt ( -a ) ) ^ 3 = Real.sqrt ( -a ) * Real.sqrt ( -a ) ^ 2 by ring, Real.sq_sqrt <| neg_nonneg.mpr <| by nlinarith [ sq_nonneg a ] ] ; norm_num [ pow_three ] ; ring;
          rw [ show ( a ^ 3 * 4 + b ^ 2 * 27 ) = ( a * Real.sqrt ( -a ) * 2 + b * Real.sqrt 3 * 3 ) * ( - ( a * Real.sqrt ( -a ) * 2 ) + b * Real.sqrt 3 * 3 ) by ring_nf; norm_num [ Real.sq_sqrt ( show 0 ≤ -a by nlinarith [ sq_nonneg a ] ) ] ; ring ] ; norm_num ; ring;
          field_simp;
          rw [ div_sub_div ] <;> ring <;> norm_num;
          · rw [ Real.sq_sqrt ] <;> nlinarith [ sq_nonneg a ];
          · by_contra h_contra;
            have h_eq : b = (a * Real.sqrt (-a) * 2) / (Real.sqrt 3 * 3) := by
              exact eq_div_of_mul_eq ( by positivity ) ( by linarith );
            subst h_eq; ring_nf at *; norm_num at *;
            rw [ Real.sq_sqrt ] at h_discr <;> nlinarith [ sq_nonneg a ];
          · by_contra h_contra;
            have h_eq : b = - (a * Real.sqrt (-a) * 2) / (3 * Real.sqrt 3) := by
              exact eq_div_of_mul_eq ( by positivity ) ( by linarith );
            subst h_eq; ring_nf at *; norm_num at *;
            rw [ Real.sq_sqrt ] at h_discr <;> nlinarith [ sq_nonneg a ];
        · rw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ];
        · convert Polynomial.nodup_roots _ using 1;
          refine' IsCoprime.symm _;
          norm_num [ p ];
          refine' IsCoprime.mul_left _ _;
          · exact ⟨ Polynomial.C ( 1 / 3 ), 0, Polynomial.funext fun x => by norm_num ⟩;
          · refine' IsCoprime.mul_left _ _;
            · exact ⟨ Polynomial.C ( 1 / 2 ), 0, Polynomial.funext fun x => by norm_num ⟩;
            · refine' IsCoprime.symm _;
              refine' IsCoprime.symm ( Polynomial.irreducible_X.coprime_iff_not_dvd.mpr _ );
              rw [ Polynomial.X_dvd_iff ] ; norm_num;
              rintro rfl; nlinarith;
      unfold invPhi invPhi_cubic_centered_formula;
      by_cases ha : a = 0 <;> simp_all +decide [ Polynomial.splits_iff_card_roots ];
      rw [ if_pos ];
      · grind;
      · erw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> aesop

/-
Algebraic inequality for n=3 Stam.
-/
lemma algebraic_stam_inequality_n3 (A C B D : ℝ) (hA : A < 0) (hC : C < 0) :
    -3/2 * ((B + D) / (A + C))^2 - 2/9 * (A + C) ≥ (-3/2 * (B / A)^2 - 2/9 * A) + (-3/2 * (D / C)^2 - 2/9 * C) := by
      -- Let t = C/(A+C). Then (1-t) = A/(A+C).
      set t : ℝ := C / (A + C)
      have ht : 0 < t ∧ t < 1 := by
        exact ⟨ div_pos_of_neg_of_neg hC ( by linarith ), by rw [ div_lt_iff_of_neg ] <;> linarith ⟩;
      -- Then $(B + D) / (A + C) = (1 - t) * (B / A) + t * (D / C)$.
      have h_rewrite : (B + D) / (A + C) = (1 - t) * (B / A) + t * (D / C) := by
        grind;
      rw [ h_rewrite ] ; nlinarith [ mul_le_mul_of_nonneg_left ht.2.le ( sub_nonneg_of_le ht.1.le ), sq_nonneg ( B / A - D / C ) ] ;

/-
If X^3 + aX + b has distinct real roots, then 4a^3 + 27b^2 < 0.
-/
lemma cubic_discriminant_neg_of_nodup_splits (a b : ℝ)
    (h_nodup : (X^3 + C a * X + C b).roots.Nodup)
    (h_splits : (X^3 + C a * X + C b).Splits (RingHom.id ℝ)) :
    4 * a^3 + 27 * b^2 < 0 := by
      obtain ⟨x₁, x₂, x₃, hx⟩ : ∃ x₁ x₂ x₃ : ℝ, x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧ x₁^3 + a * x₁ + b = 0 ∧ x₂^3 + a * x₂ + b = 0 ∧ x₃^3 + a * x₃ + b = 0 := by
        -- Since the polynomial has distinct roots, we can extract three distinct elements from its roots.
        obtain ⟨x₁, x₂, x₃, hx⟩ : ∃ x₁ x₂ x₃ : ℝ, x₁ ∈ Polynomial.roots (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ∧ x₂ ∈ Polynomial.roots (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ∧ x₃ ∈ Polynomial.roots (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
          have h_card : Multiset.card (Polynomial.roots (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b)) = 3 := by
            rw [ Polynomial.splits_iff_card_roots ] at h_splits;
            rw [ h_splits, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ];
          rcases Multiset.card_eq_three.mp h_card with ⟨ x₁, x₂, x₃, h ⟩ ; use x₁, x₂, x₃ ; aesop;
        exact ⟨ x₁, x₂, x₃, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2, by aesop ⟩;
      -- By Vieta's formulas, we know that $x_1 + x_2 + x_3 = 0$ and $x_1 x_2 + x_2 x_3 + x_3 x_1 = a$.
      have h_vieta_sum : x₁ + x₂ + x₃ = 0 := by
        exact mul_left_cancel₀ ( sub_ne_zero_of_ne hx.1 ) <| mul_left_cancel₀ ( sub_ne_zero_of_ne hx.2.1 ) <| mul_left_cancel₀ ( sub_ne_zero_of_ne hx.2.2.1 ) <| by linear_combination hx.2.2.2.1 * ( x₂ - x₃ ) - hx.2.2.2.2.1 * ( x₁ - x₃ ) + hx.2.2.2.2.2 * ( x₁ - x₂ ) ;
      have h_vieta_prod_sum : x₁ * x₂ + x₂ * x₃ + x₃ * x₁ = a := by
        exact mul_left_cancel₀ ( sub_ne_zero_of_ne hx.1 ) ( by ring_nf; nlinarith );
      -- By Vieta's formulas, we know that $x_1 x_2 x_3 = -b$.
      have h_vieta_prod : x₁ * x₂ * x₃ = -b := by
        grind +ring;
      -- Substitute $a = x₁ * x₂ + x₂ * x₃ + x₃ * x₁$ and $b = -x₁ * x₂ * x₃$ into the inequality.
      have h_sub : 4 * (x₁ * x₂ + x₂ * x₃ + x₃ * x₁) ^ 3 + 27 * (-x₁ * x₂ * x₃) ^ 2 < 0 := by
        have h_sub : (x₁ - x₂)^2 * (x₁ - x₃)^2 * (x₂ - x₃)^2 > 0 := by
          exact mul_pos ( mul_pos ( sq_pos_of_ne_zero ( sub_ne_zero.mpr hx.1 ) ) ( sq_pos_of_ne_zero ( sub_ne_zero.mpr hx.2.1 ) ) ) ( sq_pos_of_ne_zero ( sub_ne_zero.mpr hx.2.2.1 ) );
        rw [ ← eq_sub_iff_add_eq' ] at h_vieta_sum ; subst_vars ; nlinarith;
      aesop

/-
Finite Free Stam Inequality for n=3 centered polynomials.
-/
theorem finite_free_stam_inequality_centered_n3 (p q : ℝ[X])
    (hp : is_centered 3 p) (hq : is_centered 3 q)
    (hp_real : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hq_real : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hpq_real : (boxplus 3 p q).Splits (RingHom.id ℝ)) (hpq_nodup : (boxplus 3 p q).roots.Nodup) :
    invPhi (boxplus 3 p q) ≥ invPhi p + invPhi q := by
      obtain ⟨a, b, hp_eq⟩ : ∃ a b : ℝ, p = Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b := by
        rcases hp with ⟨ hp₁, hp₂, hp₃ ⟩;
        rw [ p.as_sum_range_C_mul_X_pow ] ; use p.coeff 1, p.coeff 0; norm_num [ Finset.sum_range_succ', hp₂, hp₃ ] ;
        rw [ ← hp₂, hp₁.coeff_natDegree, Polynomial.C_1 ]
      obtain ⟨c, d, hq_eq⟩ : ∃ c d : ℝ, q = Polynomial.X^3 + Polynomial.C c * Polynomial.X + Polynomial.C d := by
        rcases hq with ⟨ hq₁, hq₂, hq₃ ⟩;
        rw [ Polynomial.as_sum_range_C_mul_X_pow q ] ; use q.coeff 1, q.coeff 0; norm_num [ Finset.sum_range_succ', hq₂, hq₃ ] ; ring;
        rw [ ← hq₂, hq₁.coeff_natDegree ] ; norm_num
      obtain ⟨e, f, hpq_eq⟩ : ∃ e f : ℝ, boxplus 3 p q = Polynomial.X^3 + Polynomial.C e * Polynomial.X + Polynomial.C f := by
        -- Since $p$ and $q$ are centered, their boxplus convolution is also centered, hence has the form $X^3 + eX + f$.
        have h_centered : is_centered 3 (boxplus 3 p q) := by
          exact?;
        rcases h_centered with ⟨ hp₁, hp₂, hp₃ ⟩ ; rw [ Polynomial.as_sum_range_C_mul_X_pow ( boxplus 3 p q ) ] ; norm_num [ Finset.sum_range_succ', Polynomial.natDegree_eq_of_degree_eq_some, hp₁, hp₂, hp₃ ] ;
        rw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ( Polynomial.degree_eq_natDegree <| by aesop_cat ) ] at hp₁ ; aesop;
      -- By definition of $invPhi$, we know that
      have h_invPhi_p : invPhi p = -3 / 2 * (b / a) ^ 2 - 2 / 9 * a := by
        convert invPhi_eq_invPhi_cubic_centered_formula a b _ _ using 1;
        · aesop;
        · convert cubic_discriminant_neg_of_nodup_splits a b _ _ using 1 <;> aesop;
        · aesop
      have h_invPhi_q : invPhi q = -3 / 2 * (d / c) ^ 2 - 2 / 9 * c := by
        convert invPhi_eq_invPhi_cubic_centered_formula c d _ _ using 1;
        · aesop;
        · convert cubic_discriminant_neg_of_nodup_splits c d _ _ using 1 <;> aesop;
        · aesop
      have h_invPhi_pq : invPhi (boxplus 3 p q) = -3 / 2 * (f / e) ^ 2 - 2 / 9 * e := by
        convert invPhi_eq_invPhi_cubic_centered_formula e f _ using 1;
        · aesop;
        · convert cubic_discriminant_neg_of_nodup_splits e f _ _ using 1 <;> aesop;
      -- By definition of $boxplus$, we know that $e = a + c$ and $f = b + d$.
      have h_e : e = a + c := by
        have h_e : (boxplus 3 p q).coeff 1 = a + c := by
          convert boxplus_centered_coeff_n_sub_2 3 p q hp hq ( by norm_num ) using 1 ; norm_num [ hp_eq, hq_eq ];
        aesop
      have h_f : f = b + d := by
        have := boxplus_centered_cubic_coeff_0 p q hp hq; aesop;
      -- By definition of $a$, $b$, $c$, and $d$, we know that $4a^3 + 27b^2 < 0$ and $4c^3 + 27d^2 < 0$.
      have h_discr_p : 4 * a^3 + 27 * b^2 < 0 := by
        apply cubic_discriminant_neg_of_nodup_splits a b; aesop;
        aesop
      have h_discr_q : 4 * c^3 + 27 * d^2 < 0 := by
        convert cubic_discriminant_neg_of_nodup_splits c d _ _ using 1 <;> aesop;
      -- By definition of $a$, $b$, $c$, and $d$, we know that $a < 0$ and $c < 0$.
      have h_a_neg : a < 0 := by
        nlinarith [ sq_nonneg a ]
      have h_c_neg : c < 0 := by
        nlinarith [ sq_nonneg c ];
      have := algebraic_stam_inequality_n3 a c b d h_a_neg h_c_neg; aesop;

-- ============================================================================
-- Additional results from AristotleQ32 -- Centered n=2 infrastructure
-- ============================================================================

/-
If X^2 + c has distinct real roots, then c < 0.
-/
lemma quadratic_centered_coeff_neg (c : ℝ)
    (h_nodup : (X^2 + C c).roots.Nodup)
    (h_splits : (X^2 + C c).Splits (RingHom.id ℝ)) :
    c < 0 := by
      rw [ Polynomial.splits_iff_card_roots ] at h_splits;
      by_contra h_nonneg;
      rcases lt_or_eq_of_le ( le_of_not_gt h_nonneg ) with h | rfl <;> norm_num at *;
      · obtain ⟨ x, hx ⟩ := Multiset.card_pos_iff_exists_mem.mp ( by linarith ) ; norm_num at hx ; nlinarith;
      · norm_num [ two_smul ] at h_nodup

/-
Finite Free Stam Inequality for n=2 centered polynomials.
-/
theorem finite_free_stam_inequality_centered_n2 (p q : ℝ[X])
    (hp : is_centered 2 p) (hq : is_centered 2 q)
    (hp_real : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hq_real : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hpq_real : (boxplus 2 p q).Splits (RingHom.id ℝ)) (hpq_nodup : (boxplus 2 p q).roots.Nodup) :
    invPhi (boxplus 2 p q) ≥ invPhi p + invPhi q := by
      -- By definition of $p$ and $q$, we know that $p = X^2 + c_p$ and $q = X^2 + c_q$ for some $c_p, c_q \in ℝ$.
      obtain ⟨cp, hp_eq⟩ : ∃ cp : ℝ, p = Polynomial.X ^ 2 + Polynomial.C cp := by
        rcases hp with ⟨ hp_monic, hp_deg, hp_coeff ⟩ ; rw [ Polynomial.as_sum_range_C_mul_X_pow p ] ; use p.coeff 0 ; norm_num [ Finset.sum_range_succ', hp_monic, hp_deg, hp_coeff ] ;
        rw [ ← hp_deg, hp_monic.coeff_natDegree, Polynomial.C_1 ]
      obtain ⟨cq, hq_eq⟩ : ∃ cq : ℝ, q = Polynomial.X ^ 2 + Polynomial.C cq := by
        rcases hq with ⟨ hq₁, hq₂, hq₃ ⟩;
        rw [ Polynomial.as_sum_range_C_mul_X_pow q ] ; norm_num [ Finset.sum_range_succ', hq₂, hq₃ ];
        have := hq₁.coeff_natDegree; aesop;
      -- By definition of $p$ and $q$, we know that $p ⊞ q = X^2 + (c_p + c_q)$.
      have h_boxplus_eq : boxplus 2 p q = Polynomial.X ^ 2 + Polynomial.C (cp + cq) := by
        unfold boxplus;
        unfold boxplus_coeff; norm_num [ Finset.sum_range_succ', hp_eq, hq_eq ] ; ring;
      have h_invPhis : ∀ c : ℝ, (Polynomial.X ^ 2 + Polynomial.C c).roots.Nodup → (Polynomial.X ^ 2 + Polynomial.C c).Splits (RingHom.id ℝ) → invPhi (Polynomial.X ^ 2 + Polynomial.C c) = -2 * c := by
        intros c hc_nodup hc_splits
        have h_discriminant : c < 0 := by
          exact?;
        -- By definition of $invPhi$, we know that $invPhi(X^2 + c) = -2c$.
        have h_invPhi_def : invPhi (Polynomial.X ^ 2 + Polynomial.C c) = 1 / (Phi (Polynomial.X ^ 2 + Polynomial.C c)) := by
          unfold invPhi;
          rw [ Polynomial.splits_iff_card_roots ] at hc_splits ; aesop;
        rw [ h_invPhi_def, Phi_quadratic_centered c h_discriminant ] ; ring;
        norm_num;
      grind

-- ============================================================================
-- Additional results from AristotleQ32 -- Quartic infrastructure
-- ============================================================================

/-
Coefficients of boxplus for symmetric quartics.
-/
lemma boxplus_symmetric_quartic_coeffs (p q : ℝ[X])
    (hp : is_centered 4 p) (hq : is_centered 4 q)
    (hp_sym : p.coeff 1 = 0) (hq_sym : q.coeff 1 = 0) :
    (boxplus 4 p q).coeff 2 = p.coeff 2 + q.coeff 2 ∧
    (boxplus 4 p q).coeff 0 = p.coeff 0 + q.coeff 0 + p.coeff 2 * q.coeff 2 / 6 := by
      constructor;
      · convert boxplus_centered_coeff_n_sub_2 4 p q hp hq _ using 1 ; norm_num;
      · unfold boxplus; norm_num [ Finset.sum_range_succ' ] ; ring;
        unfold boxplus_coeff; norm_num [ Finset.sum_range_succ' ] ; ring;
        have := hp.1; have := hq.1; ( have := hp.2.1; have := hq.2.1; ( erw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ( Polynomial.degree_eq_natDegree <| by aesop ) ] at *; aesop; ) )

/-
Boxplus of symmetric centered quartics is symmetric.
-/
lemma boxplus_symmetric_quartic_is_symmetric (p q : ℝ[X])
    (hp : is_centered 4 p) (hq : is_centered 4 q)
    (hp_sym : p.coeff 1 = 0) (hq_sym : q.coeff 1 = 0) :
    (boxplus 4 p q).coeff 1 = 0 := by
      rw [ show ( boxplus 4 p q : Polynomial ℝ ) = ∑ i ∈ Finset.range ( 4 + 1 ), Polynomial.C ( ( boxplus_coeff 4 p q i ) ) * Polynomial.X ^ ( 4 - i ) by rfl ] ; simp_all +decide [ Finset.sum ] ;
      unfold boxplus_coeff; norm_num [ Finset.sum_range_succ, hp_sym, hq_sym ] ;
      cases hp ; cases hq ; aesop

-- ============================================================================
-- Additional results from AristotleQ32 -- Convexity infrastructure
-- ============================================================================

/-
g(u) = (8u^2 - 2u) / (12u + 1) is convex on [0, infinity).
-/
def g_aux (u : ℝ) : ℝ := (8 * u^2 - 2 * u) / (12 * u + 1)

lemma g_aux_second_deriv (u : ℝ) (hu : u > -1/12) :
    deriv^[2] g_aux u = 64 / (12 * u + 1)^3 := by
      -- Let's simplify the expression for the second derivative.
      have h_simplify : deriv^[2] (fun u : ℝ => (8 * u^2 - 2 * u) / (12 * u + 1)) u = deriv (fun u : ℝ => (16 * u - 2) * (12 * u + 1) / (12 * u + 1)^2 - (8 * u^2 - 2 * u) * 12 / (12 * u + 1)^2) u := by
        refine' Filter.EventuallyEq.deriv_eq _;
        filter_upwards [ lt_mem_nhds hu ] with u hu using by norm_num [ mul_comm, show u * 12 + 1 ≠ 0 from by linarith ] ; ring;
      convert h_simplify using 1 ; norm_num [ mul_comm ] ; ring;
      norm_num [ show 1 + u * 24 + u ^ 2 * 144 ≠ 0 by nlinarith ] ; ring;
      grind

lemma g_aux_convex_on : ConvexOn ℝ (Set.Ici 0) g_aux := by
  refine' ⟨ convex_Ici _, _ ⟩;
  unfold g_aux;
  norm_num +zetaDelta at *;
  intro x hx y hy a b ha hb hab; rw [ mul_div, mul_div, div_add_div, div_le_div_iff₀ ] <;> try positivity;
  obtain rfl := eq_sub_of_add_eq hab;
  nlinarith [ mul_nonneg hb ( sq_nonneg ( x - y ) ), mul_nonneg hb ( mul_nonneg hx hy ), mul_nonneg hb ( mul_nonneg hx ha ), mul_nonneg hb ( mul_nonneg hy ha ), mul_nonneg hx hy, mul_nonneg hx ha, mul_nonneg hy ha ]

/-
F_aux(a, c) = -2c(a^2 - 4c) / (a(12c + a^2)).
-/
def F_aux (a c : ℝ) : ℝ :=
  -2 * c * (a^2 - 4 * c) / (a * (12 * c + a^2))

lemma F_aux_eq_a_mul_g_aux (a c : ℝ) (ha : a ≠ 0) :
    F_aux a c = a * g_aux (c / a^2) := by
  unfold F_aux g_aux
  field_simp
  ring

/-
h_aux(k) = k(1-k) / (2(3k+1)).
-/
def h_aux (k : ℝ) : ℝ := k * (1 - k) / (2 * (3 * k + 1))

lemma F_aux_eq_neg_a_mul_h_aux (a c : ℝ) (ha : a ≠ 0) (h_denom : 12 * c + a^2 ≠ 0) :
    F_aux a c = -a * h_aux (4 * c / a^2) := by
  unfold F_aux h_aux
  field_simp
  ring

-- ============================================================================
-- Additional results from AristotleQ33 -- Concavity and Jensen gap results
-- ============================================================================

/-
The auxiliary function f_aux is concave on the interval (0, \infty).
-/
lemma f_aux_concave : ConcaveOn ℝ (Set.Ioi 0) f_aux := by
  fapply concaveOn_of_deriv2_nonpos <;> norm_num [ f_aux ];
  · exact convex_Ioi 0;
  · exact ContinuousOn.div ( Continuous.continuousOn ( by continuity ) ) ( Continuous.continuousOn ( by continuity ) ) fun x hx => by linarith [ hx.out ] ;
  · exact DifferentiableOn.div ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id ) |> DifferentiableOn.mul <| differentiableOn_const _ |> DifferentiableOn.sub <| differentiableOn_id.const_mul _ ) ( differentiableOn_const _ |> DifferentiableOn.add <| differentiableOn_id.const_mul _ ) fun x hx => by linarith [ hx.out ] ;
  · -- Let's calculate the first derivative of $f_{\text{aux}}$.
    have h_deriv : ∀ t > 0, deriv f_aux t = (2 * (1 - 8 * t - 48 * t^2)) / (1 + 12 * t)^2 := by
      intros t ht; rw [ show f_aux = fun t => 2 * t * ( 1 - 4 * t ) / ( 1 + 12 * t ) by funext; rfl ] ; norm_num [ mul_comm, mul_assoc, mul_left_comm, ne_of_gt ( by positivity : 0 < 1 + t * 12 ) ] ; ring;
    exact DifferentiableOn.congr ( by exact DifferentiableOn.div ( DifferentiableOn.mul ( differentiableOn_const _ ) ( by exact DifferentiableOn.sub ( DifferentiableOn.sub ( differentiableOn_const _ ) ( differentiableOn_id.const_mul _ ) ) ( differentiableOn_id.pow 2 |> DifferentiableOn.const_mul <| _ ) ) ) ( by exact DifferentiableOn.pow ( by exact DifferentiableOn.add ( differentiableOn_const _ ) ( differentiableOn_id.const_mul _ ) ) _ ) <| by intros t ht; exact ne_of_gt <| sq_pos_of_pos <| by linarith [ ht.out ] ) h_deriv;
  · -- Let's calculate the first derivative of $f_aux$.
    have h_deriv : ∀ x > 0, deriv f_aux x = 2 * (1 - 8 * x - 48 * x^2) / (1 + 12 * x)^2 := by
      unfold f_aux; intro x hx; norm_num [ mul_comm, ( show 1 + x * 12 ≠ 0 by linarith ) ] ; ring;
    intro x hx; rw [ Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioi_mem_nhds hx ) fun y hy => h_deriv y hy ) ] ; norm_num [ mul_comm, hx.ne' ] ;
    norm_num [ show 1 + x * 12 ≠ 0 by positivity ] ; ring_nf ; norm_num;
    nlinarith [ inv_pos.2 ( by positivity : 0 < 1 + x * 48 + x ^ 2 * 864 + x ^ 3 * 6912 + x ^ 4 * 20736 ) ]

/-
The inequality holds when the shifted argument is small and the sum of arguments is small.
-/
lemma f_aux_ineq_easy_case (t x y : ℝ)
    (ht : 0 < t) (ht1 : t < 1)
    (hx : 0 < x) (hx1 : x < 1/4)
    (hy : 0 < y) (hy1 : y < 1/4)
    (hsum : x + y ≤ 1/6)
    (hZ : t^2 * x + (1 - t)^2 * y + t * (1 - t) / 6 ≤ 1/12) :
    f_aux (t^2 * x + (1 - t)^2 * y + t * (1 - t) / 6) ≥ t * f_aux x + (1 - t) * f_aux y := by
  refine' le_trans _ ( f_aux_increasing _ _ _ _ _ );
  convert ( f_aux_concave.2 _ _ _ _ _ ) using 1;
  all_goals norm_num <;> try nlinarith;
  nlinarith only [ mul_nonneg ht.le ( sub_nonneg.2 ht1.le ), hsum ]

/-
The inequality holds when the sum of arguments is large and the shifted argument is not too small.
-/
lemma f_aux_ineq_case2_easy (t x y : ℝ)
    (ht : 0 < t) (ht1 : t < 1)
    (hx : 0 < x) (hx1 : x < 1/4)
    (hy : 0 < y) (hy1 : y < 1/4)
    (hsum : x + y > 1/6)
    (hZ : t^2 * x + (1 - t)^2 * y + t * (1 - t) / 6 ≥ 1/12) :
    f_aux (t^2 * x + (1 - t)^2 * y + t * (1 - t) / 6) ≥ t * f_aux x + (1 - t) * f_aux y := by
  -- By the lemma f_aux_decreasing, $f_aux(Z) \geq f_aux(W)$.
  have h_f_aux_decreasing : f_aux (t ^ 2 * x + (1 - t) ^ 2 * y + t * (1 - t) / 6) ≥ f_aux (t * x + (1 - t) * y) := by
    apply_rules [ f_aux_decreasing ] ; nlinarith [ mul_pos ht ( sub_pos.2 ht1 ) ] ;
    nlinarith [ mul_pos ht ( sub_pos.2 ht1 ) ];
  refine le_trans ?_ h_f_aux_decreasing;
  have h_f_aux_concave : ConcaveOn ℝ (Set.Ioi 0) f_aux := by
    exact?;
  exact h_f_aux_concave.2 hx hy ( by linarith ) ( by linarith ) ( by linarith )

/-
Definition of the polynomial difference representing the numerator of the Jensen gap inequality.
-/
def poly_diff (t x y : ℝ) : ℝ :=
  let Z := t^2 * x + (1 - t)^2 * y + t * (1 - t) / 6
  (2 * Z * (1 - 4 * Z)) * (1 + 12 * x) * (1 + 12 * y) -
  (t * (2 * x * (1 - 4 * x)) * (1 + 12 * Z) * (1 + 12 * y) +
   (1 - t) * (2 * y * (1 - 4 * y)) * (1 + 12 * Z) * (1 + 12 * x))

/-
Symmetry of the polynomial difference under parameter swap.
-/
lemma poly_diff_symmetry (t x y : ℝ) :
    poly_diff t x y = poly_diff (1 - t) y x := by
  unfold poly_diff; ring;

/-
Definition of the polynomial difference under the substitution t = 1/2 - s.
-/
def poly_diff_subst (s x y : ℝ) : ℝ :=
  let t := 1/2 - s
  poly_diff t x y

/- Aristotle failed to find a proof. -/
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