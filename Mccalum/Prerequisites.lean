import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mccalum.Delineability
import Mccalum.Invariance
import Mccalum.Submanifold

/-!
# Prerequisites for Theorem 3.2.3

The axioms representing results from McCallum's thesis that we use as black boxes
(Theorem 3.2.1 "Lifting", Theorem 2.3.3 + Lemma 3.2.2, etc.), together with the
helper lemmas that are proved in Lean.

We state the product-based axioms using `Finset` products `∏ f ∈ A, f` directly
(rather than indexed families `∏ i : Fin m, F i`) to avoid conversion overhead.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

variable {n : ℕ}

/-- **Theorem 3.2.1** (Lifting theorem, §3.3). -/
axiom lifting_theorem
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hpos : 0 < f.natDegree)
    (hsf : Squarefree f)
    (hdisc_ne : Polynomial.discr f ≠ 0)
    (hnonzero : NotIdenticallyZeroOn f S)
    (hdeg : DegreeInvariant f S)
    (hdisc : OrderInvariantMv (Polynomial.discr f) S) :
    AnalyticDelineable f S ∧
    (∀ (θ : (Fin n → ℝ) → ℝ), ContinuousOn θ S → IsRootFunction f θ S →
      OrderInvariantFull f (SectionGraph θ S))

/-- **Theorem 2.3.3** + **Lemma 3.2.2**: discriminant of product is order-invariant. -/
axiom discr_prod_order_invariant
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hS : IsConnected S)
    (hsf : ∀ f ∈ A, Squarefree f)
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g)
    (hdisc : ∀ f ∈ A, OrderInvariantMv (Polynomial.discr f) S)
    (hres : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      OrderInvariantMv (Polynomial.resultant f g) S) :
    OrderInvariantMv (Polynomial.discr (∏ f ∈ A, f)) S

/-- **Lemma 3.2.2** backward: order-invariance of product implies each factor. -/
axiom order_invariant_full_factor_of_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (T : Set ((Fin n → ℝ) × ℝ))
    (hprod : OrderInvariantFull (∏ f ∈ A, f) T) :
    ∀ f ∈ A, OrderInvariantFull f T

/-- Degree-invariance from coefficient order-invariance. -/
axiom degree_invariant_of_coeff_order_invariant
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hS : IsConnected S) (hS_ne : S.Nonempty)
    (hcoeff : ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S)
    (hnonzero : NotIdenticallyZeroOn f S) :
    DegreeInvariant f S

/-- Product of squarefree pairwise coprime polynomials is squarefree. -/
theorem prod_squarefree_of_coprime
    (A : Finset (PolyR n))
    (hsf : ∀ f ∈ A, Squarefree f)
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g) :
    Squarefree (∏ f ∈ A, f) := by
  induction A using Finset.induction with
  | empty => simp
  | @insert p A hpA ih =>
    rw [Finset.prod_insert hpA, squarefree_mul_iff]
    refine ⟨?_, hsf p (Finset.mem_insert_self p A), ?_⟩
    · apply IsCoprime.isRelPrime
      apply IsCoprime.prod_right
      intro g hg
      refine hcop p (Finset.mem_insert_self p A) g (Finset.mem_insert_of_mem hg) ?_
      intro heq; rw [heq] at hpA; exact hpA hg
    · exact ih (fun f hf => hsf f (Finset.mem_insert_of_mem hf))
        (fun f hf g hg hne =>
          hcop f (Finset.mem_insert_of_mem hf) g (Finset.mem_insert_of_mem hg) hne)

/-- Discriminant of a degree-1 polynomial is order-invariant. In fact the
discriminant equals `1`, so this is trivially invariant. -/
theorem discr_degree_one_order_invariant
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hdeg : f.natDegree = 1) :
    OrderInvariantMv (Polynomial.discr f) S := by
  have hf_ne : f ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  have hf_deg : f.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hf_ne, hdeg]; rfl
  have hdiscr : Polynomial.discr f = 1 :=
    Polynomial.discr_of_degree_eq_one hf_deg
  rw [hdiscr]
  intro a _ b _
  have h1 : polyOrder n (1 : MvPolyR n) a = 0 :=
    (polyOrder_zero_iff n 1 a).mpr (by simp)
  have h2 : polyOrder n (1 : MvPolyR n) b = 0 :=
    (polyOrder_zero_iff n 1 b).mpr (by simp)
  rw [h1, h2]

/-- Nonzero discriminant of squarefree polynomial. -/
axiom discr_ne_zero_of_squarefree
    (f : PolyR n)
    (hsf : Squarefree f) (hpos : 0 < f.natDegree) :
    Polynomial.discr f ≠ 0

/-- Delineability of product implies delineability of each factor (coprime case). -/
axiom delineable_factor_of_delineable_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g)
    (hprod : AnalyticDelineable (∏ f ∈ A, f) S) :
    ∀ f ∈ A, AnalyticDelineable f S

/-- Root function of a factor is a root function of the product. -/
theorem root_function_factor_of_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n)) (G : PolyR n) (hG : G ∈ A)
    (θ : (Fin n → ℝ) → ℝ)
    (hθ : IsRootFunction G θ S) :
    IsRootFunction (∏ f ∈ A, f) θ S := by
  intro a ha
  have hprod : specialize (∏ f ∈ A, f) a = ∏ f ∈ A, specialize f a := by
    simp [specialize, Polynomial.map_prod]
  rw [Polynomial.IsRoot, hprod, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hG (hθ a ha)

/-- Degree-invariance of product from degree-invariance of factors.

**Note:** The original statement used `NotIdenticallyZeroOn` (existential) for `hne`,
but that is too weak — a factor can be degree-invariant with constant degree 0, not
identically zero, yet have its specialization vanish at some points, breaking
degree-invariance of the product. The corrected hypothesis requires each specialization
to be nonzero everywhere on `S`, which is what is available at the call site via
`specialize_nonzero_everywhere`. -/
theorem degree_invariant_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hdeg : ∀ f ∈ A, DegreeInvariant f S)
    (hne : ∀ f ∈ A, ∀ a ∈ S, specialize f a ≠ 0) :
    DegreeInvariant (∏ f ∈ A, f) S := by
  intro a ha b hb
  have ha' : ∀ f ∈ A, Polynomial.map (evalBase a) f ≠ 0 := fun f hf => hne f hf a ha
  have hb' : ∀ f ∈ A, Polynomial.map (evalBase b) f ≠ 0 := fun f hf => hne f hf b hb
  simp only [specialize, Polynomial.map_prod]
  rw [Polynomial.natDegree_prod _ _ ha', Polynomial.natDegree_prod _ _ hb']
  exact Finset.sum_congr rfl (fun f hf => hdeg f hf a ha b hb)

/-- If a nonzero coefficient of `f` is order-invariant on `S` and `f` is not identically
    zero on `S`, then at every point of `S` the specialization of `f` is nonzero. -/
theorem specialize_nonzero_everywhere
    (f : PolyR n)
    (S : Set (Fin n → ℝ))
    (hne : NotIdenticallyZeroOn f S)
    (hcoeff : ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S) :
    ∀ a ∈ S, specialize f a ≠ 0 := by
  obtain ⟨a₀, ha₀, hfa₀⟩ := hne
  rw [Ne, Polynomial.ext_iff, not_forall] at hfa₀
  push Not at hfa₀
  obtain ⟨k, hk⟩ := hfa₀
  simp only [specialize, Polynomial.coeff_map, Polynomial.coeff_zero] at hk
  have hc_ne : f.coeff k ≠ 0 := by
    intro heq; apply hk; simp [heq]
  have hc_oi := hcoeff k hc_ne
  have hord₀ : polyOrder n (f.coeff k) a₀ = 0 := by
    rw [polyOrder_zero_iff]; exact hk
  intro a ha
  have hord : polyOrder n (f.coeff k) a = 0 := by
    rw [hc_oi a ha a₀ ha₀, hord₀]
  rw [polyOrder_zero_iff] at hord
  intro hfa
  apply hord
  have : (specialize f a).coeff k = 0 := by rw [hfa]; simp
  simp [specialize, Polynomial.coeff_map] at this
  exact this

/-- Product of not-identically-zero polynomials is not identically zero on `S`,
    when all nonzero coefficients of each factor are order-invariant on `S`. -/
theorem not_identically_zero_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hne : ∀ f ∈ A, NotIdenticallyZeroOn f S)
    (hcoeff : ∀ f ∈ A, ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S)
    (hS_ne : S.Nonempty) :
    NotIdenticallyZeroOn (∏ f ∈ A, f) S := by
  have hall : ∀ f ∈ A, ∀ a ∈ S, specialize f a ≠ 0 :=
    fun f hf => specialize_nonzero_everywhere f S (hne f hf) (hcoeff f hf)
  obtain ⟨a, ha⟩ := hS_ne
  refine ⟨a, ha, ?_⟩
  rw [show specialize (∏ f ∈ A, f) a = ∏ f ∈ A, specialize f a from by
    simp [specialize, Polynomial.map_prod]]
  exact Finset.prod_ne_zero_iff.mpr (fun f hf => hall f hf a ha)

lemma natDegree_mul {n : Nat} (p q : PolyR n) (hp : 0 < p.natDegree) (hq : 0 < q.natDegree) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  refine Polynomial.natDegree_mul (p := p) (q := q) ?_ ?_
  · exact ne_zero_of_natDegree_gt hp
  · exact ne_zero_of_natDegree_gt hq

lemma prod_insert (A : Finset (PolyR n)) (x : (PolyR n)) (hx : x ∉ A) :
    ∏ i ∈ insert x A, i = x *  ∏ i ∈ A, i := by
  rw [Finset.prod_eq_prod_diff_singleton_mul (i := x)]
  · have : insert x A \ {x} = A := by grind
    rw [this]
    exact CommMonoid.mul_comm (∏ x ∈ A, x) x
  · exact Finset.mem_insert_self x A

theorem prod_pos_degree'
    (A : Finset (PolyR n)) (hA : A.Nonempty)
    (hpos : ∀ f ∈ A, 0 < f.natDegree) :
    (∏ f ∈ A, f).natDegree = ∑ f ∈ A, f.natDegree := by
  induction A using Finset.induction
  next => simp at hA
  next p A p_not_mem IH =>
    if hA: A.Nonempty then
      have deg_pos : ∀ f ∈ A, 0 < natDegree f := by simp_all only [Finset.mem_insert, or_true,
        implies_true, forall_const, Finset.insert_nonempty, forall_eq_or_imp]
      have := IH hA deg_pos
      rw [prod_insert A p _, natDegree_mul, IH]
      · exact Eq.symm (Finset.sum_insert p_not_mem)
      · exact hA
      · assumption
      · exact hpos p (Finset.mem_insert_self p A)
      · rw [this]
        exact Finset.sum_pos deg_pos hA
      · exact p_not_mem
    else
      have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      rw [this]
      simp

/-- Product of positive-degree polynomials has positive degree
    (when the set is nonempty). -/
theorem prod_pos_degree
    (A : Finset (PolyR n)) (hA : A.Nonempty)
    (hpos : ∀ f ∈ A, 0 < f.natDegree) :
    0 < (∏ f ∈ A, f).natDegree := by
  rw [prod_pos_degree' _ hA hpos]
  exact Finset.sum_pos hpos hA

end
