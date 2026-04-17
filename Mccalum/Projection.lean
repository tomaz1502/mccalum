import Mathlib
import CAD.Order

/-!
# McCallum's Reduced Projection Theorem (Theorem 3.2.3)

This file contains the statement and proof of Theorem 3.2.3 from McCallum's PhD thesis
"An Improved Projection Operation for Cylindrical Algebraic Decomposition" (1984).

## Main result

**Theorem 3.2.3**: Let `A` be a finite squarefree basis of `r`-variate integral polynomials
(`r ≥ 2`), `S` a connected submanifold of `ℝ^{r-1}`. Suppose each element of `A` is not
identically zero on `S`, and each element of the reduced projection `P(A)` is
order-invariant in `S`. Then:
1. Each element of `A` is degree-invariant on `S`
2. Each element of `A` is analytically delineable on `S`
3. The sections of `A` over `S` are pairwise disjoint
4. Each element of `A` is order-invariant in every section of `A` over `S`

## Strategy

The proof uses three sorry'd ingredients:
- **Theorem 2.3.3** (discriminant factorization)
- **Lemma 3.2.2** (order-invariance of products)
- **Theorem 3.2.1** (Lifting theorem) — proved via Zariski's 1975 theorem (Ch. 4)
-/

noncomputable section

open Polynomial MvPolynomial Set Classical

/-! ## Type abbreviations -/

/-- r-variate polynomials viewed as univariate in `xᵣ` over `ℝ[x₁,…,xₙ]`. -/
abbrev PolyR (n : ℕ) := Polynomial (MvPolynomial (Fin n) ℝ)

/-- (r-1)-variate polynomials over `ℝ`. -/
abbrev MvPolyR (n : ℕ) := MvPolynomial (Fin n) ℝ

variable {n : ℕ}

/-! ## Evaluation -/

/-- Evaluate base variables of an MvPolynomial at a point `a ∈ ℝⁿ`. -/
abbrev evalBase (a : Fin n → ℝ) : MvPolyR n →+* ℝ :=
  MvPolynomial.eval a

/-- Specialize `f(x, xᵣ)` at `x = a` to get `f(a, xᵣ) ∈ ℝ[xᵣ]`. -/
def specialize (f : PolyR n) (a : Fin n → ℝ) : Polynomial ℝ :=
  f.map (evalBase a)

/-- Convert `PolyR n` to `MvPolynomial (Fin (n+1)) ℝ` via `finSuccEquiv`. -/
def toMvPoly (f : PolyR n) : MvPolynomial (Fin (n + 1)) ℝ :=
  (MvPolynomial.finSuccEquiv ℝ n).symm f

/-! ## Order

We use the Frechet derivative-based `order` from `CAD.Order` as the primary
definition. The equivalence with iterated partial derivatives (`order'`) is
established in `CAD.Order.order_order'`.
-/

/-- The analytic order of `g ∈ ℝ[x₁,…,xₘ]` at `a`, defined via Frechet derivatives.
    This is a wrapper around `order` from `CAD.Order`, specializing to polynomial
    evaluation functions which are always analytic. -/
def polyOrder (m : Nat) (g : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) : ℕ∞ :=
  order ℝ (fun x => MvPolynomial.eval x g) a
    (AnalyticOnNhd.eval_mvPolynomial g a (Set.mem_univ a))

/-- `polyOrder` agrees with the iterated-partial-derivative definition `order'`
    from `CAD.Order`. -/
theorem polyOrder_eq_order' (m : Nat) (g : MvPolynomial (Fin m) ℝ) (a : Fin m → ℝ) :
    polyOrder m g a = order' m g a := by
  unfold polyOrder
  rw [← order_order']

/-! ## Analytic submanifold -/

/-- `S` is an analytic submanifold of `ℝⁿ` (McCallum, Definition p.20). -/
def IsAnalyticSubmanifold (S : Set (Fin n → ℝ)) : Prop :=
  S.Nonempty ∧
  ∃ s : ℕ, s ≤ n ∧
    ∀ p ∈ S, ∃ (U : Set (Fin n → ℝ)) (_ : IsOpen U) (_ : p ∈ U),
      ∃ Φ : (Fin n → ℝ) → (Fin n → ℝ),
        (∀ x ∈ U, x ∈ S ↔ ∀ i : Fin n, s ≤ i.val → Φ x i = 0)

/-! ## Key Definitions -/

/-- `f` is **degree-invariant** on `S`. -/
def DegreeInvariant (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, (specialize f a).natDegree = (specialize f b).natDegree

/-- A base polynomial `g` is **order-invariant** on `S`. -/
def OrderInvariantMv (g : MvPolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, polyOrder n g a = polyOrder n g b

/-- Order of `f ∈ ℝ[x₁,…,xₙ][xᵣ]` at `(a, y) ∈ ℝⁿ × ℝ`. -/
def orderFull (f : PolyR n) (a : Fin n → ℝ) (y : ℝ) : ℕ∞ :=
  polyOrder (n + 1) (toMvPoly f) (Fin.cons y a)

/-- A full polynomial `f` is **order-invariant** in `T ⊆ ℝⁿ × ℝ`. -/
def OrderInvariantFull (f : PolyR n) (T : Set ((Fin n → ℝ) × ℝ)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, orderFull f p.1 p.2 = orderFull f q.1 q.2

/-- `f` is **not identically zero** on `S`. -/
def NotIdenticallyZeroOn (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ a ∈ S, specialize f a ≠ 0

/-- The graph of `θ` over `S`, i.e., a **section**. -/
def SectionGraph (θ : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | p.1 ∈ S ∧ p.2 = θ p.1}

/-- `θ` is a **root function** of `G` on `S`. -/
def IsRootFunction (G : PolyR n) (θ : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) :
    Prop :=
  ∀ a ∈ S, (specialize G a).IsRoot (θ a)

/-! ## Analytic delineability -/

def AnalyticDelineable (f : PolyR n) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (k : ℕ) (θ : Fin k → ((Fin n → ℝ) → ℝ)) (m : Fin k → ℕ),
    (∀ i, ContinuousOn (θ i) S) ∧
    (∀ a ∈ S, ∀ i j : Fin k, i < j → θ i a < θ j a) ∧
    (∀ a ∈ S, ∀ y : ℝ,
      (specialize f a).IsRoot y ↔ ∃ i : Fin k, y = θ i a) ∧
    (∀ i, 0 < m i) ∧
    (∀ a ∈ S, ∀ i, (specialize f a).rootMultiplicity (θ i a) = m i)

/-! ## Squarefree basis -/

structure IsSquarefreeBasis (A : Finset (PolyR n)) : Prop where
  pos_degree : ∀ f ∈ A, 0 < f.natDegree
  sq_free : ∀ f ∈ A, Squarefree f
  pairwise_coprime : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g

/-! ## Reduced projection P(A) -/

def coeffSet (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  {c | ∃ f ∈ A, ∃ k : ℕ, f.coeff k = c ∧ c ≠ 0}

def discrSet (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  {d | ∃ f ∈ A, 2 ≤ f.natDegree ∧ d = Polynomial.discr f}

def resSet (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  {r | ∃ f ∈ A, ∃ g ∈ A, f ≠ g ∧ 1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧
    r = Polynomial.resultant f g}

def reducedProjection (A : Finset (PolyR n)) : Set (MvPolyR n) :=
  coeffSet A ∪ discrSet A ∪ resSet A

/-! ## Sections of A -/

def SectionsDisjoint (A : Finset (PolyR n)) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ F ∈ A, ∀ G ∈ A, F ≠ G → ∀ a ∈ S,
    Disjoint {y | (specialize F a).IsRoot y} {y | (specialize G a).IsRoot y}

def OrderInvariantInAllSections (A : Finset (PolyR n)) (S : Set (Fin n → ℝ)) :
    Prop :=
  ∀ F ∈ A, ∀ G ∈ A, ∀ θ : (Fin n → ℝ) → ℝ,
    ContinuousOn θ S → IsRootFunction G θ S →
    OrderInvariantFull F (SectionGraph θ S)

/-! ## Sorry'd prerequisites

We state the prerequisites using `Finset` products `∏ f ∈ A, f` directly
(rather than indexed families `∏ i : Fin m, F i`) to avoid conversion overhead. -/

section Prerequisites

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
axiom prod_squarefree_of_coprime
    (A : Finset (PolyR n))
    (hsf : ∀ f ∈ A, Squarefree f)
    (hcop : ∀ f ∈ A, ∀ g ∈ A, f ≠ g → IsCoprime f g) :
    Squarefree (∏ f ∈ A, f)

/-- Discriminant of a degree-1 polynomial is order-invariant whenever
    its coefficients are (it equals the leading coefficient up to sign). -/
axiom discr_degree_one_order_invariant
    (S : Set (Fin n → ℝ))
    (f : PolyR n)
    (hdeg : f.natDegree = 1)
    (hcoeff : ∀ k : ℕ, f.coeff k ≠ 0 → OrderInvariantMv (f.coeff k) S) :
    OrderInvariantMv (Polynomial.discr f) S

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
axiom root_function_factor_of_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n)) (G : PolyR n) (hG : G ∈ A)
    (θ : (Fin n → ℝ) → ℝ)
    (hθ : IsRootFunction G θ S) :
    IsRootFunction (∏ f ∈ A, f) θ S

/-- Degree-invariance of product from degree-invariance of factors. -/
axiom degree_invariant_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hdeg : ∀ f ∈ A, DegreeInvariant f S)
    (hne : ∀ f ∈ A, NotIdenticallyZeroOn f S) :
    DegreeInvariant (∏ f ∈ A, f) S

/-- Product of not-identically-zero polynomials is not identically zero. -/
axiom not_identically_zero_prod
    (S : Set (Fin n → ℝ))
    (A : Finset (PolyR n))
    (hne : ∀ f ∈ A, NotIdenticallyZeroOn f S) :
    NotIdenticallyZeroOn (∏ f ∈ A, f) S

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

end Prerequisites

/-! ## Main theorem -/

/-- Coprime polynomials have no common root after specialization. -/
theorem no_common_root_of_coprime (F G : PolyR n) (hcop : IsCoprime F G)
    (a : Fin n → ℝ) (y : ℝ) :
    ¬ ((specialize F a).IsRoot y ∧ (specialize G a).IsRoot y) := by
  intro ⟨hF, hG⟩
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : specialize (u * F + v * G) a = 1 := by
    rw [huv]; simp [specialize, Polynomial.map_one]
  have h2 : (specialize (u * F + v * G) a).eval y = 1 := by
    rw [h1]; simp
  simp only [specialize, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.eval_add, Polynomial.eval_mul] at h2
  rw [Polynomial.IsRoot] at hF hG
  simp only [specialize] at hF hG
  rw [hF, hG] at h2
  linarith

/-- **Theorem 3.2.3** (McCallum PhD, p.47). -/
theorem mccallum_3_2_3
    (A : Finset (PolyR n))
    (S : Set (Fin n → ℝ))
    (hA : IsSquarefreeBasis A)
    (hA_ne : A.Nonempty)
    (hS_submfld : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (hnonzero : ∀ f ∈ A, NotIdenticallyZeroOn f S)
    (hP : ∀ g ∈ reducedProjection A, OrderInvariantMv g S) :
    (∀ f ∈ A, DegreeInvariant f S) ∧
    (∀ f ∈ A, AnalyticDelineable f S) ∧
    SectionsDisjoint A S ∧
    OrderInvariantInAllSections A S := by
  have hS_ne : S.Nonempty := hS_conn.1
  -- Helper: nonzero coefficients of A-elements are order-invariant
  have hcoeff_oi : ∀ f ∈ A, ∀ k : ℕ, f.coeff k ≠ 0 →
      OrderInvariantMv (f.coeff k) S := by
    intro f hf k hk
    apply hP; left; left
    exact ⟨f, hf, k, rfl, hk⟩
  -- (1) Degree-invariance
  have h_deg : ∀ f ∈ A, DegreeInvariant f S := by
    intro f hf
    exact degree_invariant_of_coeff_order_invariant S f hS_conn hS_ne
      (hcoeff_oi f hf) (hnonzero f hf)
  -- (3) Section disjointness from pairwise coprimality
  have h_disjoint : SectionsDisjoint A S := by
    intro F hF G hG hne a _
    rw [Set.disjoint_left]
    intro y hyF hyG
    exact no_common_root_of_coprime F G
      (hA.pairwise_coprime F hF G hG hne) a y ⟨hyF, hyG⟩
  -- Discriminants of A-elements are order-invariant in S
  have hdisc_oi : ∀ f ∈ A, OrderInvariantMv (Polynomial.discr f) S := by
    intro f hf
    by_cases hdeg : 2 ≤ f.natDegree
    · apply hP; left; right; exact ⟨f, hf, hdeg, rfl⟩
    · -- deg(f) = 1: use discr_degree_one_order_invariant
      have hpos := hA.pos_degree f hf
      have h1 : f.natDegree = 1 := by omega
      exact discr_degree_one_order_invariant S f h1 (hcoeff_oi f hf)
  -- Resultants of distinct pairs are order-invariant in S
  have hres_oi : ∀ f ∈ A, ∀ g ∈ A, f ≠ g →
      OrderInvariantMv (Polynomial.resultant f g) S := by
    intro f hf g hg hne
    apply hP; right
    exact ⟨f, hf, g, hg, hne, hA.pos_degree f hf, hA.pos_degree g hg, rfl⟩
  -- Properties of the product f = ∏ F∈A
  set f := ∏ g ∈ A, g with hf_def
  have hf_sf : Squarefree f :=
    prod_squarefree_of_coprime A hA.sq_free hA.pairwise_coprime
  have hf_pos : 0 < f.natDegree :=
    prod_pos_degree A hA_ne hA.pos_degree
  have hf_discr_ne : Polynomial.discr f ≠ 0 :=
    discr_ne_zero_of_squarefree f hf_sf hf_pos
  have hf_nz : NotIdenticallyZeroOn f S :=
    not_identically_zero_prod S A hnonzero
  have hf_deg : DegreeInvariant f S :=
    degree_invariant_prod S A h_deg hnonzero
  have hf_discr_oi : OrderInvariantMv (Polynomial.discr f) S :=
    discr_prod_order_invariant S A hS_conn hA.sq_free hA.pairwise_coprime
      hdisc_oi hres_oi
  -- Apply the Lifting theorem to f
  have hf_lift := lifting_theorem S f hS_submfld hS_conn hf_pos hf_sf
    hf_discr_ne hf_nz hf_deg hf_discr_oi
  obtain ⟨hf_delin, hf_oi_sections⟩ := hf_lift
  refine ⟨h_deg, ?_, h_disjoint, ?_⟩
  -- (2) Delineability: each F∈A is delineable since ∏A is and factors are coprime
  · exact delineable_factor_of_delineable_prod S A hA.pairwise_coprime hf_delin
  -- (4) Order-invariance in all sections
  · intro F hF G hG θ hθ_cont hθ_root
    -- θ is a root function of G, hence of ∏A
    have hθ_prod : IsRootFunction (∏ g ∈ A, g) θ S :=
      root_function_factor_of_prod S A G hG θ hθ_root
    -- ∏A is order-invariant in graph(θ) by the Lifting theorem
    have hprod_oi : OrderInvariantFull (∏ g ∈ A, g) (SectionGraph θ S) :=
      hf_oi_sections θ hθ_cont hθ_prod
    -- Each factor F is order-invariant in graph(θ) by Lemma 3.2.2
    exact order_invariant_full_factor_of_prod S A (SectionGraph θ S) hprod_oi F hF

#print axioms mccallum_3_2_3
