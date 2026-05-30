import Mccalum.Invariance
import Mccalum.PolyOrderMul
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Data.ENat.BigOperators
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Order-invariance of product implies order-invariance of each factor

**Lemma 3.2.2** (backward direction): if the product `∏ f ∈ A, f` has order-invariant
full on a preconnected set `T`, then each factor does.
-/

noncomputable section

open Polynomial MvPolynomial Set Classical Topology

variable {n : ℕ}

/-! ### Additivity of orderFull -/

private lemma specialize_mul (f g : PolyR n) (a : Fin n → ℝ) :
    specialize (f * g) a = specialize f a * specialize g a :=
  Polynomial.map_mul (MvPolynomial.eval a)

private lemma specialize_one (a : Fin n → ℝ) :
    specialize (1 : PolyR n) a = 1 :=
  Polynomial.map_one (MvPolynomial.eval a)

theorem orderFull_add (f g : PolyR n) (a : Fin n → ℝ) (y : ℝ) :
    orderFull (f * g) a y = orderFull f a y + orderFull g a y := by
  simp only [orderFull, specialize_mul]
  by_cases hf : specialize f a = 0
  · simp [hf]
  by_cases hg : specialize g a = 0
  · simp [hg]
  · simp [hf, hg, mul_ne_zero hf hg,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hf hg), Nat.cast_add]

private lemma orderFull_one (a : Fin n → ℝ) (y : ℝ) :
    orderFull (1 : PolyR n) a y = 0 := by
  simp only [orderFull, specialize_one, if_neg one_ne_zero]
  have : (1 : Polynomial ℝ).rootMultiplicity y = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])
  simp [this]

theorem orderFull_prod_sum (A : Finset (PolyR n)) (a : Fin n → ℝ) (y : ℝ) :
    orderFull (∏ f ∈ A, f) a y = ∑ f ∈ A, orderFull f a y := by
  induction A using Finset.induction with
  | empty => simp [Finset.prod_empty, Finset.sum_empty, orderFull_one]
  | @insert g S hgS ih =>
    rw [Finset.prod_insert hgS, Finset.sum_insert hgS, orderFull_add, ih]

/-! ### Finiteness of order -/

theorem orderFull_lt_top_of_spec_ne {f : PolyR n} {a : Fin n → ℝ}
    (hne : specialize f a ≠ 0) (y : ℝ) : orderFull f a y < ⊤ := by
  simp only [orderFull, if_neg hne]; exact ENat.coe_lt_top _

/-! ### Superlevel sets of orderFull are closed -/

private lemma toMvPoly_iterate_derivative (f : PolyR n) (j : ℕ) :
    toMvPoly (Polynomial.derivative^[j] f) =
      (MvPolynomial.finSuccEquiv ℝ n).symm (Polynomial.derivative^[j] f) := rfl

private lemma iterate_derivative_specialize (f : PolyR n) (a : Fin n → ℝ) (j : ℕ) :
    Polynomial.derivative^[j] (specialize f a) =
      specialize (Polynomial.derivative^[j] f) a := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [Function.iterate_succ', Function.comp_def]
    rw [ih, specialize, specialize, Polynomial.derivative_map]

private lemma eval_specialize_eq_eval_toMvPoly (g : PolyR n) (a : Fin n → ℝ) (y : ℝ) :
    (specialize g a).eval y = MvPolynomial.eval (Fin.cons y a) (toMvPoly g) := by
  simp only [specialize, toMvPoly]
  rw [MvPolynomial.eval_eq_eval_mv_eval',
    (MvPolynomial.finSuccEquiv ℝ n).apply_symm_apply g]

private lemma contDiff_mvPoly_eval (m : ℕ) (g : MvPolynomial (Fin m) ℝ) :
    ContDiff ℝ ⊤ (fun x => MvPolynomial.eval x g) :=
  (show AnalyticOnNhd ℝ (fun x => MvPolynomial.eval x g) univ from
    fun x hx => AnalyticOnNhd.eval_mvPolynomial g x hx).contDiff

private lemma continuous_finCons :
    Continuous (fun p : (Fin n → ℝ) × ℝ => (Fin.cons p.2 p.1 : Fin (n + 1) → ℝ)) := by
  apply continuous_pi; intro i
  refine Fin.cases ?_ ?_ i
  · exact continuous_snd
  · intro j; exact (continuous_apply j).comp continuous_fst

theorem isClosed_orderFull_ge (f : PolyR n) (k : ℕ) :
    IsClosed {p : (Fin n → ℝ) × ℝ | ↑k ≤ orderFull f p.1 p.2} := by
  have heq : {p : (Fin n → ℝ) × ℝ | ↑k ≤ orderFull f p.1 p.2} =
      ⋂ (j : ℕ) (_ : j < k),
        {p : (Fin n → ℝ) × ℝ |
          MvPolynomial.eval (Fin.cons p.2 p.1) (toMvPoly (Polynomial.derivative^[j] f)) = 0} := by
    ext p; simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro h j hj
      rw [← eval_specialize_eq_eval_toMvPoly, ← iterate_derivative_specialize]
      simp only [orderFull] at h
      split_ifs at h with hspec
      · rw [hspec, Polynomial.iterate_derivative_zero, Polynomial.eval_zero]
      · have hk : k ≤ (specialize f p.1).rootMultiplicity p.2 := by exact_mod_cast h
        exact (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
          (Nat.lt_of_lt_of_le hj hk))
    · intro h
      simp only [orderFull]
      split_ifs with hspec
      · exact le_top
      · rcases k.eq_zero_or_pos with rfl | hk
        · exact zero_le _
        · have hroot : ∀ m ≤ k - 1,
              (Polynomial.derivative^[m] (specialize f p.1)).IsRoot p.2 := by
            intro m hm
            show (Polynomial.derivative^[m] (specialize f p.1)).eval p.2 = 0
            rw [iterate_derivative_specialize, eval_specialize_eq_eval_toMvPoly]
            exact h m (by omega)
          have := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hspec hroot
          exact_mod_cast (show k ≤ (specialize f p.1).rootMultiplicity p.2 by omega)
  rw [heq]
  apply isClosed_iInter; intro j; apply isClosed_iInter; intro _
  exact isClosed_eq
    ((contDiff_mvPoly_eval (n + 1) (toMvPoly (Polynomial.derivative^[j] f))).continuous.comp
      continuous_finCons)
    continuous_const

/-! ### Main theorem -/

private lemma orderFull_factor_false
    {A : Finset (PolyR n)} {T : Set ((Fin n → ℝ) × ℝ)}
    (hconn : IsPreconnected T)
    (hne : ∀ f ∈ A, f ≠ 0)
    (hspec : ∀ f ∈ A, ∀ p ∈ T, specialize f p.1 ≠ 0)
    (hprod : OrderInvariantFull (∏ f ∈ A, f) T)
    {f : PolyR n} (hf : f ∈ A)
    {p q : (Fin n → ℝ) × ℝ} (hp : p ∈ T) (hq : q ∈ T)
    (hlt : (orderFull f p.1 p.2).toNat < (orderFull f q.1 q.2).toNat) :
    False := by
  set rest := ∏ g ∈ A.erase f, g
  have hne_rest : ∀ g ∈ A.erase f, g ≠ 0 :=
    fun g hg => hne g (Finset.mem_of_mem_erase hg)
  have hspec_rest : ∀ g ∈ A.erase f, ∀ s ∈ T, specialize g s.1 ≠ 0 :=
    fun g hg => hspec g (Finset.mem_of_mem_erase hg)
  have hf_fin (s : (Fin n → ℝ) × ℝ) (hs : s ∈ T) : orderFull f s.1 s.2 < ⊤ :=
    orderFull_lt_top_of_spec_ne (hspec f hf s hs) s.2
  have hr_fin (s : (Fin n → ℝ) × ℝ) (hs : s ∈ T) : orderFull rest s.1 s.2 < ⊤ := by
    show orderFull (∏ g ∈ A.erase f, g) s.1 s.2 < ⊤
    rw [orderFull_prod_sum]
    exact WithTop.sum_lt_top.mpr fun g hg =>
      orderFull_lt_top_of_spec_ne (hspec_rest g hg s hs) s.2
  -- ℕ extraction helpers (only for points in T)
  have hvf (s : (Fin n → ℝ) × ℝ) (hs : s ∈ T) :
      orderFull f s.1 s.2 = ↑((orderFull f s.1 s.2).toNat) :=
    (ENat.coe_toNat (hf_fin s hs).ne).symm
  have hvr (s : (Fin n → ℝ) × ℝ) (hs : s ∈ T) :
      orderFull rest s.1 s.2 = ↑((orderFull rest s.1 s.2).toNat) :=
    (ENat.coe_toNat (hr_fin s hs).ne).symm
  -- Sum identity: vf + vr = constant on T
  have hsplit (t : (Fin n → ℝ) × ℝ) (ht : t ∈ T) :
      (↑((orderFull f t.1 t.2).toNat) : ℕ∞) + ↑((orderFull rest t.1 t.2).toNat) =
      ∑ g ∈ A, orderFull g t.1 t.2 := by
    rw [← hvf t ht, ← hvr t ht]
    show orderFull f t.1 t.2 + orderFull (∏ g ∈ A.erase f, g) t.1 t.2 = _
    rw [orderFull_prod_sum (A.erase f)]
    exact Finset.add_sum_erase A (fun g => orderFull g t.1 t.2) hf
  have hnat_sum (s : (Fin n → ℝ) × ℝ) (hs : s ∈ T) :
      (orderFull f s.1 s.2).toNat + (orderFull rest s.1 s.2).toNat =
      (orderFull f p.1 p.2).toNat + (orderFull rest p.1 p.2).toNat := by
    have hconst : ∑ g ∈ A, orderFull g s.1 s.2 = ∑ g ∈ A, orderFull g p.1 p.2 := by
      rw [← orderFull_prod_sum, ← orderFull_prod_sum]; exact hprod s hs p hp
    have hs_eq := hsplit s hs; have hp_eq := hsplit p hp
    rw [← hs_eq, ← hp_eq] at hconst
    exact_mod_cast hconst
  -- Natural number names
  set a₁ := (orderFull f p.1 p.2).toNat
  set b₁ := (orderFull rest p.1 p.2).toNat
  set a₂ := (orderFull f q.1 q.2).toNat
  set b₂ := (orderFull rest q.1 q.2).toNat
  set cn := a₁ + b₁
  have hq_sum : a₂ + b₂ = cn := hnat_sum q hq
  -- Two closed sets
  set k := a₂
  set U := {s : (Fin n → ℝ) × ℝ | ↑k ≤ orderFull f s.1 s.2}
  set V := {s : (Fin n → ℝ) × ℝ | ↑(cn - k + 1) ≤ orderFull rest s.1 s.2}
  -- T ⊆ U ∪ V
  have hcover : T ⊆ U ∪ V := by
    intro s hs
    by_cases h : k ≤ (orderFull f s.1 s.2).toNat
    · left; show ↑k ≤ orderFull f s.1 s.2; rw [hvf s hs]; exact_mod_cast h
    · right; show ↑(cn - k + 1) ≤ orderFull rest s.1 s.2; rw [hvr s hs]
      have hs_sum := hnat_sum s hs
      exact_mod_cast show cn - k + 1 ≤ (orderFull rest s.1 s.2).toNat by omega
  -- T ∩ (U ∩ V) = ∅
  have hdisjoint : T ∩ (U ∩ V) = ∅ := by
    ext s; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, U, V]
    intro ⟨hs, hU, hV⟩
    have h1 : k ≤ (orderFull f s.1 s.2).toNat := by rw [hvf s hs] at hU; exact_mod_cast hU
    have h2 : cn - k + 1 ≤ (orderFull rest s.1 s.2).toNat := by
      rw [hvr s hs] at hV; exact_mod_cast hV
    have := hnat_sum s hs; omega
  -- Contradiction via preconnectedness
  have hp_not_U : p ∉ U := by
    show ¬(↑k ≤ orderFull f p.1 p.2); rw [hvf p hp]
    exact_mod_cast show ¬(k ≤ a₁) from Nat.not_le.mpr hlt
  have hq_not_V : q ∉ V := by
    show ¬(↑(cn - k + 1) ≤ orderFull rest q.1 q.2); rw [hvr q hq]
    exact_mod_cast show ¬(cn - k + 1 ≤ b₂) by omega
  exact (isPreconnected_iff_subset_of_disjoint_closed.mp hconn U V
    (isClosed_orderFull_ge f k) (isClosed_orderFull_ge rest (cn - k + 1))
    hcover hdisjoint).elim (fun h => hp_not_U (h hp)) (fun h => hq_not_V (h hq))

theorem order_invariant_full_factor_of_prod
    (A : Finset (PolyR n))
    (T : Set ((Fin n → ℝ) × ℝ))
    (hconn : IsPreconnected T)
    (hne : ∀ f ∈ A, f ≠ 0)
    (hspec : ∀ f ∈ A, ∀ p ∈ T, specialize f p.1 ≠ 0)
    (hprod : OrderInvariantFull (∏ f ∈ A, f) T) :
    ∀ f ∈ A, OrderInvariantFull f T := by
  intro f hf p hp q hq
  have hp_fin := orderFull_lt_top_of_spec_ne (hspec f hf p hp) p.2
  have hq_fin := orderFull_lt_top_of_spec_ne (hspec f hf q hq) q.2
  have hvp : orderFull f p.1 p.2 = ↑(orderFull f p.1 p.2).toNat :=
    (ENat.coe_toNat hp_fin.ne).symm
  have hvq : orderFull f q.1 q.2 = ↑(orderFull f q.1 q.2).toNat :=
    (ENat.coe_toNat hq_fin.ne).symm
  rcases lt_trichotomy (orderFull f p.1 p.2).toNat (orderFull f q.1 q.2).toNat with h | h | h
  · exact absurd h (Nat.not_lt.mpr (Nat.le_of_not_lt
      fun hlt => orderFull_factor_false hconn hne hspec hprod hf hp hq hlt))
  · rw [hvp, hvq, h]
  · exact absurd h (Nat.not_lt.mpr (Nat.le_of_not_lt
      fun hlt => orderFull_factor_false hconn hne hspec hprod hf hq hp hlt))

end
