import Mccalum

def an_sub (i : Nat) (S: Set (Fin i → ℝ)) : Prop := IsAnalyticSubmanifold S

def an_del (i : Nat) (S : Set (Fin i → ℝ)) (f : Polynomial (MvPolynomial (Fin i) ℝ)) : Prop := AnalyticDelineable f S

def connected (i : Nat) (S : Set (Fin i → ℝ)) : Prop := IsConnected S

def non_null (i : Nat) (S : Set (Fin i → ℝ)) (f : Polynomial (MvPolynomial (Fin i) ℝ)) : Prop :=
  ∀ a ∈ S, specialize f a ≠ 0

def ord_inv (i : Nat) (S : Set (Fin i → ℝ)) (f : MvPolynomial (Fin i) ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, polyOrder i f a = polyOrder i f b

theorem nalbach_4_1
    (i : Nat) (S : Set (Fin i → ℝ)) (f : PolyR i) (hf_sf : Squarefree f) (hf_i : f.natDegree > 1) :
    an_sub i S →
    connected i S →
    non_null i S f →
    ord_inv i S f.discr →
    sgn_inv i S f.leadingCoeff →
    an_del i S f := by

  intros h_sub h_conn h_non_null h_ord_inv h_sgn_inv
  have hp_i0 : f.natDegree > 0 := by omega
  have discr_ne_zero : f.discr ≠ 0 := by apply discr_ne_zero_of_squarefree f hf_sf hp_i0
  have deg_inv := brown_original i f hp_i0 discr_ne_zero S h_sub h_conn h_ord_inv h_sgn_inv h_non_null
  have hunit : IsUnit (f.natDegree : MvPolynomial (Fin i) ℝ) := by
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial (Fin i) ℝ) f.natDegree]
    exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  have discr_in_elim := Brown.discr_mem_span f hf_i hunit
  have := lifting_theorem_generalized S f h_sub h_conn deg_inv h_non_null f.discr discr_ne_zero discr_in_elim h_ord_inv
  exact this.1

#print axioms nalbach_4_1

theorem nalbach_4_1_generalized
  (i : Nat) (S : Set (Fin i → ℝ)) (f : PolyR i) (P : MvPolynomial (Fin i) ℝ)
  (hP : P ≠ 0) (hP_mem₁ : Polynomial.C P ∈
    Ideal.span ({ f, f.derivative } : Set (PolyR i)))
  (hP_mem₂ : Polynomial.C P ∈
    Ideal.span ({ f.reverse, f.reverse.derivative } : Set (PolyR i)))
  (hf_deg : f.natDegree > 0) :
    an_sub i S →
    connected i S →
    non_null i S f →
    ord_inv i S P →
    sgn_inv i S f.leadingCoeff →
    an_del i S f := by

  intros h_sub h_conn h_non_null h_ord_inv h_sgn_inv
  have h_deg_inv :=
    brown_generalized i f P hP hP_mem₁ hP_mem₂ hf_deg S h_sub h_conn h_ord_inv h_sgn_inv h_non_null
  have := lifting_theorem_generalized S f h_sub h_conn h_deg_inv h_non_null P hP hP_mem₁ h_ord_inv
  exact this.1

#print axioms nalbach_4_1_generalized
