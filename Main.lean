import Mccalum

noncomputable def sgn (a : ℝ) : ℤ :=
  if a > 0 then 1 else if a = 0 then 0 else -1

def an_sub (i : Nat) (S: Set (Fin i → ℝ)) : Prop := IsAnalyticSubmanifold S

def an_del (i : Nat) (S : Set (Fin i → ℝ)) (f : Polynomial (MvPolynomial (Fin i) ℝ)) : Prop := AnalyticDelineable f S

def connected (i : Nat) (S : Set (Fin i → ℝ)) : Prop := IsConnected S

def non_null (i : Nat) (S : Set (Fin i → ℝ)) (f : Polynomial (MvPolynomial (Fin i) ℝ)) : Prop :=
  ∀ a ∈ S, specialize f a ≠ 0

def ord_inv (i : Nat) (S : Set (Fin i → ℝ)) (f : MvPolynomial (Fin i) ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, polyOrder i f a = polyOrder i f b

def sgn_inv (i : Nat) (S : Set (Fin i → ℝ)) (f : MvPolynomial (Fin i) ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, sgn (f.eval a) = sgn (f.eval b)

theorem deg_inv_of_ldcf_sgn_inv (i : Nat) (p : Polynomial (MvPolynomial (Fin i) ℝ)) (S : Set (Fin i → ℝ)) (hp_i : p.natDegree > 0) (h_non_null : non_null i S p) :
    sgn_inv i S p.leadingCoeff → DegreeInvariant p S := by
  intros h s1 hs1 s2 hs2
  simp [sgn_inv] at h
  have := h s1 hs1 s2 hs2
  if h_deg: MvPolynomial.eval s1 p.leadingCoeff = 0 then
    have := h_non_null s1 hs1
    admit
  else
    admit

theorem discr_in_elim_ideal (i : Nat) (p : Polynomial (MvPolynomial (Fin i) ℝ)) : Polynomial.C p.discr ∈ Ideal.span ({p, Polynomial.derivative p} : Set (PolyR i)) := sorry

theorem nalbach_4_1 (i : Nat) (S : Set (Fin i → ℝ)) (p : Polynomial (MvPolynomial (Fin i) ℝ)) (hp_sf : Squarefree p) (hp_i : p.natDegree > 0) :
    an_sub i S →
    connected i S →
    non_null i S p →
    ord_inv i S p.discr →
    sgn_inv i S p.leadingCoeff →
    an_del i S p := by

  intros h_sub h_conn h_non_null h_ord_inv h_sgn_inv
  have deg_inv := deg_inv_of_ldcf_sgn_inv i p S hp_i h_non_null h_sgn_inv
  have discr_in_elim := discr_in_elim_ideal i p
  have discr_ne_zero : p.discr ≠ 0 := by apply discr_ne_zero_of_squarefree p hp_sf hp_i
  have := lifting_theorem_generalized S p h_sub h_conn deg_inv h_non_null p.discr discr_ne_zero discr_in_elim h_ord_inv
  exact this.1
