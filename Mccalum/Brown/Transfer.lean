import Mathlib

/-!
# Transfer of elimination-ideal membership to shifted reverses

Algebraic core of the generalized Brown theorem (Theorem 3.1' of
`thesis/brown_generalized.tex`, the "Transfer" Lemma 4.6 there).

Given `f ∈ R[X]` of degree `n ≥ 1` and `P ∈ R` with
* `C P ∈ ⟨f, f'⟩` and
* `C P ∈ ⟨rev f, (rev f)'⟩`  (where `rev f = reflect n f` is the degree-`n` reverse),

we show that for every shift `γ ∈ R`,

* `C P ∈ ⟨f*_γ, (f*_γ)'⟩`, where `f*_γ := reflect n (f(X + γ))`.

The informal document proves this by passing to the bivariate homogenization
`F(Z, W)` and saturating the ideal `⟨F, F_Z, F_W⟩` at `⟨Z, W⟩`
(`P·⟨Z,W⟩^{2M} ⊆ J`).  Here the same argument is conducted entirely inside
`R[X]`, avoiding the homogenization layer:

1. the first membership transfers through "shift, then reflect" and yields
   `X^{M₁} * C P ∈ ⟨f*, (f*)'⟩` (`reflect_span_transfer`, via the Euler-type
   identity `reflect_derivative_eq` — Lemma 4.2 of the document);
2. the second membership transfers through the transform
   `Λ_γ^N := reflect N ∘ taylor γ ∘ reflect N` (the chart incarnation of the
   `Z ↔ W` swap composed with the shift), and yields
   `(1 + γX)^{M₂} * C P ∈ ⟨f*, (f*)'⟩` (`mobius_span_transfer`, via the
   Euler-type identity `mobius_derivative`);
3. `X` and `1 + γX` are coprime in `R[X]`, which plays the role of
   "`Z^i W^j` with `i + j = 2M` has `i ≥ M` or `j ≥ M`": together the two
   memberships give `C P ∈ ⟨f*, (f*)'⟩` (`membership_transfer_shifted_reverse`).

Everything is over an arbitrary commutative ring.
-/

noncomputable section

open Polynomial

namespace Brown

variable {R : Type*} [CommRing R]

/-! ### The Euler-type identity for `reflect` (Lemma 4.2) -/

/-- **Euler-type identity** relating reflection and differentiation:
`reflect N (φ') = (N+1) · reflect (N+1) φ - X · (reflect (N+1) φ)'`
for `deg φ ≤ N + 1`.  Both sides equal `∑ i·aᵢ·X^(N+1-i)` for `φ = ∑ aᵢ X^i`. -/
theorem reflect_derivative_eq (φ : R[X]) (N : ℕ) (hφ : φ.natDegree ≤ N + 1) :
    reflect N (derivative φ) =
      C ((N + 1 : ℕ) : R) * reflect (N + 1) φ - X * derivative (reflect (N + 1) φ) := by
  ext k
  rw [coeff_reflect, coeff_derivative, coeff_sub, coeff_C_mul, coeff_reflect]
  rcases k with _ | j
  · -- k = 0: the `X * _` term contributes nothing
    rw [revAt_zero, revAt_zero, mul_coeff_zero, coeff_X_zero, zero_mul, sub_zero]
    push_cast
    ring
  · -- k = j + 1
    rw [coeff_X_mul, coeff_derivative, coeff_reflect]
    rcases lt_trichotomy (j + 1) (N + 1) with hlt | heq | hgt
    · -- j + 1 ≤ N
      have hjN : j + 1 ≤ N := by omega
      rw [revAt_le hjN, revAt_le (by omega : j + 1 ≤ N + 1),
        show N - (j + 1) + 1 = N + 1 - (j + 1) from by omega,
        show N + 1 - (j + 1) = N - j from by omega]
      have hc : ((N - (j + 1) : ℕ) : R) = (N : R) - (j : R) - 1 := by
        rw [Nat.cast_sub hjN]; push_cast; ring
      rw [hc]
      push_cast
      ring
    · -- j + 1 = N + 1: both sides vanish
      have hz : φ.coeff (j + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [revAt_eq_self_of_lt (by omega : N < j + 1),
        revAt_le (by omega : j + 1 ≤ N + 1),
        show N + 1 - (j + 1) = 0 from by omega, hz, zero_mul, ← heq]
      push_cast
      ring
    · -- j + 1 > N + 1: both sides vanish
      have hz1 : φ.coeff (j + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      have hz2 : φ.coeff (j + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [revAt_eq_self_of_lt (by omega : N < j + 1),
        revAt_eq_self_of_lt (by omega : N + 1 < j + 1), hz1, hz2]
      ring

/-! ### Shift (`taylor`) commutes with differentiation -/

/-- The shift `taylor γ` commutes with `derivative` (the derivative of `X + C γ` is `1`). -/
theorem taylor_derivative (γ : R) (ψ : R[X]) :
    taylor γ (derivative ψ) = derivative (taylor γ ψ) := by
  rw [taylor_apply, taylor_apply, derivative_comp, derivative_X_add_C, one_mul]

/-! ### Reflection of `(X + C γ)^N` -/

private lemma natDegree_X_add_C_le (γ : R) : (X + C γ : R[X]).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans (max_le natDegree_X_le ((natDegree_C γ).le.trans zero_le_one))

theorem reflect_X_add_C_pow (γ : R) (N : ℕ) :
    reflect N ((X + C γ) ^ N) = (1 + C γ * X) ^ N := by
  induction N with
  | zero => simp
  | succ M ih =>
    have hdeg : ((X + C γ : R[X]) ^ M).natDegree ≤ M :=
      natDegree_pow_le.trans (by
        calc M * (X + C γ : R[X]).natDegree ≤ M * 1 :=
              Nat.mul_le_mul_left M (natDegree_X_add_C_le γ)
          _ = M := Nat.mul_one M)
    have h2 : reflect (1 + M) ((X + C γ) * (X + C γ) ^ M)
        = reflect 1 (X + C γ) * reflect M ((X + C γ) ^ M) :=
      reflect_mul _ _ (natDegree_X_add_C_le γ) hdeg
    rw [pow_succ' (X + C γ) M, show M + 1 = 1 + M from Nat.add_comm M 1, h2, ih,
      reflect_add, reflect_one_X, reflect_C, pow_one, pow_add, pow_one]

/-! ### The transform `Λ_γ^N = reflect N ∘ taylor γ ∘ reflect N` -/

/-- The "reverse–shift–reverse" transform at formal degree `N`.  On polynomials of
degree `≤ N` it realizes `φ(z) ↦ (γz+1)^N · φ(z/(γz+1))`, the lower-triangular
Möbius substitution; it is the chart-level incarnation of the homogeneous swap
`Z ↔ W` conjugated with the shift. -/
def mobius (γ : R) (N : ℕ) (φ : R[X]) : R[X] :=
  reflect N (taylor γ (reflect N φ))

theorem mobius_add (γ : R) (N : ℕ) (φ ψ : R[X]) :
    mobius γ N (φ + ψ) = mobius γ N φ + mobius γ N ψ := by
  unfold mobius
  rw [reflect_add, map_add, reflect_add]

theorem natDegree_mobius_le (γ : R) (N : ℕ) (φ : R[X]) (h : φ.natDegree ≤ N) :
    (mobius γ N φ).natDegree ≤ N :=
  natDegree_reflect_le.trans (max_le le_rfl
    (by rw [natDegree_taylor]; exact natDegree_reflect_le.trans (max_le le_rfl h)))

/-- `Λ_γ` is multiplicative on matching formal degrees (like `reflect_mul`). -/
theorem mobius_mul (γ : R) {a b : ℕ} (φ ψ : R[X])
    (ha : φ.natDegree ≤ a) (hb : ψ.natDegree ≤ b) :
    mobius γ (a + b) (φ * ψ) = mobius γ a φ * mobius γ b ψ := by
  have h1 : (taylor γ (reflect a φ)).natDegree ≤ a := by
    rw [natDegree_taylor]; exact natDegree_reflect_le.trans (max_le le_rfl ha)
  have h2 : (taylor γ (reflect b ψ)).natDegree ≤ b := by
    rw [natDegree_taylor]; exact natDegree_reflect_le.trans (max_le le_rfl hb)
  unfold mobius
  rw [reflect_mul φ ψ ha hb, taylor_mul, reflect_mul _ _ h1 h2]

/-- `Λ_γ^N (C P) = C P * (1 + γX)^N` — constants pick up the cofactor `(1 + γX)^N`. -/
theorem mobius_C (γ : R) (N : ℕ) (P : R) :
    mobius γ N (C P) = C P * (1 + C γ * X) ^ N := by
  unfold mobius
  rw [reflect_C, taylor_mul, taylor_C, taylor_X_pow, reflect_C_mul, reflect_X_add_C_pow]

/-- **Euler-type identity for `Λ_γ`**:
`Λ_γ^N (φ') = (1 + γX) · (Λ_γ^{N+1} φ)' - (N+1) γ · Λ_γ^{N+1} φ`
for `deg φ ≤ N + 1`.  Derived from `reflect_derivative_eq` (used three times)
plus the involutivity of `reflect`. -/
theorem mobius_derivative (γ : R) (N : ℕ) (φ : R[X]) (hφ : φ.natDegree ≤ N + 1) :
    mobius γ N (derivative φ) =
      (1 + C γ * X) * derivative (mobius γ (N + 1) φ)
        - C ((N + 1 : ℕ) : R) * (C γ * mobius γ (N + 1) φ) := by
  set Φ : R[X] := reflect (N + 1) φ with hΦ_def
  set Φb : R[X] := taylor γ Φ with hΦb_def
  set T : R[X] := reflect (N + 1) Φb with hT_def
  have hT : mobius γ (N + 1) φ = T := rfl
  have hΦb_eq : Φb = reflect (N + 1) T := by rw [hT_def, reflect_reflect]
  have hΦdeg : Φ.natDegree ≤ N + 1 :=
    natDegree_reflect_le.trans (max_le le_rfl hφ)
  have hΦbdeg : Φb.natDegree ≤ N + 1 := by
    rw [hΦb_def, natDegree_taylor]; exact hΦdeg
  have hTdeg : T.natDegree ≤ N + 1 :=
    natDegree_reflect_le.trans (max_le le_rfl hΦbdeg)
  -- Euler for `φ`, pushed through `taylor γ`
  have h2 : taylor γ (reflect N (derivative φ))
      = C ((N + 1 : ℕ) : R) * Φb - (X + C γ) * derivative Φb := by
    rw [reflect_derivative_eq φ N hφ, map_sub, taylor_mul, taylor_mul, taylor_C, taylor_X,
      taylor_derivative]
  -- Euler for `T` rewrites the first two summands
  have h3 : C ((N + 1 : ℕ) : R) * Φb - X * derivative Φb = reflect N (derivative T) := by
    rw [hΦb_eq]
    exact (reflect_derivative_eq T N hTdeg).symm
  have h4 : taylor γ (reflect N (derivative φ))
      = reflect N (derivative T) - C γ * derivative Φb := by
    rw [h2, ← h3]; ring
  -- apply `reflect N` and use Euler for `Φb`
  have h5 : mobius γ N (derivative φ)
      = derivative T - C γ * reflect N (derivative Φb) := by
    show reflect N (taylor γ (reflect N (derivative φ))) = _
    rw [h4, reflect_sub, reflect_C_mul, reflect_reflect]
  have h6 : reflect N (derivative Φb)
      = C ((N + 1 : ℕ) : R) * T - X * derivative T :=
    reflect_derivative_eq Φb N hΦbdeg
  rw [hT, h5, h6]
  ring

/-! ### Transfer of span membership through the three transforms -/

/-- Membership in `⟨φ, φ'⟩` transfers through the shift `taylor γ`. -/
theorem taylor_span_transfer (γ : R) (φ : R[X]) (P : R)
    (hP : C P ∈ Ideal.span ({φ, derivative φ} : Set R[X])) :
    C P ∈ Ideal.span ({taylor γ φ, derivative (taylor γ φ)} : Set R[X]) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
  refine Ideal.mem_span_pair.mpr ⟨taylor γ A, taylor γ B, ?_⟩
  rw [← taylor_derivative, ← taylor_mul, ← taylor_mul, ← map_add, hAB, taylor_C]

/-- Membership in `⟨φ, φ'⟩` transfers through `reflect (N+1)` at the cost of a
factor `X^M` (Lemma 6.2(i) of the document, "reflection"). -/
theorem reflect_span_transfer (N : ℕ) (φ : R[X]) (hφ : φ.natDegree ≤ N + 1) (P : R)
    (hP : C P ∈ Ideal.span ({φ, derivative φ} : Set R[X])) :
    ∃ M : ℕ, X ^ M * C P ∈
      Ideal.span ({reflect (N + 1) φ, derivative (reflect (N + 1) φ)} : Set R[X]) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
  set M := max (A.natDegree + (N + 1)) (B.natDegree + N) with hM_def
  have hMN1 : N + 1 ≤ M := le_max_of_le_left (Nat.le_add_left _ _)
  have hA : A.natDegree ≤ M - (N + 1) := by
    have := le_max_left (A.natDegree + (N + 1)) (B.natDegree + N)
    omega
  have hB : B.natDegree ≤ M - N := by
    have := le_max_right (A.natDegree + (N + 1)) (B.natDegree + N)
    omega
  have haM : (M - (N + 1)) + (N + 1) = M := by omega
  have hbM : (M - N) + N = M := by omega
  have hφ' : (derivative φ).natDegree ≤ N := by
    have := natDegree_derivative_le φ
    omega
  have e1 : reflect M (A * φ) = reflect (M - (N + 1)) A * reflect (N + 1) φ := by
    conv_lhs => rw [← haM]
    exact reflect_mul A φ hA hφ
  have e2 : reflect M (B * derivative φ)
      = reflect (M - N) B * reflect N (derivative φ) := by
    conv_lhs => rw [← hbM]
    exact reflect_mul B (derivative φ) hB hφ'
  have key : C P * X ^ M
      = reflect (M - (N + 1)) A * reflect (N + 1) φ
        + reflect (M - N) B *
          (C ((N + 1 : ℕ) : R) * reflect (N + 1) φ - X * derivative (reflect (N + 1) φ)) := by
    rw [← reflect_derivative_eq φ N hφ, ← e1, ← e2, ← reflect_add, hAB, reflect_C]
  refine ⟨M, Ideal.mem_span_pair.mpr
    ⟨reflect (M - (N + 1)) A + C ((N + 1 : ℕ) : R) * reflect (M - N) B,
     -(X * reflect (M - N) B), ?_⟩⟩
  linear_combination key.symm

/-- Membership in `⟨φ, φ'⟩` transfers through `Λ_γ^{N+1}` at the cost of a factor
`(1 + γX)^M` (the second half of the saturation argument). -/
theorem mobius_span_transfer (γ : R) (N : ℕ) (φ : R[X]) (hφ : φ.natDegree ≤ N + 1) (P : R)
    (hP : C P ∈ Ideal.span ({φ, derivative φ} : Set R[X])) :
    ∃ M : ℕ, (1 + C γ * X) ^ M * C P ∈
      Ideal.span ({mobius γ (N + 1) φ, derivative (mobius γ (N + 1) φ)} : Set R[X]) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
  set M := max (A.natDegree + (N + 1)) (B.natDegree + N) with hM_def
  have hMN1 : N + 1 ≤ M := le_max_of_le_left (Nat.le_add_left _ _)
  have hA : A.natDegree ≤ M - (N + 1) := by
    have := le_max_left (A.natDegree + (N + 1)) (B.natDegree + N)
    omega
  have hB : B.natDegree ≤ M - N := by
    have := le_max_right (A.natDegree + (N + 1)) (B.natDegree + N)
    omega
  have haM : (M - (N + 1)) + (N + 1) = M := by omega
  have hbM : (M - N) + N = M := by omega
  have hφ' : (derivative φ).natDegree ≤ N := by
    have := natDegree_derivative_le φ
    omega
  have e1 : mobius γ M (A * φ) = mobius γ (M - (N + 1)) A * mobius γ (N + 1) φ := by
    conv_lhs => rw [← haM]
    exact mobius_mul γ A φ hA hφ
  have e2 : mobius γ M (B * derivative φ)
      = mobius γ (M - N) B * mobius γ N (derivative φ) := by
    conv_lhs => rw [← hbM]
    exact mobius_mul γ B (derivative φ) hB hφ'
  have key : C P * (1 + C γ * X) ^ M
      = mobius γ (M - (N + 1)) A * mobius γ (N + 1) φ
        + mobius γ (M - N) B *
          ((1 + C γ * X) * derivative (mobius γ (N + 1) φ)
            - C ((N + 1 : ℕ) : R) * (C γ * mobius γ (N + 1) φ)) := by
    rw [← mobius_derivative γ N φ hφ, ← e1, ← e2, ← mobius_add, hAB, mobius_C]
  refine ⟨M, Ideal.mem_span_pair.mpr
    ⟨mobius γ (M - (N + 1)) A
        - C ((N + 1 : ℕ) : R) * (C γ * mobius γ (M - N) B),
     (1 + C γ * X) * mobius γ (M - N) B, ?_⟩⟩
  linear_combination key.symm

/-! ### The coprimality finish -/

theorem isCoprime_X_one_add_C (γ : R) : IsCoprime (X : R[X]) (1 + C γ * X) :=
  ⟨-C γ, 1, by ring⟩

/-- **Transfer lemma** (Lemma 4.6 of the document).  If `C P` lies in the
elimination-style ideals of both `f` and its degree-`n` reverse, then it lies in
the ideal of the shifted reverse `f*_γ = reflect n (taylor γ f)`, for every `γ`. -/
theorem membership_transfer_shifted_reverse
    (f : R[X]) (hpos : 0 < f.natDegree) (γ : R) (P : R)
    (h₁ : C P ∈ Ideal.span ({f, derivative f} : Set R[X]))
    (h₂ : C P ∈ Ideal.span ({f.reverse, derivative f.reverse} : Set R[X])) :
    C P ∈ Ideal.span ({reflect f.natDegree (taylor γ f),
      derivative (reflect f.natDegree (taylor γ f))} : Set R[X]) := by
  obtain ⟨m, hm⟩ : ∃ m, f.natDegree = m + 1 := ⟨f.natDegree - 1, by omega⟩
  rw [hm]
  -- Branch 1: shift then reflect, picking up `X^M₁`
  have hshift : C P ∈ Ideal.span ({taylor γ f, derivative (taylor γ f)} : Set R[X]) :=
    taylor_span_transfer γ f P h₁
  obtain ⟨M₁, hM₁⟩ := reflect_span_transfer m (taylor γ f)
    (by rw [natDegree_taylor]; omega) P hshift
  -- Branch 2: `Λ_γ` applied to the reverse, picking up `(1 + γX)^M₂`
  have h₂' : C P ∈ Ideal.span
      ({reflect (m + 1) f, derivative (reflect (m + 1) f)} : Set R[X]) := by
    rwa [Polynomial.reverse, hm] at h₂
  obtain ⟨M₂, hM₂⟩ := mobius_span_transfer γ m (reflect (m + 1) f)
    (natDegree_reflect_le.trans (max_le le_rfl (by omega))) P h₂'
  have hmob : mobius γ (m + 1) (reflect (m + 1) f) = reflect (m + 1) (taylor γ f) := by
    unfold mobius
    rw [reflect_reflect]
  rw [hmob] at hM₂
  -- Coprimality of `X^M₁` and `(1 + γX)^M₂` clears both cofactors
  obtain ⟨u, v, huv⟩ := (isCoprime_X_one_add_C γ).pow (m := M₁) (n := M₂)
  have hsplit : C P = u * (X ^ M₁ * C P) + v * ((1 + C γ * X) ^ M₂ * C P) := by
    linear_combination (C P : R[X]) * huv.symm
  rw [hsplit]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ u hM₁) (Ideal.mul_mem_left _ v hM₂)

/-! ### Trailing degree of a reflection

Bookkeeping for step (2) of the main proof: the multiplicity of `0` as a root of
the reverse records the degree drop. -/

/-- For `ψ ≠ 0` with `deg ψ ≤ N`, the trailing degree of `reflect N ψ` is
`N - deg ψ`. -/
theorem natTrailingDegree_reflect {ψ : R[X]} {N : ℕ} (hψ : ψ ≠ 0)
    (hdeg : ψ.natDegree ≤ N) :
    (reflect N ψ).natTrailingDegree = N - ψ.natDegree := by
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_reflect, revAt_le (by omega : N - ψ.natDegree ≤ N),
      Nat.sub_sub_self hdeg]
    exact leadingCoeff_ne_zero.mpr hψ
  · apply le_natTrailingDegree (by rwa [Ne, reflect_eq_zero_iff])
    intro m hm
    rw [coeff_reflect]
    apply coeff_eq_zero_of_natDegree_lt
    rw [revAt_le (by omega : m ≤ N)]
    omega

end Brown
