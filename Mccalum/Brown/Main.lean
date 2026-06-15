import Mathlib
import Mccalum.Generalized.Projection
import Mccalum.Brown.Transfer
import Mccalum.Brown.Refine
import Mccalum.Brown.Discr

/-!
# Brown's theorem, generalized to elimination ideals (Theorem 3.1')

`brown_generalized` is Theorem 3.1' of `thesis/brown_generalized.tex` (Version B):
if `P ≠ 0` lies in both `⟨f, f_z⟩ ∩ R[x]` and `⟨rev f, (rev f)'⟩ ∩ R[x]`, `P` is
order-invariant on the connected analytic submanifold `S`, `lc f` is
sign-invariant on `S`, and `f` vanishes identically at no point of `S`, then `f`
is degree-invariant on `S`.

Proof layout (following §5 of the document):
* if `lc f` is nowhere zero on `S`, the degree is constantly `deg f` (easy case);
* otherwise `lc f ≡ 0` on `S`.  At each `p ∈ S` choose `γ` with `f(p, γ) ≠ 0`,
  pass to the auxiliary polynomial `f* = reflect n (taylor γ f)`, transfer the
  membership hypotheses to `⟨f*, (f*)'⟩` (`Brown.membership_transfer_shifted_reverse`,
  which replaces the homogenization layer of the document by a coprimality
  argument in `R[z]`), refine `S` to a connected analytic submanifold `S ∩ N`
  inside `{f(·, γ) ≠ 0}` (`IsAnalyticSubmanifold.refine_connected`), and apply the
  generalized lifting theorem to `f*`.  The multiplicity of the root `0` of `f*`
  along the unique delineation branch through `0` records the degree drop
  `n - deg f(q, ·)`, which is therefore locally constant;
* a locally constant function on connected `S` is constant.
-/

noncomputable def sgn (r : ℝ) : ℤ := if r > 0 then 1 else if r = 0 then 0 else -1

def sgn_inv (i : Nat) (S : Set (Fin i → ℝ)) (f : MvPolynomial (Fin i) ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, sgn (f.eval a) = sgn (f.eval b)

open Polynomial in
private lemma sgn_eq_zero_iff {x : ℝ} : sgn x = 0 ↔ x = 0 := by
  unfold sgn
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h (ne_of_gt h1)⟩
  · simp [h2]
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h h2⟩

open Polynomial in
/-- Specialization commutes with the shift-and-reflect construction of `f*`. -/
private lemma spec_reflect_taylor {k : Nat} (f : PolyR k) (γ : ℝ) (q : Fin k → ℝ) :
    specialize (reflect f.natDegree (taylor (MvPolynomial.C γ) f)) q
      = reflect f.natDegree (taylor γ (specialize f q)) := by
  show (reflect f.natDegree (taylor (MvPolynomial.C γ) f)).map (evalBase q) = _
  rw [← reflect_map, map_taylor]
  have hc : evalBase q (MvPolynomial.C γ) = γ := by simp
  rw [hc]
  rfl

open Polynomial in
/-- **Hard case, local step**: if `lc f ≡ 0` on `S`, the specialized degree of `f`
is locally constant on `S`.  This is the pointwise argument of Theorem 3.1'. -/
private theorem brown_degree_locally_constant
    (k : Nat) (f : PolyR k) (P : MvPolynomial (Fin k) ℝ)
    (P_ne_zero : P ≠ 0)
    (hP_mem₁ : Polynomial.C P ∈
      Ideal.span ({ f, f.derivative } : Set (PolyR k)))
    (hP_mem₂ : Polynomial.C P ∈
      Ideal.span ({ f.reverse, f.reverse.derivative } : Set (PolyR k)))
    (pos_deg : 0 < f.natDegree)
    (S : Set (Fin k → ℝ))
    (hS : IsAnalyticSubmanifold S)
    (h_ord : OrderInvariantMv P S)
    (h_lc : ∀ q ∈ S, evalBase q f.leadingCoeff = 0)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    (p : Fin k → ℝ) (hp : p ∈ S) :
    ∃ N : Set (Fin k → ℝ), IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ S ∩ N, (specialize f q).natDegree = (specialize f p).natDegree := by
  classical
  -- choose a shift `γ` avoiding the (finitely many) roots of `f(p, ·)`
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, (specialize f p).eval γ ≠ 0 :=
    Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ (hspec_ne p hp)
      (lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk ℝ))
  -- the auxiliary polynomial `f*` and the transferred witness membership
  have htransfer : Polynomial.C P ∈ Ideal.span
      ({reflect f.natDegree (taylor (MvPolynomial.C γ) f),
        derivative (reflect f.natDegree (taylor (MvPolynomial.C γ) f))} : Set (PolyR k)) :=
    Brown.membership_transfer_shifted_reverse f pos_deg (MvPolynomial.C γ) P hP_mem₁ hP_mem₂
  set fstar : PolyR k := reflect f.natDegree (taylor (MvPolynomial.C γ) f) with hfstar_def
  -- the formal leading coefficient of `f*` is `f(·, γ)`; its constant coefficient is `lc f`
  have hkey : ∀ q, evalBase q (fstar.coeff f.natDegree) = (specialize f q).eval γ := by
    intro q
    rw [← Polynomial.coeff_map]
    show (specialize fstar q).coeff f.natDegree = _
    rw [hfstar_def, spec_reflect_taylor, coeff_reflect, revAt_le (le_refl f.natDegree),
      Nat.sub_self, taylor_coeff_zero]
  have hfstar_coeff0 : fstar.coeff 0 = f.leadingCoeff := by
    rw [hfstar_def, coeff_reflect, revAt_zero]
    conv_lhs => rw [show f.natDegree = (taylor (MvPolynomial.C γ) f).natDegree
      from (natDegree_taylor f (MvPolynomial.C γ)).symm]
    rw [coeff_natDegree, leadingCoeff_taylor]
  -- the open set where the formal leading coefficient of `f*` survives
  set N₀ : Set (Fin k → ℝ) := {q | evalBase q (fstar.coeff f.natDegree) ≠ 0} with hN₀_def
  have hN₀_open : IsOpen N₀ :=
    isOpen_ne.preimage (MvPolynomial.continuous_eval _)
  have hpN₀ : p ∈ N₀ := by
    show evalBase p (fstar.coeff f.natDegree) ≠ 0
    rw [hkey p]
    exact hγ
  -- `f*` has constant degree `n` over `N₀`
  have hdeg_fstar : ∀ q ∈ N₀, (specialize fstar q).natDegree = f.natDegree := by
    intro q hq
    apply le_antisymm
    · refine Polynomial.natDegree_map_le.trans ?_
      rw [hfstar_def]
      exact natDegree_reflect_le.trans
        (max_le le_rfl (le_of_eq (natDegree_taylor f (MvPolynomial.C γ))))
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [show (specialize fstar q).coeff f.natDegree
          = evalBase q (fstar.coeff f.natDegree) from Polynomial.coeff_map _ _]
      exact hq
  have hne_fstar : ∀ q ∈ N₀, specialize fstar q ≠ 0 := by
    intro q hq h0
    apply hq
    show evalBase q (fstar.coeff f.natDegree) = 0
    rw [← Polynomial.coeff_map]
    show (specialize fstar q).coeff f.natDegree = 0
    rw [h0, Polynomial.coeff_zero]
  -- refine `S` inside `N₀` to a connected analytic submanifold (Brown's Lemma 8.2)
  obtain ⟨N₁, hN₁_open, hpN₁, hN₁_sub, hSN₁_mfld, hSN₁_conn⟩ :=
    hS.refine_connected hp hN₀_open hpN₀
  -- apply the generalized lifting theorem to `f*` on `S ∩ N₁`
  have hdeg_inv : DegreeInvariant fstar (S ∩ N₁) := by
    intro x hx y hy
    rw [hdeg_fstar x (hN₁_sub hx.2), hdeg_fstar y (hN₁_sub hy.2)]
  obtain ⟨hdelin, -⟩ := lifting_theorem_generalized (S ∩ N₁) fstar hSN₁_mfld hSN₁_conn
    hdeg_inv (fun x hx => hne_fstar x (hN₁_sub hx.2)) P P_ne_zero htransfer
    (fun x hx y hy => h_ord x hx.1 y hy.1)
  obtain ⟨nb, θ, mult, hθ_an, hθ_ord, hθ_roots, hmult_pos, hmult_const⟩ := hdelin
  -- on `S`, the constant coefficient of `f*` vanishes, so `0` is a root
  have hzero_root : ∀ q ∈ S ∩ N₁, (specialize fstar q).IsRoot 0 := by
    intro q hq
    show (specialize fstar q).eval 0 = 0
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    show (fstar.map (evalBase q)).coeff 0 = 0
    rw [Polynomial.coeff_map, hfstar_coeff0]
    exact h_lc q hq.1
  have hpSN₁ : p ∈ S ∩ N₁ := ⟨hp, hpN₁⟩
  -- the unique branch through `0` at `p`
  obtain ⟨i₀, hi₀⟩ := (hθ_roots p hpSN₁ 0).mp (hzero_root p hpSN₁)
  -- isolate that branch: near `p` (within `S ∩ N₁`) no other branch passes through `0`
  have hsep : ∀ᶠ q in nhdsWithin p (S ∩ N₁), ∀ j, j ≠ i₀ → θ j q ≠ 0 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i₀
    · exact Filter.Eventually.of_forall fun q hcon => absurd hj hcon
    · have hθjp : θ j p ≠ 0 := by
        intro h0
        have heq2 : θ j p = θ i₀ p := by rw [h0]; exact hi₀
        rcases lt_or_gt_of_ne hj with h | h
        · exact absurd heq2 (ne_of_lt (hθ_ord p hpSN₁ j i₀ h))
        · exact absurd heq2.symm (ne_of_lt (hθ_ord p hpSN₁ i₀ j h))
      have htend : Filter.Tendsto (θ j) (nhdsWithin p (S ∩ N₁)) (nhds (θ j p)) :=
        (hθ_an j).continuousOn p hpSN₁
      filter_upwards [htend.eventually (isOpen_ne.mem_nhds hθjp)] with q hq _
      exact hq
  obtain ⟨O, hO_open, hpO, hO_sub⟩ := mem_nhdsWithin.mp hsep
  -- on `S ∩ (N₁ ∩ O)` the degree of `f` is constantly `n - mult i₀`
  have key : ∀ q ∈ S ∩ (N₁ ∩ O),
      (specialize f q).natDegree = f.natDegree - mult i₀ := by
    rintro q ⟨hqS, hqN₁, hqO⟩
    have hqSN₁ : q ∈ S ∩ N₁ := ⟨hqS, hqN₁⟩
    obtain ⟨j, hj⟩ := (hθ_roots q hqSN₁ 0).mp (hzero_root q hqSN₁)
    have hj_eq : j = i₀ := by
      by_contra hne
      exact hO_sub ⟨hqO, hqSN₁⟩ j hne hj.symm
    have hθi₀q : θ i₀ q = 0 := by rw [← hj_eq, ← hj]
    have hm := hmult_const q hqSN₁ i₀
    rw [hθi₀q] at hm
    have hψ_ne : taylor γ (specialize f q) ≠ 0 := by
      rw [Ne, taylor_eq_zero]
      exact hspec_ne q hqS
    have hψ_deg : (taylor γ (specialize f q)).natDegree ≤ f.natDegree := by
      rw [natDegree_taylor]
      exact Polynomial.natDegree_map_le
    have htrail : (specialize fstar q).rootMultiplicity 0
        = f.natDegree - (specialize f q).natDegree := by
      rw [hfstar_def, spec_reflect_taylor, Polynomial.rootMultiplicity_eq_natTrailingDegree',
        Brown.natTrailingDegree_reflect hψ_ne hψ_deg, natDegree_taylor]
    have hdeg_le : (specialize f q).natDegree ≤ f.natDegree :=
      Polynomial.natDegree_map_le
    have hmult_le : mult i₀ ≤ f.natDegree := by omega
    omega
  refine ⟨N₁ ∩ O, hN₁_open.inter hO_open, ⟨hpN₁, hpO⟩, ?_⟩
  intro q hq
  rw [key q hq, key p ⟨hp, hpN₁, hpO⟩]

theorem brown_generalized
    (k : Nat)
    (f : PolyR k)
    (P : MvPolynomial (Fin k) ℝ)
    (P_ne_zero : P ≠ 0)
    (hP_mem₁ : Polynomial.C P ∈
      Ideal.span ({ f, f.derivative } : Set (PolyR k)))
    (hP_mem₂ : Polynomial.C P ∈
      Ideal.span ({ f.reverse, f.reverse.derivative } : Set (PolyR k)))
    (pos_deg : 0 < f.natDegree)
    (S : Set (Fin k → ℝ))
    (hS : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (h_ord : OrderInvariantMv P S)
    (h_sgn : sgn_inv k S f.leadingCoeff)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    : DegreeInvariant f S := by
  classical
  obtain ⟨q₀, hq₀⟩ := hS_conn.nonempty
  by_cases hlc0 : evalBase q₀ f.leadingCoeff = 0
  · -- hard case: by sign-invariance, `lc f` vanishes identically on `S`
    have h_lc : ∀ q ∈ S, evalBase q f.leadingCoeff = 0 := by
      intro q hq
      have h := h_sgn q hq q₀ hq₀
      have h0 : sgn (evalBase q₀ f.leadingCoeff) = 0 := sgn_eq_zero_iff.mpr hlc0
      exact sgn_eq_zero_iff.mp (h.trans h0)
    -- the specialized degree is locally constant on `S` ...
    have hloc : ∀ p ∈ S, ∃ N : Set (Fin k → ℝ), IsOpen N ∧ p ∈ N ∧
        ∀ q ∈ S ∩ N, (specialize f q).natDegree = (specialize f p).natDegree :=
      fun p hp => brown_degree_locally_constant k f P P_ne_zero hP_mem₁ hP_mem₂ pos_deg
        S hS h_ord h_lc hspec_ne p hp
    -- ... hence (by connectedness) globally constant
    have hcont : ContinuousOn (fun q => (specialize f q).natDegree) S := by
      intro p hp
      rw [ContinuousWithinAt, nhds_discrete ℕ, Filter.tendsto_pure]
      obtain ⟨N, hN_open, hpN, hconst⟩ := hloc p hp
      exact Filter.mem_of_superset (inter_mem_nhdsWithin S (hN_open.mem_nhds hpN))
        fun q hq => hconst q ⟨hq.1, hq.2⟩
    intro a ha b hb
    exact hS_conn.isPreconnected.constant hcont ha hb
  · -- easy case: by sign-invariance, `lc f` is nowhere zero on `S`,
    -- so the degree is constantly `deg f`
    have h_lc_ne : ∀ q ∈ S, evalBase q f.leadingCoeff ≠ 0 := by
      intro q hq hq0
      apply hlc0
      have h := h_sgn q₀ hq₀ q hq
      have h0 : sgn (evalBase q f.leadingCoeff) = 0 := sgn_eq_zero_iff.mpr hq0
      exact sgn_eq_zero_iff.mp (h.trans h0)
    intro a ha b hb
    show (f.map (evalBase a)).natDegree = (f.map (evalBase b)).natDegree
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne a ha),
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne b hb)]

#print axioms brown_generalized

open Polynomial in
/-- **Brown's Theorem 3.1** (original form, with the discriminant as witness).
Derived from `brown_generalized` using `P = f.discr`, via Fact A
(`Brown.discr_mem_span`: `C (disc f) ∈ ⟨f, f'⟩`) and Brown's Lemma 8.1
(`Brown.discr_reverse`: `disc (reverse f) = disc f`). -/
theorem brown_original
    (k : Nat)
    (f : PolyR k)
    (pos_deg : 0 < f.natDegree)
    (discr_ne_zero : f.discr ≠ 0)
    (S : Set (Fin k → ℝ))
    (hS : IsAnalyticSubmanifold S)
    (hS_conn : IsConnected S)
    (h_ord : OrderInvariantMv f.discr S)
    (h_sgn : sgn_inv k S f.leadingCoeff)
    (hspec_ne : ∀ a ∈ S, specialize f a ≠ 0)
    : DegreeInvariant f S := by
  classical
  have hn_unit : ∀ m : ℕ, m ≠ 0 → IsUnit ((m : MvPolynomial (Fin k) ℝ)) := by
    intro m hm
    rw [← map_natCast (MvPolynomial.C : ℝ →+* MvPolynomial (Fin k) ℝ) m]
    exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hm))
  -- a derivative-degree helper for the `natDegree = 2` corner case
  have hderiv_le_one : ∀ p : PolyR k, p.natDegree ≤ 1 → Polynomial.derivative p
      = Polynomial.C (p.coeff 1) := by
    intro p hp
    ext m
    rw [Polynomial.coeff_derivative, Polynomial.coeff_C]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rcases Nat.lt_or_ge f.natDegree 2 with hn1 | hn2
  · -- `natDegree f = 1`: direct dichotomy on the sign of `lc f`
    have hn1' : f.natDegree = 1 := by omega
    obtain ⟨q₀, hq₀⟩ := hS_conn.nonempty
    have hlc_eq : f.leadingCoeff = f.coeff 1 := by rw [← Polynomial.coeff_natDegree, hn1']
    by_cases hlc0 : evalBase q₀ f.leadingCoeff = 0
    · have h_lc : ∀ q ∈ S, evalBase q f.leadingCoeff = 0 := fun q hq =>
        sgn_eq_zero_iff.mp ((h_sgn q hq q₀ hq₀).trans (sgn_eq_zero_iff.mpr hlc0))
      have hdeg0 : ∀ x ∈ S, (specialize f x).natDegree = 0 := by
        intro x hx
        apply Nat.le_zero.mp
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        show (f.map (evalBase x)).coeff m = 0
        rw [Polynomial.coeff_map]
        by_cases hm1 : m = 1
        · rw [hm1, ← hlc_eq]; exact h_lc x hx
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
      intro a ha b hb
      rw [hdeg0 a ha, hdeg0 b hb]
    · have h_lc_ne : ∀ q ∈ S, evalBase q f.leadingCoeff ≠ 0 := fun q hq hq0 =>
        hlc0 (sgn_eq_zero_iff.mp ((h_sgn q₀ hq₀ q hq).trans (sgn_eq_zero_iff.mpr hq0)))
      intro a ha b hb
      show (f.map (evalBase a)).natDegree = (f.map (evalBase b)).natDegree
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne a ha),
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (h_lc_ne b hb)]
  · -- `natDegree f ≥ 2`: apply `brown_generalized` with `P = f.discr`
    have mem1 : Polynomial.C f.discr ∈
        Ideal.span ({f, f.derivative} : Set (PolyR k)) :=
      Brown.discr_mem_span f (by omega) (hn_unit _ (by omega))
    have mem2 : Polynomial.C f.discr ∈
        Ideal.span ({f.reverse, f.reverse.derivative} : Set (PolyR k)) := by
      by_cases h0 : f.coeff 0 = 0
      · -- `a₀ = 0`: factor `f = h * X`
        have hf_ne : f ≠ 0 := ne_zero_of_natDegree_gt (by omega)
        set h := f.divX with hh_def
        have hfact : f = h * X := by
          have hd := Polynomial.divX_mul_X_add f
          rw [h0, map_zero, add_zero] at hd
          rw [hh_def]; exact hd.symm
        have hh_ne : h ≠ 0 := by intro hc; apply hf_ne; rw [hfact, hc, zero_mul]
        have hh_natdeg : h.natDegree = f.natDegree - 1 := by
          have : f.natDegree = h.natDegree + 1 := by rw [hfact]; exact Polynomial.natDegree_mul_X hh_ne
          omega
        have hh_deg_pos : 0 < h.natDegree := by omega
        have hrev_eq : f.reverse = h.reverse := by rw [hfact]; exact Polynomial.reverse_mul_X h
        have hres : resultant h X h.natDegree 1 = (-1) ^ h.natDegree * h.coeff 0 := by
          have hh := resultant_X_pow_right h h.natDegree 1 le_rfl
          rw [pow_one, mul_one, pow_one] at hh
          exact hh
        have hdiscf : f.discr = h.discr * (resultant h X h.natDegree 1) ^ 2 := by
          conv_lhs => rw [hfact]
          rw [discr_mul_eq h X hh_deg_pos (by simp),
            Polynomial.discr_of_degree_eq_one Polynomial.degree_X, mul_one, Polynomial.natDegree_X]
        have hh0 : h.coeff 0 ≠ 0 := by
          intro hc; apply discr_ne_zero; rw [hdiscf, hres, hc]; ring
        rw [hrev_eq]
        by_cases hh2 : 2 ≤ h.natDegree
        · have hmemh := Brown.discr_mem_span_reverse h hh2 hh0 (hn_unit _ (by omega))
          rw [show f.discr = (resultant h X h.natDegree 1) ^ 2 * h.discr from by rw [hdiscf]; ring,
            map_mul]
          exact Ideal.mul_mem_left _ _ hmemh
        · -- `natDegree h = 1`
          have hh1 : h.natDegree = 1 := by omega
          have hdisch1 : h.discr = 1 := by
            apply Polynomial.discr_of_degree_eq_one
            rw [Polynomial.degree_eq_natDegree hh_ne, hh1]; rfl
          have hrev_deg : h.reverse.natDegree ≤ 1 := by
            rw [Polynomial.reverse_natDegree]; omega
          have hrevcoeff : h.reverse.coeff 1 = h.coeff 0 := by
            rw [show h.reverse = Polynomial.reflect h.natDegree h from rfl, Polynomial.coeff_reflect,
              hh1, Polynomial.revAt_le (le_refl 1)]
          have hderiv : Polynomial.derivative h.reverse = Polynomial.C (h.coeff 0) := by
            rw [hderiv_le_one h.reverse hrev_deg, hrevcoeff]
          have hdiscval : f.discr = h.coeff 0 * h.coeff 0 := by
            rw [hdiscf, hres, hh1, hdisch1]; ring
          rw [hdiscval, map_mul]
          nth_rewrite 2 [← hderiv]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      · -- `a₀ ≠ 0`
        exact Brown.discr_mem_span_reverse f (by omega) h0 (hn_unit _ (by omega))
    exact brown_generalized k f f.discr discr_ne_zero mem1 mem2 pos_deg S hS hS_conn h_ord
      h_sgn hspec_ne

#print axioms brown_original
