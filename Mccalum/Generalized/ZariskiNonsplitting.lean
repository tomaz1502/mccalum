import Mccalum.Generalized.ZariskiFactorization
import Mccalum.Generalized.ZariskiCodim1
import Mccalum.Generalized.A5Coincidence
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic

/-!
# Nonsplitting from factorization — wiring A2 + (A4·A5) through the assembly

This file connects the codim-1 nonsplitting pieces and turns the former axiom `zariski_nonsplitting`
into a **theorem**, resting on two transparent, separately-attackable analytic axioms:

* **A2** `weierstrass_irreducible_factorization` (`ZariskiFactorization`) — the irreducible
  factorization `h = ∏ⱼ hⱼ`.
* **A4·A5** `irreducible_factors_common_section_root` (here) — the *monodromy + resultant* kernel: the
  irreducible factors all have one **common single root** over the section. (A4: each irreducible
  factor is nonsplitting over the section, the branched-covering/transitive-monodromy argument; A5:
  distinct factors coincide there, the resultant / zero-system-continuity argument. Bundled for now;
  A5 is the separately-provable half.)

The **assembly** `nonsplitting_of_common_single_root` (`ZariskiCodim1`, proved) then yields
`zariski_nonsplitting`. Net effect on the development: the single opaque "monodromy kernel" axiom is
replaced by the precise pair {factorization, irreducible-nonsplitting+coincidence} of the thesis proof
of Theorem 4.2.2, with the algebraic glue proved. Both axioms hold in general codimension (the
codim≥2 → codim-1 blow-up of Theorem 4.1.1 Case II is absorbed into the eventual proof of A4·A5, so no
separate blow-up axiom is needed at this level).
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **(A4-core) Single irreducible Weierstrass family is nonsplitting over the section — TEMPORARY
AXIOM.**

The genuine per-factor monodromy kernel, stated for *one* irreducible Weierstrass family `H` of degree
`d ≥ 1`, taking `H`'s **own** discriminant hypotheses (nonvanishing order + order-invariance along the
section): then `H` has, for `y` near `0`, a *single* distinct root `α(y)` over the section. (Branched
covering of the roots over `{disc(H) ≠ 0}` + transitive monodromy on the roots of an irreducible
family + a homotopy-deformation contradiction — Theorem 4.2.2.)

This is the *only* remaining axiom of the nonsplitting half, scoped as the M2–M5 sub-project
(complex `analytic_root_section`, the covering map `π`, transitive monodromy Lemma 4.2.5, and the
homotopy-deformation contradiction). The full multi-factor statement
`irreducible_factor_section_single_root` is *derived* from this by the discriminant-descent
`factor_disc_order_inv` (each factor inherits a constant-order discriminant from `disc(h)`), so no
discriminant reasoning is left in the axiom. -/
axiom irreducible_section_single_root {s e : ℕ}
    (H : CParam s e → Polynomial ℂ) (d : ℕ) (hd : 1 ≤ d)
    (hH_fam : IsWeierstrassFamily H d) (hH_irr : WeierstrassIrreducible H d)
    (hHdisc_ne : order ℂ (fun w => (H w).discr) (0 : CParam s e) ≠ ⊤)
    (hHdisc_oi : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (fun w => (H w).discr) ((y, 0) : CParam s e)
        = order ℂ (fun w => (H w).discr) ((0, 0) : CParam s e)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (H ((y, 0) : CParam s e)).IsRoot β ↔ β = α

/-- **(A4) Each irreducible factor is nonsplitting over the section — THEOREM.**

Every irreducible Weierstrass factor `facⱼ` of the factorization `h = ∏ⱼ facⱼ` has, for `y` near `0`,
a *single* distinct root over the section. Derived from the single-family core
`irreducible_section_single_root`: the per-factor discriminant hypotheses are supplied by the
discriminant-descent `factor_disc_order_inv` (for `k ≥ 2`, `disc(facⱼ)` divides `disc(h)` up to a
nonvanishing analytic factor `res²·disc(∏)`, so its order is constant along the section), and for the
trivial factorization `k = 1` the single factor is `h` itself (germ-equal), inheriting `hdisc_ne`,
`hdisc` directly. The roots of *different* factors are reconciled separately by A5. -/
theorem irreducible_factor_section_single_root {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hk : 0 < k) (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_irr : ∀ j, WeierstrassIrreducible (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j : Fin k, fac j w) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ j : Fin k, ∃ α : ℂ, ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β ↔ β = α := by
  rw [Filter.eventually_all]
  intro j
  -- Per-factor discriminant hypotheses: order-nonvanishing and order-invariance along the section.
  have hDj : order ℂ (fun w => (fac j w).discr) (0 : CParam s e) ≠ ⊤ ∧
      ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
          = order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e) := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · -- `k = 1`: the single factor is `h` itself (germ-equal), so disc germs coincide.
      have hk1' : k = 1 := by omega
      subst hk1'
      have hj0 : j = 0 := Subsingleton.elim j 0
      have hfe : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = fac j w := by
        filter_upwards [hfac_eq] with w hw
        rw [hw, hj0, Fin.prod_univ_one]
      -- base-point order equality `disc(facⱼ) ~ disc(h)` at `(0,0)`
      have hgerm_base : order ℂ (fun w => (fac j w).discr) ((0, 0) : CParam s e)
          = order ℂ (weierstrassDiscFn m a) ((0, 0) : CParam s e) :=
        order_congr_of_eventuallyEq' (by
          filter_upwards [hfe] with w hw
          show (fac j w).discr = (weierstrassPoly m a w).discr
          rw [hw])
      refine ⟨?_, ?_⟩
      · rw [show ((0 : CParam s e)) = ((0, 0) : CParam s e) from rfl, hgerm_base]; exact hdisc_ne
      · -- section invariance, transported through the germ equality at each `(y,0)`
        have hfe_nhds := hfe.eventually_nhds
        have hι : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
          simpa using hc.tendsto' 0 0 (by simp)
        have hsec_germ : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
            ∀ᶠ w' in 𝓝 ((y, 0) : CParam s e), weierstrassPoly m a w' = fac j w' :=
          hι.eventually hfe_nhds
        filter_upwards [hdisc, hsec_germ] with y hy_disc hy_germ
        have e1 : order ℂ (fun w => (fac j w).discr) ((y, 0) : CParam s e)
            = order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e) :=
          order_congr_of_eventuallyEq' (by
            filter_upwards [hy_germ] with w' hw'
            show (fac j w').discr = (weierstrassPoly m a w').discr
            rw [hw'])
        rw [e1, hy_disc]; exact hgerm_base.symm
    · exact factor_disc_order_inv m a hdisc_ne hdisc k deg fac hfac_fam
        (fun l => (hfac_irr l).1) hfac_eq j hk2
  exact irreducible_section_single_root (fac j) (deg j) (hfac_irr j).1 (hfac_fam j) (hfac_irr j)
    hDj.1 hDj.2

/-- **(A5) Distinct factors coincide over the section — THEOREM (resultant coincidence).**

Any two factors `facᵢ, facⱼ` of the factorization *share a root* over the section, for `y` near `0`.
Proved (no axiom) by `pair_share_root`: the discriminant `disc(h)` carries `res(facᵢ,facⱼ)²` as a
factor (`discr_mul_eq`); its order-invariance along the section descends to `res²` (the project's
`order_factor_const_of_mul_analytic`); since the base-point factors are `Xᵈ` (sharing root `0`),
constant order forces `res(facᵢ((y,0)),facⱼ((y,0))) = 0`, hence a shared root. -/
theorem irreducible_factors_section_share_root {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hk : 0 < k) (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_irr : ∀ j, WeierstrassIrreducible (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j : Fin k, fac j w) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∀ i j : Fin k, ∃ β : ℂ,
        (fac i ((y, 0) : CParam s e)).IsRoot β ∧ (fac j ((y, 0) : CParam s e)).IsRoot β := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact pair_share_root m a hdisc_ne hdisc k deg fac hfac_fam (fun l => (hfac_irr l).1) hfac_eq i j

/-- **The irreducible factors share one common single section root — THEOREM (from A4 + A5).**

Proved by combining A4 (each factor `facⱼ` has a single root `αⱼ`) with A5 (factors share roots): a
root shared between `facⱼ` and `fac₀` must equal both `αⱼ` and `α₀`, so every `αⱼ = α₀` and `α₀` is the
common single root of all factors. -/
theorem irreducible_factors_common_section_root {s e : ℕ}
    (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e))
    (k : ℕ) (deg : Fin k → ℕ) (fac : Fin k → (CParam s e → Polynomial ℂ))
    (hk : 0 < k) (hfac_fam : ∀ j, IsWeierstrassFamily (fac j) (deg j))
    (hfac_irr : ∀ j, WeierstrassIrreducible (fac j) (deg j))
    (hfac_eq : ∀ᶠ w in 𝓝 (0 : CParam s e), weierstrassPoly m a w = ∏ j : Fin k, fac j w) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ j : Fin k, ∀ β : ℂ, (fac j ((y, 0) : CParam s e)).IsRoot β ↔ β = α := by
  filter_upwards
    [irreducible_factor_section_single_root m a ha_an ha0 hdisc_ne hdisc k deg fac hk hfac_fam
      hfac_irr hfac_eq,
     irreducible_factors_section_share_root m a ha_an ha0 hdisc_ne hdisc k deg fac hk hfac_fam
      hfac_irr hfac_eq] with y h4 h5
  obtain ⟨α₀, hα₀⟩ := h4 ⟨0, hk⟩
  refine ⟨α₀, fun j => ?_⟩
  obtain ⟨αj, hαj⟩ := h4 j
  obtain ⟨γ, hγj, hγ0⟩ := h5 j ⟨0, hk⟩
  have hαj_eq : αj = α₀ := ((hαj γ).mp hγj).symm.trans ((hα₀ γ).mp hγ0)
  rw [← hαj_eq]
  exact hαj

/-- **Zariski's theorem 4.1.1 — pure nonsplitting, now a THEOREM.** Assembled from the irreducible
factorization (A2) and the common single section root of the factors (A4·A5) via the proved
`nonsplitting_of_common_single_root`. -/
theorem zariski_nonsplitting {s e : ℕ}
    (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      ∃ α : ℂ, ∀ β : ℂ, (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot β ↔ β = α := by
  -- A2: `weierstrassPoly m a` is a Weierstrass family, so it factors into irreducibles.
  have hH : IsWeierstrassFamily (weierstrassPoly m a) m :=
    weierstrassPoly_isWeierstrassFamily m a ha_an ha0
  obtain ⟨k, deg, fac, hk, _hdeg1, hfac_fam, hfac_irr, hfac_eq⟩ :=
    weierstrass_irreducible_factorization (weierstrassPoly m a) m hH hm_pos
  -- A4·A5: the factors have one common single section root.
  have hcommon := irreducible_factors_common_section_root m a ha_an ha0 hdisc_ne hdisc
    k deg fac hk hfac_fam hfac_irr hfac_eq
  -- restrict the germ factorization to the section `t ↦ (y, 0)`
  have hsec : Filter.Tendsto (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun y : Fin s → ℂ => ((y, 0) : CParam s e)) := by fun_prop
    simpa using hcont.tendsto 0
  -- assemble
  apply nonsplitting_of_common_single_root m a
  filter_upwards [hsec.eventually hfac_eq, hcommon] with y hy_eq hy_common
  obtain ⟨α, hα⟩ := hy_common
  exact ⟨k, fun j => fac j ((y, 0) : CParam s e), α, hk, hy_eq, hα⟩

/-! ### Conclusion (1): the single holomorphic root section -/

/-- The `i`-th coefficient (`i : Fin m`, so `i < m`) of the Weierstrass polynomial is `a_i(w)`: the
leading `X^m` does not contribute (degree `m > i`), and the sum picks out the single `i`-term. -/
private lemma weierstrassPoly_coeff_lt {s e : ℕ} (m : ℕ) (a : Fin m → (CParam s e → ℂ))
    (w : CParam s e) (i : Fin m) :
    (weierstrassPoly m a w).coeff (i : ℕ) = a i w := by
  rw [weierstrassPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (by have := i.isLt; omega), zero_add, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single i
      (fun b _ hb => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hb (Fin.ext h).symm),
          mul_zero])
      (fun h => absurd (Finset.mem_univ i) h),
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]

/-- A monic degree-`m` complex polynomial with a **single distinct root** `α` is `(X − α)^m`. -/
private lemma weierstrassPoly_eq_pow_of_unique_root {s e : ℕ} (m : ℕ)
    (a : Fin m → (CParam s e → ℂ)) (w : CParam s e) (α : ℂ)
    (huniq : ∀ β : ℂ, (weierstrassPoly m a w).IsRoot β ↔ β = α) :
    weierstrassPoly m a w = (X - C α) ^ m := by
  set p := weierstrassPoly m a w with hp
  have hmon : p.Monic := weierstrassPoly_monic m a w
  have hdeg : p.natDegree = m := weierstrassPoly_natDegree m a w
  have hcard : p.roots.card = p.natDegree := Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hroots : p.roots = Multiset.replicate m α := by
    rw [← hcard.trans hdeg]
    exact Multiset.eq_replicate_card.mpr fun b hb => (huniq b).mp (Polynomial.isRoot_of_mem_roots hb)
  have hrec := p.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rwa [hmon.leadingCoeff, map_one, one_mul, hroots, Multiset.map_replicate, Multiset.prod_replicate,
    eq_comm] at hrec

/-- **Zariski's theorem 4.1.1 — single holomorphic root section (conclusion (1)).**

A **theorem**: the single-branch / multiplicity packaging is proved from the pure nonsplitting kernel
`zariski_nonsplitting`. The branch is `ψ(y) = −a_{m-1}(y,0)/m` (the negated average of the `m`
coinciding roots, an analytic function of the coefficients); the unique-root and multiplicity-`m`
conclusions follow because the section polynomial is `(X − ψ(y))^m`. -/
theorem zariski_single_branch {s e : ℕ}
    (m : ℕ) (hm_pos : 0 < m)
    (a : Fin m → (CParam s e → ℂ))
    (ha_an : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∃ ψ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
        (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ y) = m) := by
  classical
  set iTop : Fin m := ⟨m - 1, by omega⟩ with hiTop
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set ψ : (Fin s → ℂ) → ℂ := fun y => -(m : ℂ)⁻¹ * a iTop (y, 0) with hψ
  have hpack : ∀ y : Fin s → ℂ, ∀ α : ℂ,
      (∀ β : ℂ, (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot β ↔ β = α) → ψ y = α := by
    intro y α huniq
    have hpow := weierstrassPoly_eq_pow_of_unique_root m a ((y, 0) : CParam s e) α huniq
    have hnc : ((X - C α : ℂ[X]) ^ m).nextCoeff = -(m : ℂ) * α := by
      rw [(monic_X_sub_C α).nextCoeff_pow, Polynomial.nextCoeff_X_sub_C, nsmul_eq_mul]
      ring
    have hai : a iTop (y, 0) = -(m : ℂ) * α := by
      rw [← weierstrassPoly_coeff_lt m a ((y, 0) : CParam s e) iTop, hpow]
      have hnd : ((X - C α : ℂ[X]) ^ m).natDegree = m := by
        rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      have heq := Polynomial.nextCoeff_of_natDegree_pos (p := (X - C α : ℂ[X]) ^ m) (by rw [hnd]; omega)
      rw [hnd] at heq
      rw [show ((iTop : ℕ)) = m - 1 from rfl, ← heq]; exact hnc
    show -(m : ℂ)⁻¹ * a iTop (y, 0) = α
    rw [hai, show -(m : ℂ)⁻¹ * (-(m : ℂ) * α) = ((m : ℂ)⁻¹ * (m : ℂ)) * α from by ring,
      inv_mul_cancel₀ hm_ne, one_mul]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · exact analyticAt_const.mul
      ((ha_an iTop).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl)
  · show -(m : ℂ)⁻¹ * a iTop ((0 : Fin s → ℂ), (0 : Fin e → ℂ)) = 0
    rw [show (((0 : Fin s → ℂ), (0 : Fin e → ℂ)) : CParam s e) = 0 from rfl, ha0 iTop, mul_zero]
  · filter_upwards [zariski_nonsplitting m hm_pos a ha_an ha0 hdisc_ne hdisc] with y hy
    obtain ⟨α, huniq⟩ := hy
    intro β
    rw [hpack y α huniq]; exact huniq β
  · filter_upwards [zariski_nonsplitting m hm_pos a ha_an ha0 hdisc_ne hdisc] with y hy
    obtain ⟨α, huniq⟩ := hy
    rw [hpack y α huniq, weierstrassPoly_eq_pow_of_unique_root m a ((y, 0) : CParam s e) α huniq,
      rootMultiplicity_X_sub_C_pow]

end
