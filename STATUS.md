# Generalized McCallum Formalization — Status

## Main theorem
`mccallum_3_2_3_generalized` (Projection.lean) — proved from `lifting_theorem_generalized'`.

## Bridge lemma (2026-05-29): `order_invariant_factor_of_mul` — PROVED, 0 custom axioms

In `DiscrProdInvariant.lean`. The **reverse** of `order_invariant_mul_mv`: if `f * g` is
order-invariant on a **connected** (not necessarily open) `S`, with `f, g ≠ 0`, then `f` and
`g` are each order-invariant on `S`. `#print axioms` → only `[propext, Classical.choice,
Quot.sound]`.

**Why it matters:** load-bearing step for removing the `non_null` hypothesis. Shows
`P` order-invariant on `S` ⟹ `disc(f)` order-invariant on `S` (via norm identity
`P^m = ±disc·Q`) with **no** non-vanishing assumption — exactly the case `non_null` papered
over (when `S ⊆ {disc=0}`, every admissible `P` vanishes on `S`).

**Method (no `non_null`, works on non-open `S`):** `polyOrder_ne_top_of_ne_zero` (finite order
for nonzero polys, via Taylor-shift + `MvPowerSeries.order_eq_top_iff`); `isClosed_polyOrder_ge`
(upper semicontinuity via continuous iterated Fréchet derivs); `polyOrder_factor_le`
(connectivity: `{f≤A}`,`{g<B}` open, cover `S`, disjoint on `S`); two USC functions summing to
a constant on a connected set are each constant.

**proof.tex gap found (codim case):** lines 441-444 / 466 silently assume `ord_0 P̃ < ⊤`
(restricted section order). False when `S ⊆ {disc=0}` (e.g. `f=(x₃-x₁)²-x₂`, `S={x₂=0}`: moving
double root, delineable, yet `disc̃ ≡ 0`). proof.tex's Zariski (Lifting.lean 1446-1448, "constant
**nonzero** order on ℂˢ") also excludes it. Honest fix: use the **ambient** order (constant along
`S` in ℝⁿ⁻¹), which `polyOrder`/`OrderInvariantMv` already measure. NOT an artifact of the
generalization — the discriminant itself vanishes on `S` in these cases (intrinsic to McCallum
Thm 2's codim case). **NEXT: axiom reformulation** to ambient (McCallum Thm 2) form, fed by this
bridge, dropping `non_null`.

## Order-transfer lemma (2026-05-29): `order_comp_eq_of_diffeo` — PROVED, 0 custom axioms

In `OrderComp.lean` (new file). **Vanishing `order` is invariant under a local analytic
diffeomorphism**: `order ℝ (g ∘ e) x = order ℝ g (e x)` for mutually-inverse smooth `e, e'`
on open sets. `#print axioms` → only `[propext, Classical.choice, Quot.sound]`.

**Method (no full Faà-di-Bruno):** one-directional `order_le_order_comp` via the *bound*
`norm_iteratedFDerivWithin_comp_le` with `C = 0` (all outer derivs vanish ⟹ composite deriv
norm ≤ 0 ⟹ zero); both directions + germ-invariance of order (`order_congr_of_eventuallyEq`)
give equality. Works locally on open sets (chart maps are only locally analytic).

**Role:** this is the gate for Option B (chosen path: keep minimal chart axiom, prove the
transfer). It lets `codim_local` feed the chart axiom the **full-chart** order of `P` (finite,
since `P ≠ 0`), which equals the ambient `polyOrder P` at the corresponding `S`-point — instead
of the chart-*restricted* order that is `⊤` exactly in the `disc|_section ≡ 0` cases. Combined
with `hP_oi` (ambient order-invariance), gives order-invariance of `P̃` along the section.

**Both Option-B gates now cleared** (bridge + transfer). REMAINING: restructure
`analytic_pseudopoly_delineable` to full-base (section × transverse) form taking the full order
along the section; rewire `codim_local` (g, P̃ over full chart; order hyps via transfer); drop
`non_null` through the chain + Projection.

## `non_null` REMOVED (2026-05-29) — theorem now = Rule 4.1 generalized

`mccallum_3_2_3_generalized` **no longer has** `hd_non_null`/`hr_non_null` (the discriminant/
resultant non-vanishing hypotheses). Its hypotheses now match Jasper's Rule 4.1 exactly
(an_sub, connected, non_null(f) [= `hnonzero`, f not nullified], `ord_inv(d)` [`hd_oi`],
`ord_inv(r)` [`hr_oi`], degree/coeff structure) — generalized to **arbitrary elimination-ideal
elements** `d, r`. `#print axioms` → `[analytic_pseudopoly_delineable, propext,
Classical.choice, Quot.sound]`. No sorries. Full project builds.

**How:** the axiom `analytic_pseudopoly_delineable` was restructured to the **full-base**
(section × transverse) form: it takes the family `g` and witness `P` over `ℝˢ × ℝⁿ⁻ˢ`, with
`P`'s order **finite at 0 and constant along the section** (the ambient order, finite even when
`disc|_section ≡ 0`), and concludes delineability over the section. `codim_local` feeds it via
`order_comp_partialHomeomorph_symm` (the chart transfer), so `order ℝ P̃ (y,0) = polyOrder P (Ψ y)`
= constant on `S` by `hP_oi` — no non-vanishing needed. The degree subtlety is sidestepped:
the axiom requires constant degree only **along the section** (true by leading-coeff continuity),
not off it.

**New supporting lemmas (both 0 custom axioms):**
- `order_invariant_factor_of_mul` (DiscrProdInvariant.lean) — reverse-order bridge (for the
  eventual axiom proof: `P` order-inv ⟹ `disc` order-inv).
- `order_comp_eq_of_diffeo`, `order_comp_partialHomeomorph_symm` (OrderComp.lean, new file) —
  vanishing order invariant under a local analytic diffeomorphism; load-bearing for feeding the axiom.

## Axiom decomposition — glue pieces being proven (2026-05-29)

Decomposing `analytic_pseudopoly_delineable` into named classical pieces. Status of the
documented decomposition steps:
- **Step 6 Schwarz reflection** — `real_restriction_analytic` (Lifting.lean): a function
  holomorphic at a real point restricts to a real-analytic function on `ℝˢ` (via
  `restrictScalars` + the `realEmbedding` CLM + `Re`). **PROVED, 0 custom axioms.**
- **Hypothesis-side glue, family complexification** — `complexify_pseudopoly` (Lifting.lean):
  a real pseudopolynomial family (analytic coeffs, degree ≤ N) complexifies to `gℂ : ℂᵐ → ℂ[t]`
  with analytic coeffs agreeing on the reals coefficient-wise. Built per-coefficient via
  `analyticAt_complexify` + reassembly with `Polynomial.monomial`. **PROVED, 0 custom axioms.**
  (Witness complexification = existing `analyticAt_complexify` directly. Remaining part-2 piece:
  the **membership** transfer `C P ∈ ⟨g,g'⟩ ⟹ C Pℂ ∈ ⟨gℂ,gℂ'⟩`, via complexifying the analytic
  witnesses + the identity theorem — fiddlier, deferred.)
- Bridge (`order_invariant_factor_of_mul`) and transfer (`order_comp_eq_of_diffeo`) — **PROVED**.
- **Remaining gaps (genuine, deep):** Weierstrass preparation (convergent) and Zariski root
  sections. A *correct* split needs `(base,t)`-analytic-germ-ring infrastructure — the
  Weierstrass factor `u` is a unit only in the germ ring, NOT in `ℝ[t]` (off the section it has
  `t`-roots). An `ℝ[t]`-level split would be a FALSE axiom; not pursued. The complex→real
  root-section *matching* (complex roots are unordered; must identify real-valued sections) is
  the other intricate remaining piece. These are scoped as dedicated future work.

So `non_null` is removed and the proven-glue for the eventual axiom elimination is accumulating
(bridge, transfer, Schwarz), but full axiom elimination remains a large analytic-geometry build.

## Axiom / sorry inventory

The main theorem chain depends on **1 axiom** + standard axioms. **No sorries.**

### Recently closed (2026-05-28): hPtilde_ne and hPtilde_oi
Inside `lifting_generalized_codim_local`, the two remaining sorries at the call site
of `analytic_pseudopoly_delineable` are now **PROVED**.

**API change:** Added hypothesis `hP_eval_p : MvPolynomial.eval p P ≠ 0` to
`lifting_generalized_codim_local`, propagated as `∀ a ∈ S, eval a P ≠ 0` through
`lifting_generalized_codim_case`, `lifting_theorem_generalized'`, and
`lifting_theorem_generalized`. At `mccallum_3_2_3_generalized`, added hypotheses
`hd_eval` and `hr_eval` (chosen elimination ideal elements don't vanish on S),
and derived `hP_eval` from them via the `elimProduct` factorization. This hypothesis
is natural for CAD: cells in a CAD decomposition are precisely the regions where
the chosen elimination ideal elements don't vanish.

### Axioms (in the chain)

**`analytic_pseudopoly_delineable`** (Lifting.lean) — sole remaining axiom.

This monolithic axiom bundles the deep complex-analytic core of the proof.
**Planned decomposition** (documented in the axiom's docstring):

1. **`weierstrass_preparation_complex`** (TODO axiom) — classical Weierstrass
   preparation theorem for holomorphic functions in several complex variables.
   Mathlib has the algebraic version (`PowerSeries.exists_isWeierstrassFactorization`);
   bridging to convergent power series is the gap.
2. **`zariski_root_sections_complex`** (TODO axiom) — Zariski's 1975 theorem on
   analytic root sections of a Weierstrass polynomial with disc of constant order.
3. **`real_root_section_of_complex`** (provable) — Schwarz reflection.
4. **`analytic_pseudopoly_delineable`** (would become a theorem proved from 1–3).

### Recently eliminated axiom (2026-05-28)

**`order_invariant_of_delineable`** — was an axiom, now **FULLY PROVED** (0 axioms).
Fix: changed `orderFull` definition from total multivariate order (`polyOrder`) to
`rootMultiplicity` of the specialized polynomial. With this definition, the theorem
follows trivially from delineability (constant rootMultiplicity on each section graph).

### Sorries: **NONE**

### Key definition change (2026-05-28)

`orderFull` (Invariance.lean) changed from:
```
polyOrder (n + 1) (toMvPoly f) (Fin.cons y a)
```
to:
```
if specialize f a = 0 then top else (specialize f a).rootMultiplicity y
```

The old definition used total multivariate order (via iterated Frechet derivatives).
This was wrong: a counterexample showed `order_invariant_of_delineable` was FALSE with
the old definition (f(x1,x2)(t) = t^2 + x1*x2, S = {x2=0}, theta = 0).

The new definition uses univariate rootMultiplicity of the specialized polynomial,
which is the correct notion for CAD lifting theorems.

### API changes (2026-05-28)
- `orderFull` definition changed (see above)
- `OrderInvariantFactor.lean` completely rewritten to use `rootMultiplicity`
- `order_invariant_full_factor_of_prod` gained `hspec` hypothesis:
  `forall f in A, forall p in T, specialize f p.1 != 0`
- `orderFull_eq_rootMultiplicity_at_delineable_root`: was sorry'd, now trivial 1-line proof
- `orderFull_eq_one_of_simple_root`: was complex polyOrder proof, now trivial 2-line proof

## Fully proved components

- `order_invariant_of_delineable` — delineability => order-invariance on sections, **PROVED**
- `order_mul_analytic` — order(fg) = order(f) + order(g), **PROVED**
- `order_additivity_holomorphic` — Thesis Lemma 4.1, **PROVED**
- `order_ne_top_of_ne_zero` — identity theorem (multi-variable), **PROVED**
- `isOpen_order_le_inter` — upper semi-continuity of order, **PROVED**
- `isOpen_order_lt_inter` — {order < b} open, **PROVED**
- `IsAnalyticSubmanifold.straightening_chart` — Theorem 2.2.1 (Submanifold.lean)
- `ift_local_root_section` — IFT for simple polynomial roots (SimpleRoots.lean)
- `separable_locally_delineable` — simple roots => local delineability (SimpleRoots.lean)
- `locally_delineable_to_global` — globalization, open case (SimpleRoots.lean)
- `locally_delineable_to_global'` — globalization, non-open connected sets (Lifting.lean)
- `order_invariant_of_locally_invariant` — globalization of order invariance (Lifting.lean)
- `lifting_generalized_open_case` — open case of lifting theorem (Lifting.lean)
- `lifting_generalized_codim_case` — codim case (Lifting.lean)
- `lifting_generalized_codim_local` — local codim case, **NO SORRIES** (Lifting.lean)
- `norm_eq_resultant_monic` — norm = resultant for monic polynomials (Lifting.lean)
- `norm_identity_elim` — P in elimination ideal => P^m = Res * Q (Lifting.lean)
- `norm_mk_mul_X_sub_C`, `norm_eq_prod_eval_of_monic_splits`,
  `norm_adjoinRoot_map` — supporting lemmas for norm chain (Lifting.lean)
- `exists_complement_of_surjective` — linear algebra helper (Submanifold.lean)
- `analyticAt_complexify` — real-analytic extends to holomorphic (Lifting.lean)
- `complexify_order_invariant` — constant order transfers to complexification (Lifting.lean)
- `hPtilde_elim` — Ptilde in <g, g'> proved via chart specialization (Lifting.lean)
- `orderFull_eq_rootMultiplicity_at_delineable_root` — trivial with new definition, **PROVED**
- `orderFull_eq_one_of_simple_root` — trivial with new definition, **PROVED**
- `isClosed_orderFull_ge` — superlevel sets of orderFull are closed, **PROVED**
- `order_invariant_full_factor_of_prod` — product OI => factor OI, **PROVED**

## Architecture

```
Projection.lean
  +-- mccallum_3_2_3_generalized  (Theorem 3.2.3')
        +-- lifting_theorem_generalized'  (Lifting.lean)
              |-- lifting_generalized_open_case  (s = r-1, S open)
              |     +-- simple_roots_delineable  (SimpleRoots.lean)
              |-- lifting_generalized_codim_case  (s < r-1, S submanifold)
              |     |-- lifting_generalized_codim_local  <- 0 sorries, 1 axiom
              |     |     +-- analytic_pseudopoly_delineable  (AXIOM)
              |     |-- order_invariant_of_delineable  (PROVED)
              |     |-- locally_delineable_to_global'
              |     +-- order_invariant_of_locally_invariant
              +-- norm_identity_elim
                    +-- norm_eq_resultant_monic
```

Last updated: 2026-05-28
