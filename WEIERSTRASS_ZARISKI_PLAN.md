# Plan: Proving `analytic_pseudopoly_delineable` via Weierstrass → Zariski

This is the faithful (McCallum / Zariski-1965) route to discharge the **sole remaining axiom**.
It is honest about scope: this is a multi-component analytic-geometry formalization, with two
genuinely deep ingredients absent from Mathlib (convergent Weierstrass preparation, and Zariski
equisingularity). Each phase below lists concrete Lean tasks, target signatures, Mathlib
dependencies (with status), what we can REUSE, and a difficulty estimate.

---

## 0. The target

`analytic_pseudopoly_delineable` (Lifting.lean), full-base form:

- **Given**: an analytic family `g : (ℝˢ × ℝᵉ) → ℝ[t]` (coeffs analytic at `0`, section
  degree `m₀ = (g 0).natDegree > 0`, degree constant along the section); a witness
  `P : ℝˢ × ℝᵉ → ℝ` with `order ℝ P 0 ≠ ⊤`, `C(P w) ∈ ⟨g w, g' w⟩` near `0`, and
  `order ℝ P (·,0)` constant along the section.
- **Conclude**: section delineability — a nbhd `V ∋ 0` in `ℝˢ`, finitely many analytic
  `η_i : ℝˢ → ℝ`, ordered, with constant positive multiplicities, exhausting the roots of
  `g(y, 0)` for `y ∈ V`.

The transverse factor `ℝᵉ` exists ONLY so the witness order is the **ambient** (finite) order;
the conclusion is over the section. This is what makes the `disc|_section ≡ 0` case reachable.

## The mathematical proof (what we are formalizing)

1. The real roots `β₁ < ⋯ < β_k` of `g(0,0) ∈ ℝ[t]` are finite. Work **locally near each `β_j`**.
2. **Complexify** `g, P` to holomorphic data on a polydisc `Δ ⊆ ℂˢ⁺ᵉ`.
3. **Weierstrass preparation** at `(0, β_j)`: `g_ℂ = u_j · h_j` with `u_j` a unit and `h_j` a
   Weierstrass polynomial (monic in `t`, degree `m_j = mult of β_j`, coeffs holomorphic, → 0 at 0).
   Roots of `g_ℂ` near `β_j` = roots of `h_j`.
4. **Discriminant order**: from `P ∈ ⟨g,g'⟩` finite & section-constant order, deduce (norm identity
   `P^m = ±disc(h_j)·Q` + order additivity/bridge) that `disc(h_j)` has constant order along the
   section `T = ℂˢ × {0}`.
5. **Zariski**: a Weierstrass polynomial whose discriminant has constant order along `T` has
   holomorphic root sections over `T` with constant multiplicities.
6. **Schwarz reflection**: the root sections real on `T ∩ ℝˢ` restrict to real-analytic functions.
7. **Assemble**: collect/​order the real root functions across all `β_j`, with multiplicities.

---

## PHASE A — Reductions & localization  *(feasible; reuses existing infra)*

### A1. Separable subcase (removes the easy case)
If `disc(g(0,0)) ≠ 0` then `g(0,0)` is squarefree ⇒ all roots simple ⇒ `ift_local_root_section`
at each root gives the analytic sections directly. **Reuse** `separable_locally_delineable`,
`ift_local_root_section`. Adapt the section-only conclusion shape.
- Target: `lemma delineable_of_separable_origin (...) : <axiom conclusion>` under
  `(g 0).discr ≠ 0` (equivalently `IsCoprime (g 0) (g 0).derivative`).
- **Mathlib**: `Polynomial.discr` ✅, coprime/squarefree ✅. **Difficulty: low-moderate.**
- Effect: the remaining phases only need the case `disc(g(0,0)) = 0`.

### A2. Localization at a real root
Near each real root `β_j`, restrict attention to a `t`-interval `(β_j − δ, β_j + δ)` containing no
other root of `g(0,0)`. Produces, per root, a "single-cluster" problem.
- Target: `lemma roots_localize (...)` packaging the per-root neighborhoods + that they exhaust the
  real roots and stay separated. **Reuse** continuity of roots away from collisions.
- **Mathlib**: root-count locally constant under perturbation is ABSENT — must prove via
  continuity of `g(y,0).eval` + sign changes / argument principle. **Difficulty: moderate.**

### A3. Complexify the local data
`g → g_ℂ` (**reuse** `complexify_pseudopoly`), `P → P_ℂ` (**reuse** `analyticAt_complexify`),
order transfer (**reuse** `analyticAt_complexify` order-eq, `complexify_order_invariant`).
- **Obstacle (known)**: the abstract `hP_elim` membership is *pointwise* (witnesses `a(w),b(w)`
  not analytic), so it does NOT complexify directly. Resolution: we do not complexify `hP_elim`
  itself; instead we re-derive the membership for the **monic** Weierstrass polynomial `h_j` inside
  Phase D, where the relevant ring is the analytic germ ring (Phase B) and `disc`/`res` are the
  controlled objects. (The witness's role is only to force `disc` order; see D.)
- **Difficulty: moderate** (modulo Phase B for the ring).

---

## PHASE B — Analytic local ring infrastructure  *(FOUNDATIONAL; new; large)*

We need a `CommRing` of convergent power series / holomorphic germs to host Weierstrass output and
the norm identity. This is the substrate the whole route runs on. Mathlib has **formal**
`MvPowerSeries` but no convergent subring and no germ ring.

### B1. The ring `𝒪ₙ` of holomorphic germs at `0 ∈ ℂⁿ`
Define `𝒪ₙ := convergent multivariate power series` (formal series with positive polyradius), as a
subring of `MvPowerSeries (Fin n) ℂ`, OR as germs of `AnalyticAt ℂ` functions at `0`.
- Target: `def HolGerm (n) : Type` with `CommRing`, `IsLocalRing` (units = nonzero constant term),
  and a ring map to `AnalyticAt ℂ ·` representatives.
- **Mathlib**: `MvPowerSeries` ring ✅; `IsLocalRing (MvPowerSeries σ R)` ✅ (needs local coeff);
  convergent subring ABSENT; germ ring ABSENT. **Difficulty: high** (foundational).

### B2. Order/valuation on `𝒪ₙ` and the bridge to our `order`
The `t`-adic / vanishing order on `𝒪ₙ`, and the identity `order` (Order.lean) of a germ's
representative = its valuation. Needed so Phase D's order bookkeeping connects to our lemmas.
- Target: `lemma holGerm_order_eq_order (f : HolGerm n) : valuation f = order ℂ (rep f) 0`.
- **Reuse**: our `order`, `order_mul_analytic`, `polyOrder` analogues. **Difficulty: moderate-high.**

### B3. Multivariate Cauchy estimates / method of majorants
Coefficient bounds `‖a_α‖ ≤ M / r^α` on a polydisc, and a majorant-comparison convergence
criterion. This is the analytic engine for Phase C (Weierstrass convergence) and useful for B1.
- Target: `lemma cauchy_estimate (...)`, `lemma converges_of_majorant (...)`.
- **Mathlib**: multivariate Cauchy estimates / polydiscs / majorants **ABSENT**. Single-variable
  Cauchy estimates partially exist. **Difficulty: high** (Mathlib-grade SCV analysis).

---

## PHASE C — Convergent Weierstrass preparation  *(hard; Mathlib-seeded)*

### C1. Formal factorization (reuse Mathlib)
With base ring `A = MvPowerSeries (Fin (s+e−?)) ℂ` (the `z`-variables) and distinguished variable
`t`: `g_ℂ ∈ A⟦t⟧`. Establish `A` is `IsAdicComplete`/`IsPrecomplete`/`IsHausdorff` w.r.t. its
maximal ideal, then apply `PowerSeries.exists_isWeierstrassFactorization` to get a **formal**
`g_ℂ = (distinguished poly) · (unit)`.
- **Mathlib**: `PowerSeries.exists_isWeierstrassFactorization` ✅ (univariate over adic-complete
  local ring); `IsAdicComplete (MvPowerSeries …)` **ABSENT** — must prove (`MvPowerSeries`
  completeness w.r.t. its maximal ideal). **Difficulty: high** (completeness instance is real work).

### C2. Convergence of the factors
The formal distinguished polynomial's coefficients and the unit must **converge** (lie in `𝒪`), so
they are holomorphic. Prove via B3 (majorants) — the classical convergent-Weierstrass argument
(Cauchy estimates on the Weierstrass division iterates).
- Target: `theorem weierstrass_preparation_analytic (g_ℂ holomorphic, g_ℂ(0,·) order m at β) :
    ∃ (u h : 𝒪-coeff pseudopoly), h Weierstrass-monic of degree m ∧ u unit ∧ g_ℂ = u·h locally`.
- **Mathlib**: ABSENT. **Difficulty: very high** (the convergence is the crux of this phase).

---

## PHASE D — Discriminant order from the witness  *(reuses bridge/norm; over `𝒪`)*

### D1. Membership transfer to the monic `h`
In `𝒪[t]`: `g_ℂ = u·h` with `u` a unit ⇒ `⟨g_ℂ, g_ℂ'⟩ = ⟨h, h'⟩` (since `g_ℂ' = u'h + uh'` and `u`
unit). Push the witness into `⟨h, h'⟩`. NOTE: this is where the germ ring is essential (`u` is a unit
only there) — it resolves the A3 membership obstacle.
- Target: `lemma elim_transfer_weierstrass (...)`. **Reuse** ideal-span manipulation.
  **Difficulty: moderate** (given Phase B).

### D2. Norm identity over `𝒪`
`norm_identity_elim` is stated for any `CommRing` ⇒ apply with `R = 𝒪`, `h` monic:
`P^{m} = ± disc(h) · Q` in `𝒪`. **REUSE `norm_identity_elim` directly** (already proven, generic).
- **Difficulty: low** (direct reuse) — *this is where our proven norm lemma lands on the path.*

### D3. Analytic order bridge ⇒ `disc(h)` constant order
From `order(P)` constant along the section and `P^m = ±disc(h)·Q`, conclude `order(disc(h))`
constant along the section. **Reuse the IDEA of** `order_invariant_factor_of_mul`, but adapt it
from `MvPolynomial` to **holomorphic functions / `𝒪`** (USC of `order ℂ` + `order_mul_analytic` +
connectedness). The current bridge is `polyOrder`-specific; needs an analytic restatement.
- Target: `lemma order_invariant_factor_of_mul_analytic (...)`. **Reuse**: `order_mul_analytic`,
  the USC argument structure (`isClosed_polyOrder_ge` → analytic analogue). **Difficulty: moderate.**

---

## PHASE E — Zariski root sections  *(DEEPEST; new; research-scale)*

### E1. Statement
`theorem zariski_root_sections (h : 𝒪[t] Weierstrass-monic, degree m) (T = section)
    (hdisc : order(disc h) constant along T near 0) :
    ∃ holomorphic ψ_1,…,ψ_r : T → ℂ (over a sub-polydisc), distinct, with constant multiplicities
      summing to m, exhausting the roots of h over T.`

### E2. Proof (the hard kernel)
This is Zariski's equisingularity for a 1-parameter-family-of-roots with constant discriminant
order. Candidate strategies, all substantial:
- **Newton–Puiseux**: the roots are Puiseux series in the section parameters; constant disc order
  ⇒ no monodromy along `T` ⇒ the Puiseux series are honest (integral) holomorphic. Needs a
  Newton–Puiseux theory in Lean (**ABSENT** in Mathlib). **Difficulty: very high.**
- **Discriminant cover / monodromy**: roots = branched cover of the base, branched on `{disc=0}`;
  constant order along `T` controls the branching. Needs covering-space/monodromy analytic theory.
- **Inductive on degree via the derivative `h'`**: relate root structure of `h` and `h'`; needs the
  constant-multiplicity to descend. Risk: this is the failed "elementary" idea unless powered by a
  genuine equisingularity invariant.
- **Mathlib**: Zariski, Puiseux, root-continuity, analytic root functions — ALL **ABSENT**.
  **Difficulty: very high — this is the single hardest theorem of the whole route.**

> Honest note: E is where the bulk of the research-level difficulty concentrates. It may be worth a
> *standalone* formalization effort (and possibly upstreaming to Mathlib).

---

## PHASE F — Real recovery & assembly  *(feasible; reuses Schwarz/IFT)*

### F1. Real sections via Schwarz
The `ψ_i` real-valued on `T ∩ ℝˢ` restrict to real-analytic `η_i`. **REUSE `real_restriction_analytic`**
(already proven) for `η_i := Re ∘ ψ_i ∘ realEmbedding`.
- Need: the `ψ_i` corresponding to **real** roots of `g(y,0)` are exactly the real-valued ones
  (real polynomial ⇒ real roots / conjugate pairs); identify them. **Difficulty: moderate.**

### F2. Order, multiplicity, exhaustiveness
Order the real `η_i` by value (they don't collide ⇒ strict order persists). Multiplicities are the
`h`-multiplicities (constant from E). Real-root multiplicity in `g(y,0)` = complex multiplicity.
- **Reuse**: `rootMultiplicity` API. **Difficulty: moderate.**

### F3. Discharge the axiom
Assemble `V, η, mult` and prove the five conjuncts of the axiom conclusion. Replace
`axiom analytic_pseudopoly_delineable` with `theorem`. Re-run `#print axioms
mccallum_3_2_3_generalized` → expect only standard axioms (+ any genuinely-irreducible analytic
axioms we consciously keep, e.g. if Zariski is upstreamed vs. kept as a lemma).
- **Difficulty: moderate** (plumbing), **gated entirely by Phases B/C/E.**

---

## Dependency graph & sequencing

```
A1 (separable) ─────────────────────────────► narrows scope (do FIRST, lands progress)
A2 (localize) ─► A3 (complexify) ─► D1
B1 (germ ring) ─► B2 (order) ─► D3
            └─► B3 (Cauchy/majorant) ─► C2
C1 (formal Weierstrass: needs MvPowerSeries adic-complete instance) ─► C2 (convergence)
                                   C2 ─► D1 ─► D2 (REUSE norm_identity_elim) ─► D3
                                                                   D3 ─► E1 ─► E2 (Zariski)
                                                                              E2 ─► F1 (REUSE Schwarz) ─► F2 ─► F3
```

## Where our proven work lands on the critical path
- `norm_identity_elim` → **D2** (direct reuse).
- `order_invariant_factor_of_mul` (idea) → **D3** (adapt to analytic).
- `complexify_pseudopoly`, `analyticAt_complexify`, `complexify_order_invariant` → **A3**.
- `real_restriction_analytic` → **F1** (direct reuse).
- `ift_local_root_section`, `separable_locally_delineable` → **A1**.
- `order` API, `order_mul_analytic` → **B2/D3**.

## Difficulty / risk summary

| Phase | New? | Difficulty | Main risk |
|---|---|---|---|
| A reductions/localize | partly | low–moderate | root-count continuity (A2) |
| B germ ring + Cauchy/majorant | yes | **high** | foundational SCV analysis, none in Mathlib |
| C convergent Weierstrass | yes | **very high** | `MvPowerSeries` completeness instance; convergence proof |
| D disc order | reuse | moderate | analytic bridge restatement |
| E **Zariski** | yes | **very high** | the genuine deep kernel; no Mathlib scaffolding |
| F real recovery/assembly | reuse | moderate | identifying real sections |

**Overall**: a multi-person-year, Mathlib-contribution-scale effort. The two deep mountains are
**C (convergent Weierstrass)** and **E (Zariski)**; **B** is the foundational valley both require.

## Recommended first milestones (highest value / lowest risk first)
1. **A1 separable subcase** — narrows the axiom to `disc(g(0,0)) = 0`; concrete, reuses IFT.
2. **D2 wiring** — show `norm_identity_elim` + a stub Weierstrass interface yields `disc` order
   control; validates that our proven lemmas slot in (de-risks D before B/C exist).
3. **B1/B2 germ ring** — the substrate; unblocks C and D.
4. Then the two mountains **C** and **E**, ideally as standalone (upstreamable) developments.
