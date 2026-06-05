# Plan: finishing Conclusion 1 (nonsplitting / `irreducible_section_single_root_deg`) via the thesis proof

**Goal.** Discharge the last axiom on which *Conclusion 1* of Zariski 4.1.1 depends,
`irreducible_section_single_root_deg` (A4-deg), by porting the thesis's own proof of
**Theorem 4.2.2** (nonsplitting) — the transitive-monodromy + homotopy-deformation argument —
rather than the alternative clopen-split shortcut.

**Why this route.** The thesis (`thesis/thesis.tex`) contains a complete, correct proof, which is a
large advantage for the formalization. Its logical core is *already formalized* (archived), and the
one piece that was missing when it was archived — the connectedness kernel of Lemma 4.2.5 — is exactly
what the Newton–Puiseux subproject (`Mccalum/Puiseux/RootCover.lean`) now proves. So the monodromy
route and the Puiseux work **converge**: the Puiseux connectedness result unblocks the monodromy proof,
and the Puiseux parametrization remains the route to *Conclusion 2* (order-invariance). Nothing is
wasted.

---

## Where this sits in the overall development

Conclusion 1's whole chain is already proved **except** `irreducible_section_single_root_deg`:

- A2 factorization `weierstrass_irreducible_factorization` — axiom (have).
- A4-deg `irreducible_section_single_root_deg` — **the target of this plan**.
- A5 `irreducible_factors_section_share_root` — **proved** (`ZariskiNonsplitting.lean`).
- packaging `zariski_single_branch` / `zariski_nonsplitting` — **proved**.

In the thesis, A4-deg *is* the per-irreducible-factor argument inside the proof of Theorem 4.2.2
(`thesis.tex:2693–2740`). Steps 10–11 of that proof (distinct-factor reconciliation by resultant, and
the `ψ` packaging) are already done in Lean. We port the one remaining block.

### Thesis geometry (decoding `thesis.tex:2680–2740`)

Base `Δ₁ ⊆ ℂⁿ⁻¹`, coordinates `(z, z_{n-1})`: `z ∈ ℂⁿ⁻²` is the **section parameter** (`= y`),
`z_{n-1}` the **single transverse coordinate**, `z_n` the **root variable** (`t`). The discriminant is in
the normal form `F = z_{n-1}^r · N` (`N` non-vanishing), so the discriminant locus is the smooth
hyperplane `H* = {z_{n-1}=0}` — this is the codim-1 equisingular structure, and it matches the kernel
base `Fin 1 → ℂ` (the transverse coordinate).

### Codimension (the `e` parameter), and Case I / Case II

`CParam s e = (Fin s → ℂ) × (Fin e → ℂ)`, section `{e-block = 0}`. Here `s = dim S` and
**`e = codim(S) = (r−1) − s`**, which is `≥ 2` whenever `s ≤ r−3`. The pipeline genuinely reaches
`e ≥ 2`. The thesis handles this exactly as a two-case split (`thesis.tex:2187–2412`):

- **Case I (`e = 1`, `s = n−2`)** = Theorem 4.2.1/4.2.2 = the **homotopy proof** (M1–M4 below). The
  discriminant is in normal form `z_{n-1}^r·N` directly.
- **Case II (`e ≥ 2`)** = reduce to Case I via a **blow-up**, which here is an *explicit quadratic
  substitution* (not scheme-theoretic):
  ```
  Q(z, z_{s+1},…,z_{n-1}) = (z, z_{s+1}·z_{n-1}, …, z_{n-2}·z_{n-1}, z_{n-1}).
  ```
  With `h'(Z,Z_n) = h(Q(Z),Z_n)`, quasi-homogeneity of the Taylor terms gives
  `disc(h') = F∘Q = Z_{n-1}^r·N(Z)`, `N(0) ≠ 0` — i.e. **the blow-up converts the codim-≥2
  discriminant into the codim-1 normal form**. Apply Case I to `h'`, then push the conclusion down:
  `ψ(z) := ψ'(z,0,…,0)` (for Conclusion 1 the pushdown is immediate, `thesis.tex:2414–2418`).

**Architectural decision:** retarget the homotopy proof (M1–M4) at **`e = 1`**, where the thesis
argument lives natively and the normal form is free, and add the blow-up as a **separate reduction
layer** (M5b) that turns the general-`e` statement into the `e = 1` one. This mirrors the thesis's
Case I / Case II structure exactly.

---

## The proof maps to these tasks

Thesis step (`thesis.tex:2693–2740`) → Lean obligation → status:

| Thesis step | Content | Status |
|---|---|---|
| factor `h = h₁⋯hₖ` | A2 | axiom (have) |
| **Lemma 4.2.5** root-exchange `Γ_{hᵢ}[α]=β` | transitive monodromy of the irreducible cover | topological half **DONE** (`transitive_monodromy_of_pathConnected`); algebraic kernel **NOW available** via `clopen_split_contradiction'` (Puiseux) |
| step 4: discs `Dⱼ` + transverse disc `D'`, `mⱼ` roots in `Dⱼ` | bivariate root continuity (Rouché) | **NEW** (M2) |
| step 7: homotopy `H(s,t)` (collapse `z→w`) | explicit deformation `Γ→Γ'` in `U` | **NEW** (M3) |
| step 8: homotopy `K(s,t)` (radial → circle) | explicit deformation `Γ'→Γ''` | **NEW** (M3) |
| step 9: confinement contradiction | lift of `Γ''` stuck in `D₁`, ends at `β∈D₂` | logical core **DONE** (`monodromy_exchange_contradiction`, `liftPath_confined`) |
| step 10: factors reconcile (resultant) | A5 | **PROVED** |
| step 11: `ψ` holomorphic | `a₁(w,0)=-mψ` | **PROVED** |

Genuinely-new work is concentrated in **M1 (path-connectedness bridge), M2 (Rouché separation),
M3 (the two explicit homotopies)**, plus **M5 (normal form + blow-up)**. The contradiction skeleton
and everything downstream already exist.

---

## Phases

### M0 — Reactivate & re-scope *(mechanical)*
- Move `archive/monodromy/Monodromy.lean` back to `Mccalum/Generalized/Monodromy.lean`, re-add its
  import to `Mccalum.lean`.
- Deduplicate `transitive_monodromy_of_pathConnected` (identical copy already lives in
  `Mccalum/Puiseux/Covering.lean`); have `Monodromy.lean` import `Mccalum.Puiseux.Covering` and drop
  the local copy.
- Confirm green + axiom-clean (`#print axioms` on `monodromy_exchange_contradiction`).
- `ComplexCovering.lean` is already in the build.

### M1 — Lemma 4.2.5 (transitive monodromy / root exchange) *(the key synergy)*
The piece the archive README lists as "not built (Bochner–Martin content)"; now suppliable.

- **M1-kernel-fix (DONE).** Discovered `clopen_split_contradiction'` was **vacuous**: it required a
  clopen of the *full branched* `rootVariety`, but over a disc the branch point `(0,0)` glues every
  colliding sheet, forcing one side of any split empty (so `1 ≤ d_A ∧ 1 ≤ d_B` is unsatisfiable, and
  the docstring's own task C4.2 was impossible). Fixed by re-parameterizing the factor/count chain
  (`factor_coeff_analyticAt`, `sheet_mem_locally_const`, `aRootCount_eventually_*`,
  `factor_coeff_extends`, `exists_factor_weierstrass`, `clopen_split_factorization`,
  `clopen_split_contradiction'`) by an **open separable base `U`**, consuming a clopen of the
  *punctured* cover via `IsClopenOverBase q U A := IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U))`
  and the helper `clopen_mem_const_over_sub`; `exists_local_root_sections` now returns `V ⊆ U`. Green,
  non-vacuous. (`Mccalum/Puiseux/RootCover.lean`.)
- **M1a (DONE).** `rootCover_preconnected` (`Mccalum/Generalized/Monodromy.lean`): for irreducible `q`,
  the cover over a punctured separable preconnected base `U ∈ 𝓝[≠]0` is `PreconnectedSpace`. Proof via
  `preconnectedSpace_iff_clopen`: a clopen split gives `A`, `Aᶜ` nonempty ⟹ (helper
  `rootCover_count_pos_freq`: count locally constant on connected `U`, positive at a witness sheet) two
  `∃ᶠ` positive counts ⟹ `clopen_split_contradiction'`. Axiom-clean.
- **M1b (DONE).** `rootCover_pathConnected`: the cover over `U` is `PathConnectedSpace`. Needed a
  general lemma `IsLocalHomeomorph.locPathConnectedSpace` (missing from Mathlib — local homeo pulls back
  local path-connectedness, proved via `LocPathConnectedSpace.of_bases` + the chart's `symm`-image),
  plus `rootCover_isCoveringMap` (from `rootProj_isCoveringMap_restrict`), `IsOpen.locPathConnectedSpace`
  for the base `↥U`, M1a for preconnectedness, and nonemptiness (`IsAlgClosed.exists_root`).
- **M1c (DONE).** `rootCover_exchange` (= Lemma 4.2.5): two sheets over the same base point are joined
  by a base loop whose lift carries one to the other — `transitive_monodromy_of_pathConnected` applied
  to the covering map with M1b's `PathConnectedSpace`. **The previously-"not built" Bochner–Martin
  content is now proved.**
- **Status: M1 COMPLETE.** All of `IsLocalHomeomorph.locPathConnectedSpace`, `rootCover_preconnected`,
  `rootCover_pathConnected`, `rootCover_isCoveringMap`, `rootCover_exchange` are green and axiom-clean
  (`Mccalum/Generalized/Monodromy.lean`).

### G — Generalize the kernel from `Fin 1 → ℂ` to a general base *(prerequisite to M2–M4)*

**Dimensional finding.** M1's Lemma 4.2.5 (`rootCover_exchange`) is over `Fin 1 → ℂ` — base dimension
1, i.e. the degenerate `s + e = 1` (`s = 0`) case, inherited from the Puiseux kernel being `Fin 1`
(`clopen_split_contradiction'`, `UnivIrreducible`; "task C4.2"). But M2–M4 are non-vacuous only for
`s ≥ 1`: the section polynomial splits (`l ≥ 2` distinct roots) only with a section direction, and the
root-exchanging loop genuinely needs `hᵢ` irreducible over the **full `(s+1)`-dim base** (the transverse
slice is reducible — its `l` clusters collide at the branch point — so 1-d monodromy can't exchange
them; that collapse is exactly the M3/M4 confinement). So Lemma 4.2.5 must hold over the general base.

**Obstacle & route.** Generalizing the kernel needs the factor-coefficient extension across the
discriminant locus. For `Fin 1` it is 1-variable Riemann removable singularity at a *point*
(`exists_analyticAt_extend_funUnique`); Mathlib has only this (no Hartogs/Osgood/SCV extension). But in
the normal-form setting (`disc = w^r·N`, `w` the distinguished transverse coordinate) the singular set
is the **coordinate hyperplane `{w = 0}`**, so the extension is a *parameter Cauchy integral*
`G(y,w) = (2πi)⁻¹ ∮_{|ζ|=r} (ζ−w)⁻¹·F(y,ζ) dζ`, jointly analytic by the project's own SCV keystone
`circleIntegral_analyticAt_fiber` (`CSCVPackage`, the `weierstrass_division` infrastructure; the
`osgood` bridge is discharged by `holoBridge_findim`). The separable locus is then `ℂ^s × ℂ*` (ball
minus a coordinate hyperplane), connected.

- **G1 — DONE.** `Mccalum/Generalized/HyperplaneExtension.lean` (axiom-clean, not yet imported):
  `cauchyExtend` (the parameter Cauchy integral), `cauchyExtend_analyticAt` (joint analyticity via the
  keystone), `cauchyExtend_eq_fiber` (= `F` off `{w=0}` via 1-var Riemann + Cauchy formula), assembled
  as `exists_analyticAt_extend_hyperplane`.
- **G2a — DONE.** `exists_analyticAt_extend_funCoord0` (`HyperplaneExtension.lean`, axiom-clean): G1
  transported to `Fin (n+1) → ℂ` (extension across `{coord 0 = 0}`) through the coordinate-split CLE
  `coord0Equiv` (built from `Fin.consLinearEquiv ℂ`, `.toContinuousLinearEquiv`). Analyticity transports
  along the CLE; the filter form `exists_analyticAt_extend_hyperplane_nhds` is the vehicle.
- **G2b/c — DONE** (`Mccalum/Generalized/ConnectednessGen.lean`, axiom-clean). `factor_coeff_extends_gen`
  (via G2a), `exists_factor_weierstrass_gen`, `clopen_split_factorization_gen`, `UnivIrreducibleGen`,
  `clopen_split_contradiction_gen`, `aRootCount_eventually_const_gen`, `clopen_split_contradiction'_gen`,
  all over `Fin (n+1) → ℂ` with the deleted-hyperplane filter `𝓝[{x 0 ≠ 0}] 0`. Agreement at `0` uses a
  general-filter lemma `polynomial_eq_of_eventuallyEq_filter` + `(𝓝[{x 0 ≠ 0}] 0).NeBot`; the
  factorisation is recorded off the dense hyperplane (full-nbhd density deferred to CParam wiring, where
  germ-irreducibility ⇒ `UnivIrreducibleGen`).
- **G3 — DONE** (`Mccalum/Generalized/MonodromyGen.lean`, axiom-clean). `rootCover_preconnected_gen` →
  `rootCover_pathConnected_gen` → **`rootCover_exchange_gen`** = Lemma 4.2.5 over `Fin (n+1) → ℂ`, the
  form thesis 4.2.2 needs. Mirrors M1 with the deleted-hyperplane filter; covering machinery +
  `IsLocalHomeomorph.locPathConnectedSpace` reused as-is.

**G1 + G2 + G3 COMPLETE** — green, axiom-clean, wired into `Mccalum`. Remaining toward Conclusion 1:
M2 (Rouché), M3 (homotopies), M4 (assemble via `monodromy_exchange_contradiction`), M5 (normal form +
blow-up); plus CParam wiring (`UnivIrreducibleGen` ↔ `WeierstrassIrreducible`).

### M2 — Rouché cluster separation (thesis step 4) *(DONE)*
`Mccalum/Generalized/RoucheSeparation.lean` (axiom-clean, wired into `Mccalum`, full library green).
The **complex** analogue of `multi_cluster_real_delineation`, for a monic family `P : ℂ → ℂ[X]` of
constant degree with analytic coefficients (the transverse-coordinate slice of the section family):

- **`roots_confined`** (confinement): `∀ᶠ w near 0, ∀ root t of P w, ∃ α ∈ (P 0).roots, t ∈ ball α ρ`.
  Ported the real `multi_cluster` tube-lemma + `cauchyBound` argument to ℂ (helpers
  `fam_eval_continuousOn_C`, `generalized_tube_lemma`). *Soft* — no argument principle.
- **`disc_roots_nonempty`** (non-emptiness / the degree-theoretic content): each disc keeps a root for
  `w` near `0`. The contour root count `(2πi)⁻¹∮_{|t|=ρ} ∂ₜG/G` is **analytic** in `w`
  (`powerSum_analyticAt`, the project's SCV keystone, with my own radius `ρ`) and **integer-valued**
  (`slice_powerSum_eq_rootSum`), hence locally constant, `= (P 0).rootMultiplicity α ≥ 1` at `w = 0`.
  Transported through `CParam 0 1` (`transL`/`transι`) to reuse the `Layer-C` threading lemmas; helpers
  `analyticOrderAt_eval_eq_rootMultiplicity`, `analyticAt_taylor_coeff_C`, `eventually_nat_eq...`.
- **`cluster_separation`** (bundled M2): picks `ρ` from the gap (`exists_sep_radius`), gives pairwise
  **disjoint** discs + `∀ᶠ w` (confinement ∧ each disc non-empty). This is thesis step 4.

Interface for M4: discs are `ball αⱼ ρ` in the *root* plane (lift to `A=D₁`, `B=⋃_{j≥2}Dⱼ` in the cover);
confinement is the `hconf : ∀t, φ''(t) ∈ ⋃ⱼ Dⱼ`; non-emptiness supplies `α∈D₁`, `β∈D₂` at the off-section
base point. **Risk retired.**

### M3 — The two explicit homotopies (thesis steps 7–8) *(DONE)*
`Mccalum/Generalized/MonodromyDeform.lean` (axiom-clean, wired into `Mccalum`, full library green).
**Key design decision:** the base nbhd is the *punctured sup-norm ball* `punctBall δ = ball 0 δ ∩ {z₀≠0}`
(coord `0` = transverse). In normal form this is exactly the separable locus, so `rootCover_exchange_gen`
applies to it, *and* both homotopies stay inside it automatically — no separate "tube around `w'`" needed.

- `mkHomRel` — builder turning an ambient homotopy formula `F : C(I×I, Fin(n+1)→ℂ)` that stays in
  `punctBall δ` into a `ContinuousMap.HomotopyRel` into the subtype `↥(punctBall δ)`.
- `deform_to_transverse_loop` (M3): a loop `Γ` in `punctBall δ` based at `w' = Γ 0` deforms, rel `{0,1}`,
  to a loop `Γ''` with section pinned (`Γ'' t i = w' i` for `i≠0`) and transverse on the circle
  (`‖Γ'' t 0‖ = ‖w'₀‖`); returns also `Γ.HomotopicRel Γ'' {0,1}`. Built as `H.trans K`:
  - `H(s,t) = (1−s)•Γ(t) + s•c(t)`, `c t = update (Γ 0) 0 (Γ₀ t)` — collapse section, stays in the ball
    by **convexity** (`convex_ball`), coord 0 untouched (`≠0`);
  - `K(s,t) = update (Γ 0) 0 ([(1−s)+s·‖w'₀‖/‖Γ₀ t‖]•Γ₀ t)` — radial push, `|z₀|` a **convex combination**
    of `‖Γ₀ t‖` and `‖w'₀‖` (both `<δ`, both `>0`), section `= w'`.
- Endpoints fixed using the loop property `Γ 0 = Γ 1` (so `Γ''(0)=Γ''(1)=w'`).
- **Risk retired.** The two side facts (section constant, transverse modulus constant) are exactly what
  M4 feeds into the M2 confinement at the slice `q(w'_sec,·)`.

### M4 — Assemble the single-factor result *(DONE)*
`Mccalum/Generalized/MonodromyAssemble.lean` (axiom-clean, wired into `Mccalum`, full library green).
**`section_card_le_one`**: for an irreducible normal-form Weierstrass family `q` over `punctBall δ`
(separable there, preconnected), the section polynomial `q a` at any small section point
(`a 0 = 0`, `‖a‖ < δ`) has `(q a).roots.toFinset.card ≤ 1` — the codim-1 (`e=1`) form of
`irreducible_section_single_root_deg`.

Proof = the homotopy-deformation contradiction, by `by_contra` on `2 ≤ card`:
- slice `P τ := q (update a 0 τ)` (`P 0 = q a`); coeffs analytic via `AnalyticAt.comp_of_eq` with the
  affine `update a 0 ·`; run **M2** `cluster_separation P` → radius `ρ`, disjoint discs, `∀ᶠ`
  confinement+non-emptiness; extract `η`-ball;
- pick `r = min η δ / 2`, base point `w' = update a 0 r ∈ punctBall δ`; M2 non-emptiness at `r` gives
  roots `α ∈ D₁`, `β ∈ D₂` of `q w'`, hence two sheets `e₀,e₁` over `w'` (same base ⟹ `hpe := rfl`);
- **M1** `rootCover_exchange_gen` → loop `γ` (lift `e₀↦e₁`); **M3** `deform_to_transverse_loop` → `Γ''`;
- opens `A = rc⁻¹(D₁)`, `B = rc⁻¹(⋃_{β'∈S.erase α₁} ball β' ρ)` via the root-coordinate map
  `rc e = ((e:rootVariety):_×ℂ).2`; disjoint from M2's disc-disjointness;
- **confinement (`hconf`)**: the lift's base is `Γ'' t` (`liftPath_lifts`), so `rc(lift t)` is a root of
  `q(Γ'' t) = P(Γ''ₜ 0)` (slice identity `Γ'' t = update a 0 (Γ''ₜ 0)` from M3's section-pinning), and
  `|Γ''ₜ 0| = r < η` ⟹ M2 confinement puts it in `⋃ⱼ Dⱼ = A∪B`;
- `monodromy_exchange_contradiction hcov hγ0 he'' hexch hhom … hconf heA heβB`.

### M5 — Normal form + blow-up to the general-`e` axiom
- **M5a (`e = 1` normal form):** derive `disc = z_{n-1}^r·N`, `N` non-vanishing, from the
  constant-ambient-order hypothesis. This is the Weierstrass-factorization equivalence: `disc` vanishes
  on the section so `z_{n-1} | disc`; factor `disc = z_{n-1}^r·N` with `z_{n-1} ∤ N`; then
  `ord_{(y,0)}(disc) = r + ord_{(y,0)}(N)`, so *constant order ⇔ `N(y,0) ≠ 0` for all `y` ⇔ normal form*.
  Feeds M1–M4.
- **M5b (Case II, `e ≥ 2 → e = 1`):** the explicit quadratic substitution `Q`. Concrete algebra:
  1. `h∘Q` is a Weierstrass polynomial in the blown-up coords;
  2. `disc(h∘Q) = Z_{n-1}^r·N` with `N(0) ≠ 0` (quasi-homogeneity of Taylor terms);
  3. invoke the `e = 1` result;
  4. pushdown `ψ = ψ'(·,0,…,0)` + root-transport (clean for Conclusion 1; the order-invariance
     transport, `thesis.tex:2419+`, belongs to Conclusion 2).
- **Risk:** M5a trivial; M5b is concrete polynomial algebra, not abstract blow-up geometry.

---

## Dependency graph

```
RootCover.clopen_split_contradiction' (Puiseux, proved) ─► M1 (Lemma 4.2.5) ──┐
ComplexCovering (covering map, DONE)                    ─► M1, M2             ├─► M4 ─► A4-deg (e=1)
Monodromy.monodromy_exchange_contradiction (DONE) ◄───────────────────────────┘        │
M2 (Rouché) ─► M4 ;  M3 (homotopies) ─► M4                                             ▼
M5a (normal form) ─► M1–M4 ;  M5b (blow-up) ─────────────────────► irreducible_section_single_root_deg
                                                                        │
                              A5 (proved) + zariski_single_branch (proved)
                                                                        ▼
                                                       Conclusion 1 fully axiom-free
```

**Reuse / no waste:** Conclusion 2 (`zariski_order_invariant_in_graph`) is unaffected and shares
infrastructure — the Puiseux parametrization `φ` (Covering + Basic) is its route, reusing the same
`ComplexCovering` covering map and `Covering.lean` monodromy. M1 even *consumes* the Puiseux
connectedness result.

## Already-proved assets to reuse

- `Mccalum/Generalized/ComplexCovering.lean` — branched root covering: `rootProj_isCoveringMap_restrict`,
  `analytic_root_section_complex`, local sections.
- `archive/monodromy/Monodromy.lean` (→ reactivated) — `path_confined_to_open`, `liftPath_confined`,
  `monodromy_exchange_contradiction`, `transitive_monodromy_of_pathConnected`.
- `Mccalum/Puiseux/RootCover.lean` — `clopen_split_contradiction'` (connectedness kernel).
- `ZariskiNonsplitting.lean` — A5 + packaging (steps 10–11).

## References
- `thesis/thesis.tex:2540–2765` — Theorems 4.2.1/4.2.2, Lemmas 4.2.4/4.2.5, the homotopy proof.
- `thesis/thesis.tex:2187–2412` — Theorem 4.1.1, Case I / Case II (blow-up).
- `thesis/generalized/proof_corrected.md` — ambient order, the elimination-ideal → disc transfer
  (upstream of this axiom; does not affect M1–M4).
