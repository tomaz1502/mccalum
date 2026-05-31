# Corrected proof of the key step in the Generalized Lifting Theorem (3.2.1′)

This note fixes a defect in `proof.tex`, §5.4.4 ("Recovering order-invariance of
`disc(h)`") and the Order Additivity Lemma (§4) it relies on. Everything else in
`proof.tex` is correct and is only summarized here. The fix is conceptual (the right
*notion of order*), not a counterexample to the theorem: **the theorem is true; the
proof of one step was using the wrong order.**

Throughout, `n = r − 1`, `Δ ⊆ ℂⁿ` is a polydisc, and
`T* = {z ∈ Δ : z_{s+1} = ⋯ = z_n = 0}` is the (complexified) `s`-dimensional section,
where `s = dim S`. The transverse directions are `z_{s+1}, …, z_n`.

For a holomorphic `F` on `Δ` and a point `p ∈ Δ`, write `ord_p(F)` for the **ambient
vanishing order** of `F` at `p`: the largest `k` such that every partial derivative
`∂^α F` with `|α| < k` vanishes at `p` (equivalently, the lowest total degree appearing
in the Taylor expansion of `F` at `p`). In Lean this is `analyticOrderAt` / `order ℂ F p`.

> **Two different "orders" — this is the whole point.**
> For `p ∈ T*` there are two distinct quantities:
> * `ord_p(F)` — the **ambient** order of `F` (a function on `ℂⁿ`) at the point `p`;
> * `ord_p^{T*}(F|_{T*})` — the **intrinsic** order of the *restriction* `F|_{T*}`
>   (a function on `ℂˢ`) at `p`.
>
> They differ precisely when `F` vanishes along `T*`. Example: `F = z_n` (a transverse
> coordinate). Ambient: `ord_p(F) = 1` for every `p ∈ T*`. Intrinsic: `F|_{T*} ≡ 0`, so
> `ord_p^{T*}(F|_{T*}) = ∞` everywhere. The proof needs the **ambient** order; the
> original argument silently used the intrinsic one.

---

## 1. The defect

In §5.4.4 the norm identity (Cor. 5.x) gives, on `Δ₂`,
```
        P̃ᵐ  =  ± disc(h) · Q                                   (★)
```
with `P̃, disc(h), Q` holomorphic on `Δ₂`. The proof then restricts (★) to `T*` and
applies the Order Additivity Lemma (§4) to conclude that `disc(h)|_{T*}` has constant
order. But the Order Additivity Lemma as stated requires **both factors to be not
identically zero on the connected set**, and it is justified by:

> "`disc(h) ≢ 0` because `f` is squarefree, … so `h` is squarefree." (line 537)

That establishes `disc(h) ≢ 0` **ambiently on `Δ₂`** — which is true — but the lemma
is being applied to **`disc(h)|_{T*}`**, the restriction to the section, and *that is
typically `≡ 0`*.

**Concrete witness.** Take `f = x₃² − x₂` (squarefree), `S = {x₂ = 0}` (so `r = 3`,
`s = 1`, codimension `1`). Then `h = x₃² − x₂` and `disc(h) = 4x₂`.
* Ambiently on `Δ₂`: `disc(h) = 4x₂ ≢ 0`. ✔ (matches line 537)
* On the section `T* = {z₂ = 0}`: `disc(h)|_{T*} = 4·0 ≡ 0`. ✗ — the lemma's hypothesis
  fails.

So the lemma cannot be applied as written, and `disc(h)|_{T*}` has *infinite* (constant,
but `⊤`) intrinsic order — useless for Zariski's theorem, which needs a *finite* order.
This is not a corner case: `disc(h)|_{T*} ≡ 0` is the **generic** situation in the
positive-codimension case (the section root has multiplicity `m ≥ 2`), which is the whole
reason §5.4 exists.

The very next line of `proof.tex` (line 559) already writes the *correct* object —
`disc(h) = z^{r₀} · N` with `N` non-vanishing, i.e. the **ambient** order `r₀` along the
section (in the example, `4x₂ = x₂¹ · 4`, so `r₀ = 1`). The conclusion is right; only the
lemma used to reach it is mis-stated. The fix is to prove and use the **ambient** version.

---

## 2. Corrected Lemma — order additivity along a submanifold (ambient order)

> **Lemma (Ambient order additivity along `T*`).**
> Let `Δ ⊆ ℂⁿ` be a connected polydisc and `T* ⊆ Δ` the section above. Let
> `F, G : Δ → ℂ` be holomorphic with `F ≢ 0` and `G ≢ 0` **on `Δ`** (ambient, *not* on
> `T*`). If the product `F·G` is order-invariant along `T*`, i.e. `ord_p(F·G)` is the
> same value `c` for all `p ∈ T*`, then `F` and `G` are each order-invariant along `T*`:
> `ord_p(F)` and `ord_p(G)` are constant for `p ∈ T*`.

**Proof.**

1. *Additivity at each point.* The vanishing order at a point is a valuation, so for
   every `p ∈ Δ`,
   ```
        ord_p(F·G) = ord_p(F) + ord_p(G).
   ```
   (Lean: `order_mul_analytic`, already proved.)

2. *Finiteness.* Since `F ≢ 0` on the connected open `Δ`, the identity theorem gives
   `ord_p(F) < ∞` for all `p ∈ Δ`; likewise `ord_p(G) < ∞`. (Lean:
   `order_ne_top_of_ne_zero`.) In particular `ord_p(F), ord_p(G) ∈ ℕ` for `p ∈ T*`.

3. *Minima along `T*` are attained on a dense open subset.* Put
   ```
        a = min_{p ∈ T*} ord_p(F),     b = min_{p ∈ T*} ord_p(G)
   ```
   (well-defined: non-negative integers). Consider
   ```
        Σ_F = { p ∈ T* : ord_p(F) > a }
            = { p ∈ T* : ∂^α F(p) = 0  for all |α| ≤ a }.
   ```
   Each `∂^α F` is holomorphic on `Δ`, so `∂^α F|_{T*}` is holomorphic on `T* ≅ ℂˢ`, and
   `Σ_F` is the common zero set of finitely many such functions — an **analytic subset of
   `T*`**. It is **proper**: by definition of `a` there is `q ∈ T*` with `ord_q(F) = a`,
   so some `∂^α F` with `|α| = a` has `∂^α F(q) ≠ 0`; hence `∂^α F|_{T*} ≢ 0` and
   `Σ_F ⊊ T*`. Therefore `T* ∖ Σ_F` is **dense open** in `T*`. Symmetrically `T* ∖ Σ_G`
   is dense open.

   > *Key contrast with the original lemma.* `Σ_F` is cut out by the **ambient**
   > derivatives `∂^α F` (all directions, including transverse) restricted to `T*` — not
   > by the derivatives of `F|_{T*}`. This is what makes the argument go through even when
   > `F|_{T*} ≡ 0`: in the example `F = z_n`, `Σ_F = ∅` (since `∂_{z_n}F ≡ 1 ≠ 0`),
   > so `ord_p(F) = 1` everywhere on `T*`, exactly as it should be.

4. *The minima are compatible.* `T*` is connected (it is a polydisc in `ℂˢ`), so the two
   proper analytic subsets `Σ_F, Σ_G` cannot cover it; pick
   `p* ∈ (T* ∖ Σ_F) ∩ (T* ∖ Σ_G)`. There `ord_{p*}(F) = a`, `ord_{p*}(G) = b`, so
   ```
        a + b = ord_{p*}(F·G) = c.
   ```

5. *Rigidity.* For an arbitrary `p ∈ T*`: `ord_p(F) ≥ a`, `ord_p(G) ≥ b`, and
   `ord_p(F) + ord_p(G) = ord_p(F·G) = c = a + b`. Since `a, b` are finite, the two
   inequalities and the equality force
   ```
        ord_p(F) = a   and   ord_p(G) = b.
   ```
   Hence `ord_·(F) ≡ a` and `ord_·(G) ≡ b` on `T*`. ∎

The proof is structurally the same as the existing `order_additivity_holomorphic`
(Lifting.lean:233) — finite order, additivity, the "sum is constant + each ≥ its min ⇒
each = its min" rigidity. The **only** change is that "order at a point of an open set
`U ⊆ ℂˢ`" is replaced by "**ambient** order at a point of `T* ⊆ Δ ⊆ ℂⁿ`," and the
non-vanishing hypotheses are ambient (`F, G ≢ 0` on `Δ`), not on `T*`.

---

## 3. Corrected §5.4.4 — recovering order-invariance of `disc(h)`

We keep everything up to the norm identity unchanged:

* (§5.4.3, **ambient**, correct) `P̃` is order-invariant along `T*`:
  `ord_p(P̃) = μ` for every `p ∈ T*`, where `μ = ord_0(P̃) < ∞`. (Established from: all
  ambient partials of `P̃` of order `< μ` vanish on `T*` by order-invariance of `P` on
  `S`; some order-`μ` partial is `≠ 0` at `0`, hence `≠ 0` on a `T*`-neighborhood by
  continuity. This already uses the ambient order — no change.)
* (Norm identity, Cor. 5.x, unchanged) On `Δ₂`:  `P̃ᵐ = ± disc(h) · Q`,  with `Q = N(b̄)`
  holomorphic.

Now the corrected argument:

1. **Both factors are nonzero ambiently.**
   * `disc(h) ≢ 0` on `Δ₂`: `f` squarefree ⇒ `g` squarefree as a pseudopolynomial ⇒ `h`
     (which divides `g` with unit cofactor `u`) is squarefree ⇒ its discriminant is not
     the zero function on `Δ₂`. *(This is the original line 537 — correct as an **ambient**
     statement. We do not, and need not, claim `disc(h)|_{T*} ≢ 0`; indeed it is usually
     `≡ 0`.)*
   * `Q ≢ 0` on `Δ₂`: from `P̃ᵐ ≢ 0` (as `P̃ ≢ 0`) and `disc(h) ≢ 0` in the integral
     domain `𝒪(Δ₂)`.

2. **The product is order-invariant along `T*`.** `ord_p(P̃ᵐ) = m·ord_p(P̃) = mμ` for all
   `p ∈ T*` (point-order is a valuation; Lean `order_pow_analytic`). By (★),
   `ord_p(± disc(h)·Q) = mμ` is constant along `T*`.

3. **Apply the corrected Lemma (§2)** to `F = ± disc(h)` and `G = Q` on `Δ₂` (both `≢ 0`,
   product order-invariant along `T*`). Conclusion:
   ```
        ord_p( disc(h) )  is constant  for all p ∈ T*.
   ```
   Call this constant `r₀ := ord_0(disc(h)) < ∞`.

This is **exactly** the hypothesis required by Zariski's theorem and by the Lean axiom
`zariski_root_sections`, whose `hdisc` is literally
`order ℂ (weierstrassDiscFn m a) (y,0) = order ℂ (weierstrassDiscFn m a) 0` — the
**ambient** order of the discriminant function at the section point `(y,0)`. No statement
about `disc(h)|_{T*}` is needed anywhere.

---

## 4. Downstream (unchanged) and the no-splitting remark

* **Zariski's theorem (§5.4.5, unchanged, Ch. 4 black box).** With `disc(h)`
  order-invariant along `T*`, Zariski's 1975 theorem gives holomorphic root section(s) of
  `h` over `T*` and order-invariance of `h` in the section graph.

* **Return to the real domain (§5.4.6, unchanged).** Schwarz reflection makes the section(s)
  real on `T ∩ ℝˢ`; pulling back through the chart gives the analytic real root function `θ`
  with its multiplicity, and order-invariance of `f` in its graph.

> **Remark (no splitting / single branch — why the cluster gives *one* root function).**
> Delineability *means* the real root functions are pairwise **disjoint**; in particular a
> multiplicity-`m` base root must extend to a *single* analytic function of multiplicity
> `m`, not several functions meeting at the base. This is consistent with — and is part of
> — the equisingularity content of Zariski's theorem under constant `disc(h)` order:
>
> If, over `T*`, `h` had two distinct holomorphic root sections `ψ₁ ≠ ψ₂` (both `→ 0` at
> the base, so meeting there), then the discriminant carries a factor `(ψ₁ − ψ₂)^{…}` whose
> presence *raises* the vanishing order at the base relative to nearby section points where
> `ψ₁ ≠ ψ₂` — contradicting the constant order just established. Hence the cluster is a
> single branch of multiplicity `m`. (In `f = x₃² − x₂`: over `T* = {z₂ = 0}`,
> `h|_{T*} = z₃²`, a single root `ψ = 0` of multiplicity `2`; the two Puiseux roots
> `±√z₂` separate only **transversally**, off `S`.)
>
> *Formalization consequence:* the Lean axiom `zariski_root_sections` is currently stated
> with a **general** number of sections `r`. For the cluster reached here, `r = 1`. Either
> (i) tighten the Zariski axiom's conclusion to a single branch (faithful to its use), or
> (ii) keep general `r` and derive `r = 1` from constant `disc(h)` order via the
> order-drop argument above. This is the honest home of the "no-splitting" content — it
> belongs to the Zariski/equisingularity step, **not** to the real-recovery step (which is
> the already-proved `real_delineation_of_single_branch`).

---

## 5. Notes for the formalization

1. **Target statement is already correct.** `zariski_root_sections.hdisc` uses ambient
   order at section points `(y,0)`. Good — keep it.

2. **Add the ambient Order Additivity Lemma.** The existing
   `order_additivity_holomorphic` (Lifting.lean:233) is stated for `f, g : (Fin s → ℂ) → ℂ`
   on `U ⊆ (Fin s → ℂ)` — the **intrinsic/section** version. It must **not** be applied to
   `y ↦ disc(h)(y,0)` (that pullback is identically `0` in the multiple-root case, so its
   `hf_ne` hypothesis fails). Instead formalize/apply the **ambient** version:
   `F, G : CParam s e → ℂ`, nonvanishing on the ambient polydisc, product order-invariant
   along the section `{(y,0)}`, conclude each factor order-invariant along the section.
   The proof skeleton (finite order, `order_mul_analytic`, min-attained-on-dense-open,
   rigidity) transfers verbatim; the analytic-subset/dense-open step uses the ambient
   derivatives `∂^α F` restricted to the section.

3. **Audit `DiscOrder.lean`.** Check that `order_factor_const_of_mul_analytic` /
   `order_invariant_factor_of_mul` operate on the **ambient** order at section points
   (orders of `weierstrassResFun`/`weierstrassDiscFn : CParam s e → ℂ` at `(y,0)`), not on
   the section restriction. From the `zariski` interface this appears to be the case, but
   it should be confirmed that nowhere does the chain require
   `disc(h)|_{section} ≢ 0` (which is false for `m ≥ 2`). Only `disc(h) ≢ 0` **ambiently**
   (from squarefreeness of `h`) may be used.

4. **`proof.tex` edits.** Replace the §4 Order Additivity Lemma statement with the ambient
   version (§2 here); rewrite §5.4.4 per §3 here; correct the justification on line 537 to
   say explicitly "`disc(h) ≢ 0` *ambiently on `Δ₂`*"; delete any claim that
   `disc(h)|_{T*} ≢ 0`. Add the no-splitting remark (§4 here) so the single-`ψ` use of
   Zariski is justified rather than asserted.
