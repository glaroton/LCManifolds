# LCManifolds

**Manifolds modeled on locally convex spaces, formalized in Lean 4 and Mathlib.**

> **Status: early stage.** At present the library contains the basic definition only. It is the
> geometric companion of [LCAnalysis](https://github.com/glaroton/LCAnalysis), which provides the
> calculus.

## Contents

* [`LCManifolds/Basic.lean`](LCManifolds/Basic.lean):
  * `mbGroupoid E`, the structure groupoid of Michal–Bastiani smooth diffeomorphisms between open
    subsets of a locally convex space `E`;
  * `MBManifold`, smooth manifolds modeled on `E` [Nee06, Def. I.3.1; GN26, Ch. 3].

There is no `sorry`.

## Design

Mathlib's `ChartedSpace` and `StructureGroupoid` accept an arbitrary topological model space, so
Mathlib's chart machinery is reused directly. A manifold modeled on `E` is a `ChartedSpace E M`
with `HasGroupoid M (mbGroupoid E)`. Only the notion of smoothness changes: Mathlib's
`contDiffGroupoid` needs a normed model with corners, and this library replaces it with the
Michal–Bastiani calculus of LCAnalysis.

## Planned

1. Smooth maps between manifolds.
2. Tangent spaces, the tangent bundle and the tangent map.
3. Lie groups modeled on locally convex spaces and their Lie algebras [Nee06, GN26].

## References

* **[GN26]** H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, book manuscript,
  arXiv:2602.12362 (2026).
* **[Nee06]** K.-H. Neeb, *Towards a Lie theory of locally convex groups*, Jpn. J. Math. 1 (2006),
  291–468; arXiv:1501.06269.
* The mathlib Community, *The Lean mathematical library*, CPP 2020, 367–381. This library uses
  Mathlib's `ChartedSpace`, `StructureGroupoid` and `OpenPartialHomeomorph`.

The section "How this library was written" of LCAnalysis applies here too. Gabriel Larotonda
directed the work, and the Lean proofs were written by the AI assistant Claude (Anthropic).

## Build

```bash
lake exe cache get
lake build
```

LCAnalysis is a dependency (see `lakefile.toml`).

## License

Apache 2.0; see [LICENSE](LICENSE).
