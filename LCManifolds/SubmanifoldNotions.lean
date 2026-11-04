/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Submanifold
import LCManifolds.TangentMap

/-!
# Notions of submanifolds and immersions

References: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362),
Definitions 3.1.10, 3.3.22, Remark 3.3.23, Lemma 3.3.24; K.-H. Neeb, *Towards a Lie theory of
locally convex groups*, §II.6 and §IV.4; Y. Karshon, D. Miyamoto, J. Watts, *Diffeological
submanifolds and their friends* (arXiv:2204.10381); H. Joris, *Une C^∞-application
non-immersive qui possède la propriété universelle des immersions*, Arch. Math. 39 (1982).

In finite dimensions all reasonable notions of submanifold and immersion agree, up to the
topological phenomena discussed below. In infinite dimensions they split apart, already for
Banach models and more so for locally convex ones. This file records them as separate
definitions, with names that say what each notion is. For a smooth map `f : M → N` and its
differential `T_x f` (read in charts):

* `IsWeakImmersion`: `T_x f` is injective at every point, with no condition on its range;
* `IsImmersion`: moreover `T_x f` has closed range and is a topological isomorphism onto it;
* `IsSplitImmersion`: moreover `T_x f` has a continuous linear left inverse, i.e. its range is
  complemented.

For an injective `f`, the image carries the structure transported from `M`:

* `IsWeaklyImmersedSubmanifold`, `IsImmersedSubmanifold`: `f` is an injective weak immersion,
  resp. an injective immersion;
* `IsInitialSubmanifold` (Glöckner–Neeb, Def. 3.3.22): moreover a map `g` from a test manifold is
  smooth as soon as `f ∘ g` is.

For a subset `X ⊆ M` with slice charts onto a closed subspace `S`:

* `IsEmbeddedSubmanifold` (in `LCManifolds.Submanifold`) and `IsSplitSubmanifold` (`S` is
  complemented).

Implications proved here:

* split immersion ⇒ immersion ⇒ weak immersion (`IsSplitImmersion.isImmersion`,
  `IsImmersion.isWeakImmersion`);
* the inclusion of an embedded submanifold is an immersion and is initial
  (`IsEmbeddedSubmanifold.isImmersion_val`, `IsEmbeddedSubmanifold.isInitialSubmanifold_val`);
  for a split submanifold it is a split immersion (`IsSplitSubmanifold.isSplitImmersion_val`);
* initial and immersed submanifolds are weakly immersed.

None of these implications can be reversed, and initial and immersed submanifolds are not
comparable; see the subtleties below.

**Subtleties (infinite dimensions).**

* *Weak immersions versus immersions.* The differential can be injective without having closed
  range, already between Banach spaces: the inclusion `ℓ¹ → ℓ²` is continuous, linear,
  injective, and its range is dense and not closed. Formalized in
  `LCManifolds.Examples.Counterexamples` (`not_isImmersion_lpInclusion`).
* *Immersions in the sense of Glöckner–Neeb.* Their Def. 3.3.25(b) asks for a local linear
  form with a continuous linear left inverse, which forces the range to be complemented. We do
  not use it as the definition of an immersion: it is much more restrictive than the notion
  above. For Banach models, an immersion with complemented range has this local form by the
  inverse function theorem; for locally convex models that theorem is not available.
* *Initial submanifolds* (Glöckner–Neeb, Def. 3.3.22). A subset `S ⊆ M` with its own manifold
  structure is initial if the inclusion is smooth with injective differential, and a map
  `P → S` is smooth as soon as it is smooth into `M`. The structure is then unique
  (Lemma 3.3.24), so being initial is a property of the subset; its topology may be finer than
  the induced one (Remark 3.3.23).
  - The universal property alone does not give an injective differential: by Joris' theorem
    (`g²` and `g³` smooth imply `g` smooth) the cusp `t ↦ (t², t³)` has it, and its
    differential vanishes at `0`. This is why the injectivity of the differential is part of
    the definition (Glöckner–Neeb, p. 336; Karshon–Miyamoto–Watts call the universal property
    alone a *diffeological submanifold*).
  - Initial does not mean embedded: the dense line in the torus is initial. Embedded does not
    follow from injective immersion either: the figure eight `t ↦ (sin t, sin 2t)`,
    `t ∈ (-π, π)`, is an injectively immersed curve that is not initial. The curve
    `s ↦ (sin s, -sin 2s)` is smooth in `ℝ²`, stays in the figure eight, and crosses the origin
    along the other branch; read in the parameter it jumps from `π` to `0` to `-π`
    Formalized, with the parameter `θ = 2 arctan t`, in `LCManifolds.Examples.Lemniscate`
    (`not_isInitialSubmanifold_lemniscate`).
* *Mechanisms that destroy initiality.* For an injective weak immersion, smooth maps into the
  ambient manifold that land in the image may fail to lift
  - continuously, because two pieces of the image accumulate on each other (figure eight;
    occurs in finite dimensions);
  - continuously, because there are uncountably many pieces (`ℝ × ℝ_discrete → ℝ²`; excluded
    for second countable domains, this is why Glöckner–Neeb assume separability in
    Thm. 9.2.15);
  - continuously, because the map is not even locally a topological embedding (the linear
    inclusion `ℓ¹ → ℓ²`; infinite dimensions only);
  - continuously, but not smoothly, even when the map is a homeomorphism onto its image
    (infinite dimensions only). Example: `j : ℓ² → ℓ² × ℝ`, `j x = (A x, ‖x‖²)`, with `A`
    diagonal acting on the `n`-th block of `ℓ²(ℕ, ℝ²)` by a scalar `aₙ ≤ e^{-n}`. Its
    differential `v ↦ (A v, 2⟪x, v⟫)` is injective, with non-closed range at `0`, and `j` is a
    homeomorphism onto its image (weak convergence plus convergence of norms). The curve
    `y t = ⊕ₙ n⁻² (cos (n t), sin (n t))` has constant norm and `A ∘ y` is smooth, so `j ∘ y`
    is smooth; but `y` is `C¹` and not `C²` in `ℓ²`. So `j` is topologically embedded, weakly
    immersed and not initial. In finite dimensions a weak immersion whose lifts are continuous
    is initial, so this phenomenon has no finite-dimensional analogue.
* *Unitary orbits.* Let `A = i Σₙ λₙ pₙ` be a skew-adjoint operator on a Hilbert space `H`,
  with distinct real `λₙ` and pairwise orthogonal projections `pₙ` (of any rank) summing to `1`.
  Its stabilizer in `U(H)` is the block-diagonal group `K = ⊕ₙ U(pₙ H)`. `K` is a split Lie
  subgroup, via the conditional expectation `X ↦ Σₙ pₙ X pₙ`. The orbit `U(H)/K → B(H)`,
  `uK ↦ u A u*`, is a weak immersion with differential `X ↦ [X, A]`. It is initial if and only
  if there are finitely many `pₙ`.
  - If there are finitely many `pₙ`, the spectrum is finite and the orbit is a closed embedded
    split submanifold (Beltiță–Larotonda, *Unitary group orbits versus groupoid orbits of normal
    operators*). With two projections of infinite rank it is a Grassmannian.
  - If there are infinitely many `pₙ`, the spectrum is infinite, so `[·, A]` does not have
    closed range (same reference). Then the orbit is not initial. Indeed, for orbits of
    Banach–Lie group actions with split stabilizer, initiality forces closed range: along
    `s ↦ exp(s ξ) · A`, every derivative is bounded by a constant times `‖[ξ, A]‖`. Bump
    curves along directions with `‖[ξ, A]‖` tiny are smooth in `B(H)`, and their lifts to
    `U(H)/K` are continuous but not `C¹`.
* *Initial does not imply immersion.* Let `A` be a compact injective diagonal operator on `ℓ²`
  and `j : ℓ² → ℓ² × (ℓ² ⊗ ℓ²) × (ℓ² ⊗ ℓ² ⊗ ℓ²)`, `j x = (A x, x ⊗ x, x ⊗ x ⊗ x)` (Hilbert tensor
  products). Then `j` is injective, its differential `v ↦ (A v, x ⊗ v + v ⊗ x, …)` is injective,
  and at `0` its range `A(ℓ²) × 0 × 0` is not closed. Nevertheless `j` is initial with respect to
  all test manifolds modeled on Fréchet spaces, it is a homeomorphism onto its image, and the
  image is closed. Let `f : P → ℓ²` be such that `j ∘ f` is smooth.
  - Along a smooth curve `c`, each `⟨f ∘ c, e⟩` has smooth square and cube, which are
    `⟪(f ∘ c) ⊗ (f ∘ c), e ⊗ e⟫` and its cubic analogue. So it is smooth by Joris' theorem.
    A curve in a Banach space all of whose scalar components are smooth is smooth, by uniform
    boundedness and Taylor's formula.
  - Smoothness along curves gives smoothness in the Michal–Bastiani sense when `P` is modeled
    on a Fréchet space. First, the directional derivatives `dᵏ f(p)(v, …, v)` are locally
    bounded. If not, there are `pₘ → p₀` and small `wₘ` with `‖dᵏ f(pₘ)(wₘ, …, wₘ)‖ > m`.
    Take `tₘ = 2⁻ᵐ`, `rₘ = 2⁻ᵐ⁻²` (so the intervals `[tₘ - rₘ, tₘ + rₘ]` are disjoint) and a
    bump `β` supported in `[-1, 1]`, equal to `1` on `[-1/2, 1/2]`. Then
    `c t = p₀ + ∑ₘ β ((t - tₘ) / rₘ) (pₘ - p₀ + (t - tₘ) wₘ)` is smooth if `pₘ - p₀` and `wₘ`
    decay fast enough in every seminorm. Near `tₘ`, `c` is affine, `c t = pₘ + (t - tₘ) wₘ`. So
    `(f ∘ c)⁽ᵏ⁾(tₘ) = dᵏ f(pₘ)(wₘ, …, wₘ)` is unbounded, a contradiction. Local bounds then give
    multilinearity (Boman's theorem on finite-dimensional subspaces) and joint continuity of
    the derivatives (mean value inequality).
  So for this `j` the closed-range condition fails at `0` although `j` is initial. Whether `j`
  is initial with respect to test manifolds modeled on non-metrizable spaces is open: the
  argument above uses sequences.
* *Initial Lie subgroups.* Glöckner–Neeb (Def. 9.1.5) call an initial Lie subgroup *strictly
  initial* when `L(ι)` is injective, a condition that Neeb (2006) includes in the definition.
  Not every subgroup carries an initial Lie subgroup structure: `ℓ^∞ ⊆ ℝ^ℕ` does not
  (Glöckner–Neeb, Ex. 9.1.8).
-/

open Set Filter
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

omit [ChartedSpace F N] [MBManifold F N] in
/-- The inverse transition map gives a left inverse of the derivative of a transition map between
charts of the maximal atlas. -/
theorem dMB_transition_leftInverse {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ (mbGroupoid E).maximalAtlas M) (he' : e' ∈ (mbGroupoid E).maximalAtlas M)
    {y : E} (hy : y ∈ e.target ∩ e.symm ⁻¹' e'.source) (v : E) :
    dMB (e ∘ e'.symm) ((e' ∘ e.symm) y, dMB (e' ∘ e.symm) (y, v)) = v := by
  set τ := e' ∘ e.symm
  set σ := e ∘ e'.symm
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' e'.source) := e.isOpen_inter_preimage_symm e'.open_source
  have hτ : ContDiffMBOn 1 τ (e.target ∩ e.symm ⁻¹' e'.source) :=
    smoothMBOn_transition_of_mem_maximalAtlas he he' 1
  have hσ : ContDiffMBOn 1 σ (e'.target ∩ e'.symm ⁻¹' e.source) :=
    smoothMBOn_transition_of_mem_maximalAtlas he' he 1
  have hmaps : MapsTo τ (e.target ∩ e.symm ⁻¹' e'.source) (e'.target ∩ e'.symm ⁻¹' e.source) :=
    fun z hz ↦ ⟨e'.map_source hz.2, by simp [τ, e'.left_inv hz.2, e.map_target hz.1]⟩
  have hev : σ ∘ τ =ᶠ[𝓝 y] id :=
    Filter.eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦ by
      simp [σ, τ, e'.left_inv hz.2, e.right_inv hz.1]
  rw [← ContDiffMBOn.dMB_comp (e'.isOpen_inter_preimage_symm e.open_source) hσ hτ hmaps hy v,
    dMB_congr_of_eventuallyEq hev]
  exact ((ContinuousLinearMap.id ℝ E).hasDirDerivAt y v).dMB_eq

omit [ChartedSpace F N] [MBManifold F N] in
/-- The derivative of a transition map between charts of the maximal atlas is injective: the
inverse transition map is a left inverse. -/
theorem dMB_transition_injective {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ (mbGroupoid E).maximalAtlas M) (he' : e' ∈ (mbGroupoid E).maximalAtlas M)
    {y : E} (hy : y ∈ e.target ∩ e.symm ⁻¹' e'.source) :
    Function.Injective fun v ↦ dMB (e' ∘ e.symm) (y, v) := by
  intro v w h
  have h' : dMB (e' ∘ e.symm) (y, v) = dMB (e' ∘ e.symm) (y, w) := h
  rw [← dMB_transition_leftInverse he he' hy v, ← dMB_transition_leftInverse he he' hy w, h']

omit [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- The center of the preferred chart lies in the domain of the local representative. -/
theorem chartAt_mem_chartDomain (f : M → N) (x : M) :
    chartAt E x x ∈ chartDomain f univ (chartAt E x) (chartAt F (f x)) := by
  refine ⟨(chartAt E x).map_source (mem_chart_source E x), ?_⟩
  rw [mem_preimage, (chartAt E x).left_inv (mem_chart_source E x)]
  exact ⟨mem_univ x, mem_chart_source F (f x)⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- The differential of a smooth map, read in the preferred charts, is continuous. -/
theorem SmoothMBM.continuous_dMB_chart {f : M → N} (hf : SmoothMBM E F f) (x : M) :
    Continuous fun v : E ↦ dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, v) :=
  ((hf 1).2 x (mem_univ x)).continuous_dMB (chartAt_mem_chartDomain f x)

/-! ### Immersions -/

variable (E F) in
/-- A weak immersion: a smooth map whose differential is injective at every point (in the
preferred charts). No condition is imposed on the range of the differential. -/
def IsWeakImmersion (f : M → N) : Prop :=
  SmoothMBM E F f ∧ ∀ x, Function.Injective fun v : E ↦
    dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, v)

variable (E F) in
/-- An immersion: a smooth map whose differential is, at every point (in the preferred charts),
a topological isomorphism onto a closed subspace. -/
def IsImmersion (f : M → N) : Prop :=
  SmoothMBM E F f ∧ ∀ x,
    IsClosed (Set.range fun v : E ↦
      dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, v)) ∧
    Topology.IsEmbedding fun v : E ↦
      dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, v)

variable (E F) in
/-- A split immersion: a smooth map whose differential has, at every point (in the preferred
charts), a continuous linear left inverse. Equivalently, the differential is a topological
isomorphism onto a complemented subspace. -/
def IsSplitImmersion (f : M → N) : Prop :=
  SmoothMBM E F f ∧ ∀ x, ∃ r : F →L[ℝ] E, ∀ v,
    r (dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, v)) = v

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- Immersions are weak immersions. -/
theorem IsImmersion.isWeakImmersion {f : M → N} (hf : IsImmersion E F f) :
    IsWeakImmersion E F f :=
  ⟨hf.1, fun x ↦ (hf.2 x).2.injective⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [MBManifold E M] [MBManifold F N] in
/-- Split immersions are immersions: the range of the differential `D` is the fixed set of the
continuous map `D ∘ r`, and `D` is an embedding since it has a continuous left inverse. -/
theorem IsSplitImmersion.isImmersion {f : M → N} (hf : IsSplitImmersion E F f) :
    IsImmersion E F f := by
  refine ⟨hf.1, fun x ↦ ?_⟩
  obtain ⟨r, hr⟩ := hf.2 x
  have hD := hf.1.continuous_dMB_chart x
  refine ⟨?_, Function.LeftInverse.isEmbedding hr r.continuous hD⟩
  have hrange : Set.range (fun v : E ↦
      dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, v)) =
      {y | dMB (chartAt F (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x, r y) = y} := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact congrArg _ (congrArg (Prod.mk _) (hr v))
    · intro hy
      exact ⟨r y, hy⟩
  rw [hrange]
  exact isClosed_eq (hD.comp r.continuous) continuous_id

/-! ### Submanifolds given by an injective map

An injective map `f : M → N` exhibits its image as a submanifold of `N`, with the manifold
structure transported from `M`. The structure is extra data: the figure eight carries two such
structures. Initial submanifolds are the exception, since their structure is unique
(Glöckner–Neeb, Lemma 3.3.24). -/

variable (E F) in
/-- `f` exhibits its image as a weakly immersed submanifold: `f` is an injective weak immersion. -/
def IsWeaklyImmersedSubmanifold (f : M → N) : Prop :=
  Function.Injective f ∧ IsWeakImmersion E F f

variable (E F) in
/-- `f` exhibits its image as an immersed submanifold: `f` is an injective immersion. -/
def IsImmersedSubmanifold (f : M → N) : Prop :=
  Function.Injective f ∧ IsImmersion E F f

variable (E F) in
/-- `f` exhibits its image as an initial submanifold (Glöckner–Neeb, Def. 3.3.22): `f` is an
injective weak immersion, and a map `g` from a test manifold into `M` is smooth as soon as
`f ∘ g` is smooth. The test manifolds are modeled on locally convex spaces in the universe of
the model spaces. -/
def IsInitialSubmanifold (f : M → N) : Prop :=
  Function.Injective f ∧ IsWeakImmersion E F f ∧
    ∀ {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
      [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H] {P : Type u}
      [TopologicalSpace P] [ChartedSpace H P] [MBManifold H P] (g : P → M),
      SmoothMBM H F (f ∘ g) → SmoothMBM H E g

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- Immersed submanifolds are weakly immersed. -/
theorem IsImmersedSubmanifold.isWeaklyImmersedSubmanifold {f : M → N}
    (hf : IsImmersedSubmanifold E F f) : IsWeaklyImmersedSubmanifold E F f :=
  ⟨hf.1, hf.2.isWeakImmersion⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- Initial submanifolds are weakly immersed (by definition). -/
theorem IsInitialSubmanifold.isWeaklyImmersedSubmanifold {f : M → N}
    (hf : IsInitialSubmanifold E F f) : IsWeaklyImmersedSubmanifold E F f :=
  ⟨hf.1, hf.2.1⟩

/-! ### Embedded and split submanifolds -/

section Embedded

variable {X : Set M} {S : Submodule ℝ E}

/-- `X ⊆ M` is a split submanifold: an embedded submanifold whose model `S` is complemented
(Glöckner–Neeb, Def. 3.1.10). -/
structure IsSplitSubmanifold (X : Set M) (S : Submodule ℝ E) : Prop
    extends IsEmbeddedSubmanifold X S where
  closedComplemented : S.ClosedComplemented

omit [ChartedSpace F N] [MBManifold F N] in
/-- The differential of the inclusion of an embedded submanifold, in the preferred charts, is the
restriction to `S` of a continuous linear automorphism `L` of `E` (the derivative of a transition
map of `M`). -/
theorem IsEmbeddedSubmanifold.exists_dMB_chart_val (h : IsEmbeddedSubmanifold X S) (p : X) :
    letI := h.chartedSpace
    ∃ L L' : E →L[ℝ] E, (∀ w, L' (L w) = w) ∧ (∀ w, L (L' w) = w) ∧
      ∀ v : S, dMB (chartAt E (p : M) ∘ Subtype.val ∘ (chartAt S p).symm) (chartAt S p p, v) =
        L v := by
  let := h.chartedSpace
  obtain ⟨hφ, hp⟩ := (h.exists_sliceChart p p.2).choose_spec
  set φ := (h.exists_sliceChart p p.2).choose
  set c := chartAt E (p : M)
  have hc : c ∈ (mbGroupoid E).maximalAtlas M := (mbGroupoid E).chart_mem_maximalAtlas (p : M)
  have hpc : (p : M) ∈ c.source := mem_chart_source E (p : M)
  set e := sliceChart hφ p
  change ∃ L L' : E →L[ℝ] E, (∀ w, L' (L w) = w) ∧ (∀ w, L (L' w) = w) ∧
    ∀ v : S, dMB (c ∘ Subtype.val ∘ e.symm) (e p, v) = L v
  -- the transition maps `τ = c ∘ φ⁻¹` and `σ = φ ∘ c⁻¹`
  set T := φ.target ∩ φ.symm ⁻¹' c.source
  set T' := c.target ∩ c.symm ⁻¹' φ.source
  have hT : IsOpen T := φ.isOpen_inter_preimage_symm c.open_source
  have hT' : IsOpen T' := c.isOpen_inter_preimage_symm φ.open_source
  have hτ : ContDiffMBOn 1 (c ∘ φ.symm) T := smoothMBOn_transition_of_mem_maximalAtlas hφ.1 hc 1
  have hσ : ContDiffMBOn 1 (φ ∘ c.symm) T' := smoothMBOn_transition_of_mem_maximalAtlas hc hφ.1 1
  have hy : φ p ∈ T := ⟨φ.map_source hp, by rw [mem_preimage, φ.left_inv hp]; exact hpc⟩
  have hy' : c p ∈ T' := ⟨c.map_source hpc, by rw [mem_preimage, c.left_inv hpc]; exact hp⟩
  obtain ⟨L, hL⟩ := hτ.exists_clm hT hy
  obtain ⟨L', hL'⟩ := hσ.exists_clm hT' hy'
  have hτy : (c ∘ φ.symm) (φ p) = c p := by simp [φ.left_inv hp]
  have hσy : (φ ∘ c.symm) (c p) = φ p := by simp [c.left_inv hpc]
  refine ⟨L, L', fun w ↦ ?_, fun w ↦ ?_, fun v ↦ ?_⟩
  · rw [hL, hL', ← hτy]
    exact dMB_transition_leftInverse hφ.1 hc hy w
  · rw [hL', hL, ← hσy]
    exact dMB_transition_leftInverse hc hφ.1 hy' w
  -- near `e p`, the local representative is `(c ∘ φ⁻¹) ∘ S.subtypeL`
  set D := chartDomain Subtype.val univ e c
  have hD : IsOpen D := isOpen_chartDomain isOpen_univ continuous_subtype_val.continuousOn _ _
  have hsub : ∀ y ∈ D, (y : E) ∈ T ∧ ((e.symm y : X) : M) = φ.symm y := by
    rintro y ⟨hy, -, hyc⟩
    have hc' := sliceChart_symm_apply_coe hφ p (y := y) hy
    refine ⟨⟨hy, ?_⟩, hc'⟩
    have : ((e.symm y : X) : M) ∈ c.source := hyc
    rwa [hc'] at this
  have hpD : e p ∈ D := by
    have := chartAt_mem_chartDomain (E := S) (F := E) (Subtype.val : X → M) p
    exact this
  have hev : c ∘ Subtype.val ∘ e.symm =ᶠ[𝓝 (e p)] (c ∘ φ.symm) ∘ S.subtypeL :=
    Filter.eventuallyEq_of_mem (hD.mem_nhds hpD) fun y hy ↦ by
      simp only [Function.comp_apply, (hsub y hy).2]
      rfl
  have hep : ((e p : S) : E) = φ p := sliceChart_apply_coe hφ p hp
  have hmaps : MapsTo S.subtypeL (S.subtypeL ⁻¹' T) T := fun y hy ↦ hy
  have hpre : e p ∈ S.subtypeL ⁻¹' T := by
    rw [mem_preimage, Submodule.subtypeL_apply, hep]
    exact hy
  rw [dMB_congr_of_eventuallyEq hev,
    ContDiffMBOn.dMB_comp hT hτ (S.subtypeL.contDiffMBOn 1 _) hmaps hpre v,
    (S.subtypeL.hasDirDerivAt _ _).dMB_eq, hL]
  simp only [Submodule.subtypeL_apply, hep]

omit [ChartedSpace F N] [MBManifold F N] in
/-- **The inclusion of an embedded submanifold is an immersion.** -/
theorem IsEmbeddedSubmanifold.isImmersion_val (h : IsEmbeddedSubmanifold X S) :
    letI := h.chartedSpace; haveI := h.mbManifold
    IsImmersion S E (Subtype.val : X → M) := by
  let := h.chartedSpace
  have := h.mbManifold
  refine ⟨h.smoothMBM_val, fun p ↦ ?_⟩
  obtain ⟨L, L', hL'L, hLL', hD⟩ := h.exists_dMB_chart_val p
  have hfun : (fun v : S ↦ dMB (chartAt E (p : M) ∘ Subtype.val ∘ (chartAt S p).symm)
      (chartAt S p p, v)) = L ∘ Subtype.val := funext hD
  change IsClosed (range fun v : S ↦ dMB (chartAt E (p : M) ∘ Subtype.val ∘ (chartAt S p).symm)
      (chartAt S p p, v)) ∧ Topology.IsEmbedding fun v : S ↦
      dMB (chartAt E (p : M) ∘ Subtype.val ∘ (chartAt S p).symm) (chartAt S p p, v)
  rw [hfun]
  refine ⟨?_, (Function.LeftInverse.isEmbedding hL'L L'.continuous L.continuous).comp
    Topology.IsEmbedding.subtypeVal⟩
  have hrange : range (L ∘ Subtype.val : S → E) = L' ⁻¹' (S : Set E) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      simp only [Function.comp_apply, mem_preimage, hL'L]
      exact v.2
    · intro hw
      exact ⟨⟨L' w, hw⟩, hLL' w⟩
  rw [hrange]
  exact h.isClosed.preimage L'.continuous

omit [ChartedSpace F N] [MBManifold F N] in
/-- **The inclusion of a split submanifold is a split immersion**: a continuous projection of
`E` onto `S`, composed with the inverse of the derivative of the transition map, is a left
inverse of the differential. -/
theorem IsSplitSubmanifold.isSplitImmersion_val (h : IsSplitSubmanifold X S) :
    letI := h.chartedSpace; haveI := h.mbManifold
    IsSplitImmersion S E (Subtype.val : X → M) := by
  let := h.chartedSpace
  have := h.mbManifold
  refine ⟨h.smoothMBM_val, fun p ↦ ?_⟩
  obtain ⟨L, L', hL'L, -, hD⟩ := h.exists_dMB_chart_val p
  obtain ⟨P, hP⟩ := h.closedComplemented
  refine ⟨P.comp L', fun v ↦ ?_⟩
  change P (L' (dMB (chartAt E (p : M) ∘ Subtype.val ∘ (chartAt S p).symm)
    (chartAt S p p, v))) = v
  rw [hD, hL'L, hP]

omit [ChartedSpace F N] [MBManifold F N] in
/-- **The inclusion of an embedded submanifold is initial**: a map into the submanifold is smooth
as soon as it is smooth into `M`. In the slice chart `φ`, the local representative is the
corestriction to `S` of a local representative of a smooth map into `M`, which is smooth
(`ContDiffMBOn.codRestrict`). -/
theorem IsEmbeddedSubmanifold.isInitialSubmanifold_val (h : IsEmbeddedSubmanifold X S) :
    letI := h.chartedSpace; haveI := h.mbManifold
    IsInitialSubmanifold S E (Subtype.val : X → M) := by
  let := h.chartedSpace
  have := h.mbManifold
  refine ⟨Subtype.val_injective, h.isImmersion_val.isWeakImmersion, ?_⟩
  intro H _ _ _ _ _ _ _ P _ _ _ g hg k
  have hgc : ContinuousOn g univ :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).mpr (hg k).1
  refine ⟨hgc, fun x _ ↦ ?_⟩
  obtain ⟨hφ, -⟩ := (h.exists_sliceChart (g x) (g x).2).choose_spec
  set φ := (h.exists_sliceChart (g x) (g x).2).choose
  set d := chartAt H x
  change ContDiffMBOn k (sliceChart hφ (g x) ∘ g ∘ d.symm)
    (chartDomain g univ d (sliceChart hφ (g x)))
  have hD : IsOpen (chartDomain g univ d (sliceChart hφ (g x))) :=
    isOpen_chartDomain isOpen_univ hgc _ _
  have hM : ContDiffMBOn k (φ ∘ (Subtype.val ∘ g) ∘ d.symm)
      (chartDomain g univ d (sliceChart hφ (g x))) :=
    (hg k).contDiffMBOn_chart_of_mem_maximalAtlas isOpen_univ
      ((mbGroupoid H).chart_mem_maximalAtlas x) hφ.1
  exact ContDiffMBOn.codRestrict h.isClosed hD hM fun y hy ↦
    sliceChart_apply_coe hφ (g x) hy.2.2

omit [ChartedSpace F N] [MBManifold F N] in
/-- The inclusion of an embedded submanifold exhibits it as an immersed submanifold. -/
theorem IsEmbeddedSubmanifold.isImmersedSubmanifold_val (h : IsEmbeddedSubmanifold X S) :
    letI := h.chartedSpace; haveI := h.mbManifold
    IsImmersedSubmanifold S E (Subtype.val : X → M) := by
  let := h.chartedSpace
  have := h.mbManifold
  exact ⟨Subtype.val_injective, h.isImmersion_val⟩

end Embedded

end LCManifolds
