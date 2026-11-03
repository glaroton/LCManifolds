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
* `IsImmersion`: moreover `T_x f` has closed range and is a topological isomorphism onto it.

**Subtleties (infinite dimensions).**

* *Weak immersions versus immersions.* The differential can be injective without having closed
  range, already between Banach spaces: the inclusion `ℓ¹ → ℓ²` is continuous, linear,
  injective, and its range is dense and not closed.
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
    along the other branch; read in the parameter it jumps from `π` to `0` to `-π`.
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
/-- The derivative of a transition map between charts of the maximal atlas is injective: the
inverse transition map is a left inverse. -/
theorem dMB_transition_injective {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ (mbGroupoid E).maximalAtlas M) (he' : e' ∈ (mbGroupoid E).maximalAtlas M)
    {y : E} (hy : y ∈ e.target ∩ e.symm ⁻¹' e'.source) :
    Function.Injective fun v ↦ dMB (e' ∘ e.symm) (y, v) := by
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
  have hinv : ∀ v, dMB σ (τ y, dMB τ (y, v)) = v := fun v ↦ by
    rw [← ContDiffMBOn.dMB_comp (e'.isOpen_inter_preimage_symm e.open_source) hσ hτ hmaps hy v,
      dMB_congr_of_eventuallyEq hev]
    exact ((ContinuousLinearMap.id ℝ E).hasDirDerivAt y v).dMB_eq
  intro v w h
  have h' : dMB τ (y, v) = dMB τ (y, w) := h
  rw [← hinv v, ← hinv w, h']

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

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBManifold E M] [MBManifold F N] in
/-- Immersions are weak immersions. -/
theorem IsImmersion.isWeakImmersion {f : M → N} (hf : IsImmersion E F f) :
    IsWeakImmersion E F f :=
  ⟨hf.1, fun x ↦ (hf.2 x).2.injective⟩

end LCManifolds
