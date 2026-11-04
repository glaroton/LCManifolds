/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.SubmanifoldNotions
import LCAnalysis.BoundedBelow

/-!
# Immersions with a Banach domain

Let `M` be a Banach manifold, i.e. modeled on a **complete** normed space `E` (`CompleteSpace E`),
and `N` a manifold modeled on a normed space `F`, complete or not. An immersion `f : M → N` (the
differential is a topological isomorphism onto a closed subspace, with no complement assumed)
reflects smoothness of continuous maps: if `g : P → M` is continuous and `f ∘ g` is smooth, then
`g` is smooth (`IsImmersion.smoothMBM_of_comp`). The test manifold `P` may be modeled on any locally convex
space. Consequently, an injective immersion which is a homeomorphism onto its image is an initial
submanifold (`IsImmersedSubmanifold.isInitialSubmanifold`).

The calculus behind this is `LCAnalysis.ContDiffMBOn.of_comp_of_boundedBelow`: in charts the
differential is bounded below, and the bound persists near a point because, for Banach spaces,
Michal–Bastiani `C^{k+1}` maps are Fréchet `C^k`.

**Subtleties.**

* No inverse function theorem is used, and no complement of the range of the differential is
  needed. The image of a non-split immersion need not have slice charts: whether such an
  immersion, when a homeomorphism onto its image, is an embedded submanifold is open.
* Completeness of `E` is used: the derivative of a lift is obtained as the limit of Cauchy
  difference quotients. Completeness of `F` is not needed. Recall that a manifold modeled on an
  incomplete normed space is not a Banach manifold.
* For Fréchet or more general locally convex model spaces the statement is open: the lower bound
  of the differential need not persist near a point.
* Continuity of `g` cannot be dropped: the figure eight is an injective immersion that is not
  initial, because a smooth curve in the plane can lift discontinuously.
-/

open Set Filter
open scoped Topology Manifold ContDiff
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

omit [MBManifold F N] in
/-- **Immersions between Banach manifolds reflect smoothness of continuous maps.** -/
theorem IsImmersion.smoothMBM_of_comp {f : M → N} (hf : IsImmersion E F f) {H : Type u}
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H] {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [MBManifold H P] {g : P → M} (hg : Continuous g)
    (hfg : SmoothMBM H F (f ∘ g)) : SmoothMBM H E g := by
  intro k
  refine contMDiffMB_of_chartAt hg fun x ↦ ?_
  set c := chartAt E (g x)
  set c' := chartAt F (f (g x))
  set d := chartAt H x
  -- the local representative `J` of `f` at `g x`
  set J := c' ∘ f ∘ c.symm
  set D := chartDomain f univ c c'
  have hD : IsOpen D := isOpen_chartDomain isOpen_univ (hf.1 0).1 c c'
  have hJ : SmoothMBOn J D := fun n ↦ (hf.1 n).2 (g x) (mem_univ _)
  have hJF : ContDiffOn ℝ ∞ J D := (smoothMBOn_iff_contDiffOn hD).mp hJ
  have hy₀ : c (g x) ∈ D := chartAt_mem_chartDomain f (g x)
  -- the differential at `c (g x)` is bounded below
  have hJd : HasFDerivAt J (fderiv ℝ J (c (g x))) (c (g x)) :=
    ((hJF.contDiffAt (hD.mem_nhds hy₀)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun v : E ↦ dMB J (c (g x), v)) = ⇑(fderiv ℝ J (c (g x))) :=
    funext fun v ↦ (hJd.hasDirDerivAt v).dMB_eq
  have hemb : Topology.IsEmbedding (fderiv ℝ J (c (g x))) := by
    rw [← hfun]
    exact ((hf.2 (g x)).2 : _)
  obtain ⟨m, hm, hbd⟩ := exists_boundedBelow_of_isEmbedding hemb
  obtain ⟨V, hVD, hV, -, hy₀V, hbdV⟩ := exists_nhds_boundedBelow hD
    (hJF.continuousOn_fderiv_of_isOpen hD (by simp)) hy₀ hm hbd
  -- the local representative `γ` of `g`, on the set where it lands in `V`
  set γ := c ∘ g ∘ d.symm
  set Ω := chartDomain g univ d c
  have hΩ : IsOpen Ω := isOpen_chartDomain isOpen_univ hg.continuousOn d c
  have hγc : ContinuousOn γ Ω :=
    c.continuousOn.comp (hg.continuousOn.comp (d.continuousOn_symm.mono fun z hz ↦ hz.1)
      fun z _ ↦ mem_univ _) fun z hz ↦ hz.2.2
  set O := Ω ∩ γ ⁻¹' V
  have hO : IsOpen O := hγc.isOpen_inter_preimage hΩ hV
  have hxO : d x ∈ O := ⟨chartAt_mem_chartDomain g x, by
    change c (g (d.symm (d x))) ∈ V
    rw [d.left_inv (mem_chart_source H x)]
    exact hy₀V⟩
  -- on `O`, `J ∘ γ` is the local representative of `f ∘ g`
  have hOfg : O ⊆ chartDomain (f ∘ g) univ d c' := by
    rintro z ⟨⟨hzd, -, hzc⟩, hzV⟩
    refine ⟨hzd, mem_univ _, ?_⟩
    have := (hVD hzV).2.2
    change f (c.symm (c (g (d.symm z)))) ∈ c'.source at this
    rwa [c.left_inv hzc] at this
  have hJγ : ContDiffMBOn k (J ∘ γ) O := by
    refine ContDiffMBOn.congr_of_isOpen hO (fun z hz ↦ ?_)
      (((hfg k).2 x (mem_univ _)).mono hOfg)
    change c' (f (g (d.symm z))) = c' (f (c.symm (c (g (d.symm z)))))
    rw [c.left_inv hz.1.2.2]
  have hγk : ContDiffMBOn k γ O :=
    ContDiffMBOn.of_comp_of_boundedBelow hV (fun n ↦ (hJ n).mono hVD) (half_pos hm) hbdV k hO
      (hγc.mono inter_subset_left) (fun z hz ↦ hz.2) hJγ
  exact ⟨O, hO, hxO, inter_subset_left, hγk⟩

omit [MBManifold F N] in
/-- **An injective immersion between Banach manifolds which is a homeomorphism onto its image is
an initial submanifold.** Smooth maps into `N` with values in the image lift continuously, since
`f` is a topological embedding, and then smoothly by `IsImmersion.smoothMBM_of_comp`. -/
theorem IsImmersedSubmanifold.isInitialSubmanifold {f : M → N}
    (hf : IsImmersedSubmanifold E F f) (hemb : Topology.IsEmbedding f) :
    IsInitialSubmanifold E F f := by
  refine ⟨hf.1, hf.2.isWeakImmersion, ?_⟩
  intro H _ _ _ _ _ _ _ P _ _ _ g hfg
  have hc : Continuous (f ∘ g) := continuousOn_univ.mp (hfg 0).1
  exact hf.2.smoothMBM_of_comp (hemb.continuous_iff.mpr hc) hfg

end LCManifolds
