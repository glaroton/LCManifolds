/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.BundleConnection
import LocallyConvexManifolds.VectorField

/-!
# Sections of vector bundles and the global covariant derivative

A section of a vector bundle `V` over `M` is a map `s : M → V` with `s(x)` in the fiber over
`x` (`MBVectorBundleCore.IsSection`). In the trivialization over a chart `i` it has a local
representative `sᵢ : i(Uᵢ) → F` (`MBVectorBundleCore.localRep`), with `sⱼ ∘ τ = g · sᵢ` on
overlaps (`localRep_transition`).

For a connection on `V`, the covariant derivative `∇_X s` of a section along a vector field is
defined in the preferred chart at each point by `dsᵢ · Xᵢ − Γᵢ(Xᵢ, sᵢ)`
(`BundleConnection.covDeriv`), and it is given by the same formula in every trivialization
(`BundleConnection.localRep_covDeriv`). The curvature `R(X, Y) s = ∇_X ∇_Y s − ∇_Y ∇_X s −
∇_[X,Y] s` only depends on the values of `X`, `Y`, `s` at the point, where it is the curvature
form `Ω` of the preferred chart (`BundleConnection.curvature_eq`).

No completeness of `E` or `F` is assumed.
-/

open Set Function Filter Bundle
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace MBVectorBundleCore

variable (V : MBVectorBundleCore E M F)

/-- A section of the bundle: `s(x)` lies in the fiber over `x`. -/
def IsSection (s : M → V.TotalSpace) : Prop := ∀ x, (s x).proj = x

/-- The local representative `sᵢ : i(Uᵢ) → F` of a section in the trivialization over `i`. -/
def localRep (i : atlas E M) (s : M → V.TotalSpace) (y : E) : F :=
  (V.bundleChart i i.1 (s (i.1.symm y))).2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- The charts of the total space over charts of the atlas are in its atlas. -/
theorem bundleChart_mem_atlas (i : atlas E M) :
    V.bundleChart i i.1 ∈ atlas (E × F) V.TotalSpace :=
  ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨i.1, i.2, OpenPartialHomeomorph.refl F,
    chartedSpaceSelf_atlas.mpr rfl, rfl⟩, rfl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- On overlaps, `sⱼ(τ y) = g_{ij}(i⁻¹ y) sᵢ(y)`. -/
theorem localRep_transition {s : M → V.TotalSpace} (hs : V.IsSection s) (i j : atlas E M)
    {y : E} (hy : y ∈ i.1.target) (hyj : i.1.symm y ∈ j.1.source) :
    V.localRep j s ((j.1 ∘ i.1.symm) y) = V.coordChange i j (i.1.symm y) (V.localRep i s y) := by
  set q := i.1.symm y
  have hq : q ∈ i.1.source := i.1.map_target hy
  have e1 : j.1.symm ((j.1 ∘ i.1.symm) y) = q := by
    simp only [Function.comp_apply, q, j.1.left_inv hyj]
  unfold localRep
  rw [e1]
  have hsq : (s q).proj = q := hs q
  generalize s q = p at hsq ⊢
  obtain ⟨xp, w⟩ := p
  change xp = q at hsq
  subst hsq
  rw [bundleChart_apply, bundleChart_apply]
  exact (V.coordChange_comp ⟨chartAt E q, chart_mem_atlas E q⟩ i j q
    ⟨⟨mem_chart_source E q, hq⟩, hyj⟩ w).symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- In the preferred chart at `x`, the local representative at `x` is `s(x)` itself. -/
theorem localRep_chartAt {s : M → V.TotalSpace} (hs : V.IsSection s) (x : M) :
    V.localRep ⟨chartAt E x, chart_mem_atlas E x⟩ s (chartAt E x x) = (s x).2 := by
  unfold localRep
  rw [(chartAt E x).left_inv (mem_chart_source E x), bundleChart_apply]
  have hsx : (s x).proj = x := hs x
  generalize s x = p at hsx ⊢
  obtain ⟨xp, w⟩ := p
  change xp = x at hsx
  subst hsx
  exact V.coordChange_self _ xp (mem_chart_source E xp) w

/-- The local representatives of a `C^k` section are `C^k`. -/
theorem contDiffMBOn_localRep {k : ℕ} {s : M → V.TotalSpace} (hsv : V.IsSection s)
    (hs : ContMDiffMB E (E × F) k s) (i : atlas E M) :
    ContDiffMBOn k (V.localRep i s) i.1.target := by
  have h := hs.contDiffMBOn_chart isOpen_univ i.2 (V.bundleChart_mem_atlas i)
  have hsub : i.1.target ⊆ chartDomain s univ i.1 (V.bundleChart i i.1) := by
    intro y hy
    refine ⟨hy, mem_univ _, ?_⟩
    rw [mem_preimage, mem_bundleChart_source, hsv]
    exact ⟨i.1.map_target hy, i.1.map_target hy⟩
  exact ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn k univ).comp i.1.open_target isOpen_univ
    (h.mono hsub) (mapsTo_univ _ _)

end MBVectorBundleCore

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The local covariant derivative at `y` only depends on the germ of the section. -/
theorem localCovDerivB_congr_right {Γ : E → E → F → F} {A : E → E} {s s' : E → F} {y : E}
    (h : s =ᶠ[𝓝 y] s') : localCovDerivB Γ A s y = localCovDerivB Γ A s' y := by
  rw [localCovDerivB, localCovDerivB, dMB_congr_of_eventuallyEq h, h.eq_of_nhds]

namespace BundleConnection

variable {V : MBVectorBundleCore E M F} (C : BundleConnection V)

/-- The covariant derivative `∇_X s` of a section along a vector field, computed in the preferred
chart at each point. -/
def covDeriv (X : M → TangentBundle E M) (s : M → V.TotalSpace) (x : M) : V.TotalSpace :=
  ⟨x, (localCovDerivB (C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩)
    (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X)
    (V.localRep ⟨chartAt E x, chart_mem_atlas E x⟩ s) (chartAt E x x) : F)⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem isSection_covDeriv (X : M → TangentBundle E M) (s : M → V.TotalSpace) :
    V.IsSection (C.covDeriv X s) :=
  fun _ ↦ rfl

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem covDeriv_snd (X : M → TangentBundle E M) (s : M → V.TotalSpace) (x : M) :
    (show F from (C.covDeriv X s x).2) =
      localCovDerivB (C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩)
        (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X)
        (V.localRep ⟨chartAt E x, chart_mem_atlas E x⟩ s) (chartAt E x x) :=
  rfl

/-- **The covariant derivative does not depend on the trivialization**: in every chart `j`, the
local representative of `∇_X s` is `dsⱼ · Xⱼ − Γⱼ(Xⱼ, sⱼ)`. -/
theorem localRep_covDeriv {X : M → TangentBundle E M} {s : M → V.TotalSpace}
    (hXv : IsVectorField X) (hsv : V.IsSection s) (hs : ContMDiffMB E (E × F) 1 s)
    (j : atlas E M) {y : E} (hy : y ∈ j.1.target) :
    V.localRep j (C.covDeriv X s) y =
      localCovDerivB (C.Γ j) (localRep j X) (V.localRep j s) y := by
  set x := j.1.symm y
  have hxj : x ∈ j.1.source := j.1.map_target hy
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hxi : x ∈ i.1.source := mem_chart_source E x
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hmaps : MapsTo (j.1 ∘ i.1.symm) T j.1.target := fun z hz ↦ j.1.map_source hz.2
  have hix : i.1 x ∈ T := ⟨i.1.map_source hxi, by simp [i.1.left_inv hxi, hxj]⟩
  have hτx : (j.1 ∘ i.1.symm) (i.1 x) = y := by
    simp [i.1.left_inv hxi, x, j.1.right_inv hy]
  have hlin : ∀ z ∈ T, i.1.symm z ∈ i.1.source ∩ j.1.source := fun z hz ↦
    ⟨i.1.map_target hz.1, hz.2⟩
  have htrans := localCovDerivB_transition (G := fun z ξ ↦ V.coordChange i j (i.1.symm z) ξ)
    hT hT j.1.open_target subset_rfl (smoothMBOn_transition' i j 1) hmaps (V.smooth i j 1)
    (fun z hz ↦ V.map_add i j _ (hlin z hz)) (fun z hz ↦ V.map_smul i j _ (hlin z hz))
    ((V.contDiffMBOn_localRep hsv hs i).mono inter_subset_left)
    (V.contDiffMBOn_localRep hsv hs j) (C.transition i j) hix
    (localRep_transition hXv i j hix.1 hix.2)
    (fun z hz ↦ V.localRep_transition hsv i j hz.1 hz.2)
  rw [hτx] at htrans
  rw [htrans, ← hτx, V.localRep_transition (isSection_covDeriv C X s) i j hix.1 hix.2]
  congr 1
  exact V.localRep_chartAt (isSection_covDeriv C X s) x

/-- The curvature `R(X, Y) s = ∇_X ∇_Y s − ∇_Y ∇_X s − ∇_[X,Y] s` at `x`, as a vector of the
fiber in the preferred chart. -/
def curvature (X Y : M → TangentBundle E M) (s : M → V.TotalSpace) (x : M) : F :=
  (show F from (C.covDeriv X (C.covDeriv Y s) x).2) -
    (show F from (C.covDeriv Y (C.covDeriv X s) x).2) -
    (show F from (C.covDeriv (lieBracket X Y) s x).2)

/-- **The curvature is tensorial**: for `C²` fields and sections, `R(X, Y) s` at `x` is the
curvature form of the preferred chart, evaluated at the values of `X`, `Y`, `s` at `x`. -/
theorem curvature_eq {X Y : M → TangentBundle E M} {s : M → V.TotalSpace}
    (hXv : IsVectorField X) (hYv : IsVectorField Y) (hsv : V.IsSection s)
    (hX : ContMDiffMB E (E × E) 2 X) (hY : ContMDiffMB E (E × E) 2 Y)
    (hs : ContMDiffMB E (E × F) 2 s) (x : M) :
    C.curvature X Y s x =
      bundleCurv (C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩) (chartAt E x x)
        (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X (chartAt E x x))
        (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y (chartAt E x x))
        (V.localRep ⟨chartAt E x, chart_mem_atlas E x⟩ s (chartAt E x x)) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : i.1 x ∈ i.1.target := i.1.map_source (mem_chart_source E x)
  have hX1 := hX.of_le' (by norm_num : 1 ≤ 2)
  have hY1 := hY.of_le' (by norm_num : 1 ≤ 2)
  have hs1 := hs.of_le' (by norm_num : 1 ≤ 2)
  have hev : ∀ {A : M → TangentBundle E M}, IsVectorField A →
      V.localRep i (C.covDeriv A s) =ᶠ[𝓝 (i.1 x)]
        localCovDerivB (C.Γ i) (localRep i A) (V.localRep i s) :=
    fun hAv ↦ Filter.eventuallyEq_of_mem (i.1.open_target.mem_nhds hx)
      fun _ hy ↦ C.localRep_covDeriv hAv hsv hs1 i hy
  have hbr : localRep i (lieBracket X Y) (i.1 x) =
      localBracket (localRep i X) (localRep i Y) (i.1 x) :=
    localRep_lieBracket hXv hYv hX1 hY1 i hx
  unfold curvature
  rw [covDeriv_snd, covDeriv_snd, covDeriv_snd]
  change localCovDerivB (C.Γ i) (localRep i X) (V.localRep i (C.covDeriv Y s)) (i.1 x) -
      localCovDerivB (C.Γ i) (localRep i Y) (V.localRep i (C.covDeriv X s)) (i.1 x) -
      localCovDerivB (C.Γ i) (localRep i (lieBracket X Y)) (V.localRep i s) (i.1 x) = _
  rw [localCovDerivB_congr_right (hev hYv), localCovDerivB_congr_right (hev hXv)]
  have e3 : localCovDerivB (C.Γ i) (localRep i (lieBracket X Y)) (V.localRep i s) (i.1 x) =
      localCovDerivB (C.Γ i) (localBracket (localRep i X) (localRep i Y)) (V.localRep i s)
        (i.1 x) := by
    simp only [localCovDerivB, hbr]
  rw [e3]
  exact (C.isLocalSymbol i).localCovDerivB_curv i.1.open_target (contDiffMBOn_localRep hXv hX i)
    (contDiffMBOn_localRep hYv hY i) (V.contDiffMBOn_localRep hsv hs i) hx

end BundleConnection

end LocallyConvex.Manifolds
