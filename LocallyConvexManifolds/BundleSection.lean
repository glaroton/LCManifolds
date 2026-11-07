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

universe u v w

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {ι : Type w} {𝒰 : TrivializationCover E M ι}
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace MBVectorBundleCore

variable (V : MBVectorBundleCore 𝒰 F)

/-- A section of the bundle: `s(x)` lies in the fiber over `x`. -/
def IsSection (s : M → V.TotalSpace) : Prop := ∀ x, (s x).proj = x

/-- The local representative `sᵢ : φᵢ(Uᵢ) → F` of a section in the trivialization over `i`. -/
def localRep (i : ι) (s : M → V.TotalSpace) (y : E) : F :=
  (V.bundleChart i (𝒰.chart i).1 (s ((𝒰.chart i).1.symm y))).2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The charts of the total space over the charts of the cover are in its atlas. -/
theorem bundleChart_mem_atlas (i : ι) :
    V.bundleChart i (𝒰.chart i).1 ∈ atlas (E × F) V.TotalSpace :=
  ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨(𝒰.chart i).1, (𝒰.chart i).2, OpenPartialHomeomorph.refl F,
    chartedSpaceSelf_atlas.mpr rfl, rfl⟩, rfl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- On overlaps, `sⱼ(τ y) = g_{ij}(φᵢ⁻¹ y) sᵢ(y)`. -/
theorem localRep_transition {s : M → V.TotalSpace} (hs : V.IsSection s) (i j : ι)
    {y : E} (hy : y ∈ 𝒰.transDomain i j) :
    V.localRep j s (𝒰.trans i j y) =
      V.coordChange i j ((𝒰.chart i).1.symm y) (V.localRep i s y) := by
  set q := (𝒰.chart i).1.symm y
  unfold localRep
  rw [𝒰.symm_trans hy]
  have hsq : (s q).proj = q := hs q
  generalize s q = p at hsq ⊢
  obtain ⟨xp, w⟩ := p
  change xp = q at hsq
  subst hsq
  rw [bundleChart_apply, bundleChart_apply]
  exact (V.coordChange_comp (𝒰.indexAt q) i j q
    ⟨⟨𝒰.mem_baseSet_at q, hy.2.1⟩, hy.2.2⟩ w).symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- In the chosen trivialization at `x`, the local representative at `x` is `s(x)` itself. -/
theorem localRep_indexAt {s : M → V.TotalSpace} (hs : V.IsSection s) (x : M) :
    V.localRep (𝒰.indexAt x) s ((𝒰.chart (𝒰.indexAt x)).1 x) = (s x).2 := by
  unfold localRep
  rw [(𝒰.chart (𝒰.indexAt x)).1.left_inv
    (𝒰.baseSet_subset _ (𝒰.mem_baseSet_at x)), bundleChart_apply]
  have hsx : (s x).proj = x := hs x
  generalize s x = p at hsx ⊢
  obtain ⟨xp, w⟩ := p
  change xp = x at hsx
  subst hsx
  exact V.coordChange_self _ xp (𝒰.mem_baseSet_at xp) w

/-- The local representatives of a `C^k` section are `C^k`. -/
theorem contDiffMBOn_localRep {k : ℕ} {s : M → V.TotalSpace} (hsv : V.IsSection s)
    (hs : ContMDiffMB E (E × F) k s) (i : ι) :
    ContDiffMBOn k (V.localRep i s) (𝒰.domain i) := by
  have h := hs.contDiffMBOn_chart isOpen_univ (𝒰.chart i).2 (V.bundleChart_mem_atlas i)
  have hsub : 𝒰.domain i ⊆ chartDomain s univ (𝒰.chart i).1 (V.bundleChart i (𝒰.chart i).1) := by
    intro y hy
    refine ⟨hy.1, mem_univ _, ?_⟩
    rw [mem_preimage, mem_bundleChart_source, hsv]
    exact ⟨hy.2, 𝒰.symm_mem_source hy⟩
  exact ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn k univ).comp (𝒰.isOpen_domain i)
    isOpen_univ (h.mono hsub) (mapsTo_univ _ _)

end MBVectorBundleCore

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The local covariant derivative at `y` only depends on the germ of the section. -/
theorem localCovDerivB_congr_right {Γ : E → E → F → F} {A : E → E} {s s' : E → F} {y : E}
    (h : s =ᶠ[𝓝 y] s') : localCovDerivB Γ A s y = localCovDerivB Γ A s' y := by
  rw [localCovDerivB, localCovDerivB, dMB_congr_of_eventuallyEq h, h.eq_of_nhds]

namespace BundleConnection

variable {V : MBVectorBundleCore 𝒰 F} (C : BundleConnection V)

/-- The covariant derivative `∇_X s` of a section along a vector field, computed at each point
`x` in the chosen trivialization `i(x)`. -/
def covDeriv (X : M → TangentBundle E M) (s : M → V.TotalSpace) (x : M) : V.TotalSpace :=
  ⟨x, (localCovDerivB (C.Γ (𝒰.indexAt x)) (localRep (𝒰.chart (𝒰.indexAt x)) X)
    (V.localRep (𝒰.indexAt x) s) ((𝒰.chart (𝒰.indexAt x)).1 x) : F)⟩

theorem isSection_covDeriv (X : M → TangentBundle E M) (s : M → V.TotalSpace) :
    V.IsSection (C.covDeriv X s) :=
  fun _ ↦ rfl

theorem covDeriv_snd (X : M → TangentBundle E M) (s : M → V.TotalSpace) (x : M) :
    (show F from (C.covDeriv X s x).2) =
      localCovDerivB (C.Γ (𝒰.indexAt x)) (localRep (𝒰.chart (𝒰.indexAt x)) X)
        (V.localRep (𝒰.indexAt x) s) ((𝒰.chart (𝒰.indexAt x)).1 x) :=
  rfl

/-- **The covariant derivative does not depend on the trivialization**: in every trivialization
`j`, the local representative of `∇_X s` is `dsⱼ · Xⱼ − Γⱼ(Xⱼ, sⱼ)`. -/
theorem localRep_covDeriv {X : M → TangentBundle E M} {s : M → V.TotalSpace}
    (hXv : IsVectorField X) (hsv : V.IsSection s) (hs : ContMDiffMB E (E × F) 1 s)
    (j : ι) {y : E} (hy : y ∈ 𝒰.domain j) :
    V.localRep j (C.covDeriv X s) y =
      localCovDerivB (C.Γ j) (localRep (𝒰.chart j) X) (V.localRep j s) y := by
  set x := (𝒰.chart j).1.symm y
  set i := 𝒰.indexAt x
  have hxi : x ∈ 𝒰.baseSet i := 𝒰.mem_baseSet_at x
  set T := 𝒰.transDomain i j
  have hT : IsOpen T := 𝒰.isOpen_transDomain i j
  have hmaps : MapsTo (𝒰.trans i j) T (𝒰.domain j) := fun z hz ↦
    𝒰.transDomain_subset_domain j i (𝒰.mapsTo_trans i j hz)
  have hix : (𝒰.chart i).1 x ∈ T := 𝒰.chart_mem_transDomain hxi hy.2
  have hτx : 𝒰.trans i j ((𝒰.chart i).1 x) = y := by
    simp only [TrivializationCover.trans, Function.comp_apply,
      (𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hxi), x, (𝒰.chart j).1.right_inv hy.1]
  have hXrel := localRep_transition hXv (𝒰.chart i) (𝒰.chart j) hix.1
    (𝒰.baseSet_subset j hix.2.2)
  have htrans := localCovDerivB_transition
    (G := fun z ξ ↦ V.coordChange i j ((𝒰.chart i).1.symm z) ξ)
    hT hT (𝒰.isOpen_domain j) subset_rfl (𝒰.smoothMBOn_trans i j 1) hmaps (V.smooth i j 1)
    (fun _ hz ↦ V.map_add i j _ hz.2) (fun _ hz ↦ V.map_smul i j _ hz.2)
    ((V.contDiffMBOn_localRep hsv hs i).mono (𝒰.transDomain_subset_domain i j))
    (V.contDiffMBOn_localRep hsv hs j) (C.transition i j) hix hXrel
    (fun z hz ↦ V.localRep_transition hsv i j hz)
  rw [hτx] at htrans
  rw [htrans, ← hτx, V.localRep_transition (isSection_covDeriv C X s) i j hix]
  congr 1
  exact V.localRep_indexAt (isSection_covDeriv C X s) x

/-- The curvature `R(X, Y) s = ∇_X ∇_Y s − ∇_Y ∇_X s − ∇_[X,Y] s` at `x`, as a vector of the
fiber in the chosen trivialization at `x`. -/
def curvature (X Y : M → TangentBundle E M) (s : M → V.TotalSpace) (x : M) : F :=
  (show F from (C.covDeriv X (C.covDeriv Y s) x).2) -
    (show F from (C.covDeriv Y (C.covDeriv X s) x).2) -
    (show F from (C.covDeriv (lieBracket X Y) s x).2)

/-- **The curvature is tensorial**: for `C²` fields and sections, `R(X, Y) s` at `x` is the
curvature form of the chosen trivialization at `x`, evaluated at the values of `X`, `Y`, `s` at
`x`. -/
theorem curvature_eq {X Y : M → TangentBundle E M} {s : M → V.TotalSpace}
    (hXv : IsVectorField X) (hYv : IsVectorField Y) (hsv : V.IsSection s)
    (hX : ContMDiffMB E (E × E) 2 X) (hY : ContMDiffMB E (E × E) 2 Y)
    (hs : ContMDiffMB E (E × F) 2 s) (x : M) :
    C.curvature X Y s x =
      bundleCurv (C.Γ (𝒰.indexAt x)) ((𝒰.chart (𝒰.indexAt x)).1 x)
        (localRep (𝒰.chart (𝒰.indexAt x)) X ((𝒰.chart (𝒰.indexAt x)).1 x))
        (localRep (𝒰.chart (𝒰.indexAt x)) Y ((𝒰.chart (𝒰.indexAt x)).1 x))
        (V.localRep (𝒰.indexAt x) s ((𝒰.chart (𝒰.indexAt x)).1 x)) := by
  set i := 𝒰.indexAt x
  have hx : (𝒰.chart i).1 x ∈ 𝒰.domain i := 𝒰.chart_mem_domain (𝒰.mem_baseSet_at x)
  have hX1 := hX.of_le' (by norm_num : 1 ≤ 2)
  have hY1 := hY.of_le' (by norm_num : 1 ≤ 2)
  have hs1 := hs.of_le' (by norm_num : 1 ≤ 2)
  have hev : ∀ {A : M → TangentBundle E M}, IsVectorField A →
      V.localRep i (C.covDeriv A s) =ᶠ[𝓝 ((𝒰.chart i).1 x)]
        localCovDerivB (C.Γ i) (localRep (𝒰.chart i) A) (V.localRep i s) :=
    fun hAv ↦ Filter.eventuallyEq_of_mem ((𝒰.isOpen_domain i).mem_nhds hx)
      fun _ hy ↦ C.localRep_covDeriv hAv hsv hs1 i hy
  have hbr : localRep (𝒰.chart i) (lieBracket X Y) ((𝒰.chart i).1 x) =
      localBracket (localRep (𝒰.chart i) X) (localRep (𝒰.chart i) Y) ((𝒰.chart i).1 x) :=
    localRep_lieBracket hXv hYv hX1 hY1 (𝒰.chart i) hx.1
  unfold curvature
  rw [covDeriv_snd, covDeriv_snd, covDeriv_snd]
  change localCovDerivB (C.Γ i) (localRep (𝒰.chart i) X) (V.localRep i (C.covDeriv Y s))
        ((𝒰.chart i).1 x) -
      localCovDerivB (C.Γ i) (localRep (𝒰.chart i) Y) (V.localRep i (C.covDeriv X s))
        ((𝒰.chart i).1 x) -
      localCovDerivB (C.Γ i) (localRep (𝒰.chart i) (lieBracket X Y)) (V.localRep i s)
        ((𝒰.chart i).1 x) = _
  rw [localCovDerivB_congr_right (hev hYv), localCovDerivB_congr_right (hev hXv)]
  have e3 : localCovDerivB (C.Γ i) (localRep (𝒰.chart i) (lieBracket X Y)) (V.localRep i s)
        ((𝒰.chart i).1 x) =
      localCovDerivB (C.Γ i) (localBracket (localRep (𝒰.chart i) X) (localRep (𝒰.chart i) Y))
        (V.localRep i s) ((𝒰.chart i).1 x) := by
    simp only [localCovDerivB, hbr]
  rw [e3]
  have hd : ∀ {A : M → TangentBundle E M}, IsVectorField A → ContMDiffMB E (E × E) 2 A →
      ContDiffMBOn 2 (localRep (𝒰.chart i) A) (𝒰.domain i) :=
    fun hAv hA ↦ (contDiffMBOn_localRep hAv hA (𝒰.chart i)).mono inter_subset_left
  exact (C.isLocalSymbol i).localCovDerivB_curv (𝒰.isOpen_domain i) (hd hXv hX) (hd hYv hY)
    (V.contDiffMBOn_localRep hsv hs i) hx

end BundleConnection

end LocallyConvex.Manifolds
