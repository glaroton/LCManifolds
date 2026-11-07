/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.VectorBundle
import LocallyConvexAnalysis.OperatorValued
import LocallyConvexAnalysis.Rules

/-!
# Hom bundles, dual bundles and the cotangent bundle

Let `V₁`, `V₂` be vector bundles over `M` (modeled on a locally convex space `E`) with **normed**
fibers `F₁`, `F₂`. The bundle `Hom(V₁, V₂)` has fiber `L(F₁, F₂)` with the operator norm, and
coordinate changes `A ↦ g₂(x) ∘ A ∘ g₁(x)⁻¹` (`homCore`). The dual bundle is
`V' = Hom(V, ℝ)` (`dualCore`), and for a normed model `E` the cotangent bundle is
`T*M = (TM)'` (`cotangentCore`).

**The infinite-dimensional subtleties.**
* If a fiber is not normable, `L(F₁, F₂)` carries no vector topology for which the evaluation
  is continuous (Maissen), so `Hom(V₁, V₂)` and `V'` are not available in this generality.
* Even for normed fibers, the smoothness of the coordinate changes of `Hom(V₁, V₂)` is not
  formal: the coordinate changes of `V₁`, `V₂` are only assumed jointly smooth,
  `(y, ξ) ↦ g(y) ξ`, and we need `y ↦ g(y)` to be smooth for the **operator norm**. This is
  `contDiffMBOn_of_unc_clm` in lc-analysis, which holds for any locally convex base `E`.
* For a normed model `E`, `T*M` has fiber `E'`; it is a vector bundle in this sense with no
  completeness or reflexivity assumption.

No completeness is assumed.
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

namespace MBVectorBundleCore

section Normed

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (V : MBVectorBundleCore 𝒰 F)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- On the overlap, the coordinate change is continuous. -/
theorem continuous_coordChange (i j : ι) {x : M} (hx : x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j) :
    Continuous (V.coordChange i j x) := by
  have hc : ContinuousOn (fun p : E × F ↦ V.coordChange i j ((𝒰.chart i).1.symm p.1) p.2)
      (𝒰.transDomain i j ×ˢ univ) := (V.smooth i j 0 : ContDiffMBOn 0 _ _)
  have hy : (𝒰.chart i).1 x ∈ 𝒰.transDomain i j := 𝒰.chart_mem_transDomain hx.1 hx.2
  have := hc.comp_continuous (f := fun ξ : F ↦ ((𝒰.chart i).1 x, ξ)) (by fun_prop)
    fun ξ ↦ ⟨hy, mem_univ _⟩
  have e : (fun p : E × F ↦ V.coordChange i j ((𝒰.chart i).1.symm p.1) p.2) ∘
      (fun ξ : F ↦ ((𝒰.chart i).1 x, ξ)) = V.coordChange i j x := by
    funext ξ
    simp [(𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hx.1)]
  rwa [e] at this

open scoped Classical in
/-- The coordinate change as a continuous linear operator (zero off the overlap). -/
def coordCLM (i j : ι) (x : M) : F →L[ℝ] F :=
  if hx : x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j then
    ⟨V.coordChangeLinear i j hx, V.continuous_coordChange i j hx⟩
  else 0

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem coordCLM_apply (i j : ι) {x : M} (hx : x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j) (ξ : F) :
    V.coordCLM i j x ξ = V.coordChange i j x ξ := by
  simp [coordCLM, hx, coordChangeLinear]

omit [MBManifold E M] in
/-- **The coordinate changes are smooth for the operator norm**: `y ↦ g_{ij}(φᵢ⁻¹ y)` is smooth
as a map into `L(F)`. -/
theorem smoothMBOn_coordCLM (i j : ι) :
    SmoothMBOn (fun y ↦ V.coordCLM i j ((𝒰.chart i).1.symm y)) (𝒰.transDomain i j) := by
  have hU := 𝒰.isOpen_transDomain i j
  intro k
  refine contDiffMBOn_of_unc_clm k hU ?_
  refine ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) (fun p hp ↦ ?_) (V.smooth i j (k + 1))
  exact (V.coordCLM_apply i j hp.1.2 p.2).symm

/-- The inverse coordinate changes `y ↦ g_{ji}(φᵢ⁻¹ y)` are smooth for the operator norm. -/
theorem smoothMBOn_coordCLM_symm (i j : ι) :
    SmoothMBOn (fun y ↦ V.coordCLM j i ((𝒰.chart i).1.symm y)) (𝒰.transDomain i j) := by
  have hU := 𝒰.isOpen_transDomain i j
  have hτ := 𝒰.smoothMBOn_trans i j
  intro k
  refine contDiffMBOn_of_unc_clm k hU ?_
  have hc := ContDiffMBOn.comp
    (g := fun p : E × F ↦ V.coordChange j i ((𝒰.chart j).1.symm p.1) p.2)
    (f := fun p : E × F ↦ (𝒰.trans i j p.1, p.2)) (hU.prod isOpen_univ)
    ((𝒰.isOpen_transDomain j i).prod isOpen_univ) (V.smooth j i (k + 1))
    (((hτ (k + 1)).comp (hU.prod isOpen_univ) hU
      ((ContinuousLinearMap.fst ℝ E F).contDiffMBOn _ _) fun p hp ↦ hp.1).prodMk
      (hU.prod isOpen_univ) ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn _ _))
    fun p hp ↦ ⟨𝒰.mapsTo_trans i j hp.1, mem_univ _⟩
  refine ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) (fun p hp ↦ ?_) hc
  rw [V.coordCLM_apply j i ⟨hp.1.2.2, hp.1.2.1⟩]
  simp [𝒰.symm_trans hp.1]

end Normed

end MBVectorBundleCore

/-! ### The Hom bundle -/

section Hom

variable {F₁ F₂ : Type u} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- Composition of operators, as a continuous bilinear map. -/
private def compBilin (G₁ G₂ G₃ : Type u) [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [NormedAddCommGroup G₃] [NormedSpace ℝ G₃] :
    (G₂ →L[ℝ] G₃) →ₗ[ℝ] (G₁ →L[ℝ] G₂) →ₗ[ℝ] (G₁ →L[ℝ] G₃) :=
  LinearMap.mk₂ ℝ (fun S A ↦ S.comp A) (fun _ _ _ ↦ ContinuousLinearMap.add_comp _ _ _)
    (fun _ _ _ ↦ ContinuousLinearMap.smul_comp _ _ _)
    (fun _ _ _ ↦ ContinuousLinearMap.comp_add _ _ _)
    (fun _ _ _ ↦ ContinuousLinearMap.comp_smul _ _ _)

private theorem continuous_compBilin (G₁ G₂ G₃ : Type u) [NormedAddCommGroup G₁]
    [NormedSpace ℝ G₁] [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [NormedAddCommGroup G₃]
    [NormedSpace ℝ G₃] :
    Continuous fun p : (G₂ →L[ℝ] G₃) × (G₁ →L[ℝ] G₂) ↦ compBilin G₁ G₂ G₃ p.1 p.2 :=
  (ContinuousLinearMap.compL ℝ G₁ G₂ G₃).continuous₂

/-- **The Hom bundle** `Hom(V₁, V₂)`, with fiber `L(F₁, F₂)` (operator norm) and coordinate
changes `A ↦ g₂(x) ∘ A ∘ g₁(x)⁻¹`. -/
def homCore (V₁ : MBVectorBundleCore 𝒰 F₁) (V₂ : MBVectorBundleCore 𝒰 F₂) :
    MBVectorBundleCore 𝒰 (F₁ →L[ℝ] F₂) where
  coordChange i j x A := (V₂.coordCLM i j x).comp (A.comp (V₁.coordCLM j i x))
  map_add i j x _ A B := by
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul i j x _ c A := by
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  coordChange_self i x hx A := by
    ext ξ
    have hxx : x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet i := ⟨hx, hx⟩
    simp [V₁.coordCLM_apply i i hxx, V₂.coordCLM_apply i i hxx, V₁.coordChange_self i x hx,
      V₂.coordChange_self i x hx]
  coordChange_comp i j k x hx A := by
    ext ξ
    obtain ⟨⟨hi, hj⟩, hk⟩ := hx
    simp only [ContinuousLinearMap.comp_apply]
    rw [V₁.coordCLM_apply k j ⟨hk, hj⟩, V₁.coordCLM_apply j i ⟨hj, hi⟩,
      V₁.coordCLM_apply k i ⟨hk, hi⟩, V₂.coordCLM_apply i j ⟨hi, hj⟩,
      V₂.coordCLM_apply j k ⟨hj, hk⟩, V₂.coordCLM_apply i k ⟨hi, hk⟩,
      V₁.coordChange_comp k j i x ⟨⟨hk, hj⟩, hi⟩, V₂.coordChange_comp i j k x ⟨⟨hi, hj⟩, hk⟩]
  smooth i j k := by
    have hU := 𝒰.isOpen_transDomain i j
    have hUU : IsOpen (𝒰.transDomain i j ×ˢ (univ : Set (F₁ →L[ℝ] F₂))) :=
      hU.prod isOpen_univ
    have h₂ : ContDiffMBOn k (fun p : E × (F₁ →L[ℝ] F₂) ↦ V₂.coordCLM i j ((𝒰.chart i).1.symm p.1))
        (𝒰.transDomain i j ×ˢ univ) :=
      (V₂.smoothMBOn_coordCLM i j k).comp hUU hU
        ((ContinuousLinearMap.fst ℝ E (F₁ →L[ℝ] F₂)).contDiffMBOn _ _) fun p hp ↦ hp.1
    have h₁ : ContDiffMBOn k (fun p : E × (F₁ →L[ℝ] F₂) ↦ V₁.coordCLM j i ((𝒰.chart i).1.symm p.1))
        (𝒰.transDomain i j ×ˢ univ) :=
      (V₁.smoothMBOn_coordCLM_symm i j k).comp hUU hU
        ((ContinuousLinearMap.fst ℝ E (F₁ →L[ℝ] F₂)).contDiffMBOn _ _) fun p hp ↦ hp.1
    have hA : ContDiffMBOn k (fun p : E × (F₁ →L[ℝ] F₂) ↦ p.2)
        (𝒰.transDomain i j ×ˢ univ) :=
      (ContinuousLinearMap.snd ℝ E (F₁ →L[ℝ] F₂)).contDiffMBOn _ _
    have hAg := ContDiffMBOn.bilin (compBilin F₁ F₁ F₂) (continuous_compBilin F₁ F₁ F₂) hUU hA h₁
    exact ContDiffMBOn.bilin (compBilin F₁ F₂ F₂) (continuous_compBilin F₁ F₂ F₂) hUU h₂ hAg

/-- On the overlap, the coordinate change of `Hom(V₁, V₂)` is `A ↦ g₂ ∘ A ∘ g₁⁻¹`. -/
theorem homCore_coordChange_apply (V₁ : MBVectorBundleCore 𝒰 F₁)
    (V₂ : MBVectorBundleCore 𝒰 F₂) (i j : ι) {x : M}
    (hx : x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j) (A : F₁ →L[ℝ] F₂) (ξ : F₁) :
    (homCore V₁ V₂).coordChange i j x A ξ =
      V₂.coordChange i j x (A (V₁.coordChange j i x ξ)) := by
  change V₂.coordCLM i j x (A (V₁.coordCLM j i x ξ)) = _
  rw [V₁.coordCLM_apply j i ⟨hx.2, hx.1⟩, V₂.coordCLM_apply i j hx]

end Hom

/-! ### The trivial bundle, the dual bundle and the cotangent bundle -/

variable (𝒰) in
/-- The trivial bundle `M × F`, trivialized over `𝒰`. -/
def trivialCore (F : Type u) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] :
    MBVectorBundleCore 𝒰 F where
  coordChange _ _ _ ξ := ξ
  map_add _ _ _ _ _ _ := rfl
  map_smul _ _ _ _ _ _ := rfl
  coordChange_self _ _ _ _ := rfl
  coordChange_comp _ _ _ _ _ _ := rfl
  smooth _ _ k := (ContinuousLinearMap.snd ℝ E F).contDiffMBOn k _

section Dual

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {𝒰 : TrivializationCover E M ι}

/-- **The dual bundle** `V' = Hom(V, ℝ)` of a bundle with normed fiber, with fiber `F'`
(operator norm). (Real-valued fibers require the model to live in `Type`.) -/
def dualCore {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (V : MBVectorBundleCore 𝒰 F) :
    MBVectorBundleCore 𝒰 (F →L[ℝ] ℝ) :=
  homCore V (trivialCore 𝒰 ℝ)

end Dual

section Cotangent

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

variable (E M) in
/-- **The cotangent bundle** `T*M = (TM)'` of a manifold modeled on a normed space, with fiber
`E'`. No completeness or reflexivity is needed. -/
def cotangentCore : MBVectorBundleCore (atlasCover E M) (E →L[ℝ] ℝ) :=
  dualCore (tangentMBCore E M)

end Cotangent

end LocallyConvex.Manifolds
