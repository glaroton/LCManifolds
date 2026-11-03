/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.TangentBundle

/-!
# The tangent map

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, §I.3; H. Glöckner,
K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Ch. 3.

For a `C^1` map `f : M → N` between manifolds modeled on `E` and `F`, the tangent map
`Tf : TM → TN` sends a tangent vector `v` at `x`, written in the preferred chart `c` at `x`, to
the vector `d(c' ∘ f ∘ c⁻¹)(c x) v` at `f x`, written in the preferred chart `c'` at `f x`. We
show:

* `dMB_chart_comp`, `dMB_comp_chart`: derivatives of local representatives transform under
  changes of charts by the derivatives of the transition maps (the chain rule);
* `tangentMap_chart`: in the charts of the tangent bundles, `Tf` reads
  `(y, w) ↦ (h y, dh(y) w)`, where `h` is the local representative of `f`;
* `ContMDiffMB.tangentMap`: if `f` is `C^(k+1)`, then `Tf` is `C^k`;
* `tangentMap_comp`, `tangentMap_id`: functoriality, `T(g ∘ f) = Tg ∘ Tf` and `T id = id`.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

section Calculus

variable {E F G : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-- The chain rule for a map that agrees with a composition near the point. -/
theorem dMB_eq_comp_of_eventuallyEq {g₀ : E → F} {g₁ : F → G} {h : E → G} {U : Set E}
    {V : Set F} (hV : IsOpen V) (hg₁ : ContDiffMBOn 1 g₁ V) (hg₀ : ContDiffMBOn 1 g₀ U)
    (hUV : MapsTo g₀ U V) {y : E} (hy : y ∈ U) (hh : h =ᶠ[𝓝 y] g₁ ∘ g₀) (v : E) :
    dMB h (y, v) = dMB g₁ (g₀ y, dMB g₀ (y, v)) := by
  rw [dMB_congr_of_eventuallyEq hh]
  exact ContDiffMBOn.dMB_comp hV hg₁ hg₀ hUV hy v

end Calculus

section Charts

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]
  {f : M → N}

/-- Changing the chart of the source: `d(e' f e₂⁻¹)(e₂ x) ∘ d(e₂ e₁⁻¹)(e₁ x) = d(e' f e₁⁻¹)(e₁ x)`. -/
theorem dMB_chart_comp (hf : ContMDiffMB E F 1 f) {e₁ e₂ : OpenPartialHomeomorph M E}
    (he₁ : e₁ ∈ atlas E M) (he₂ : e₂ ∈ atlas E M) {e' : OpenPartialHomeomorph N F}
    (he' : e' ∈ atlas F N) {x : M} (hx₁ : x ∈ e₁.source) (hx₂ : x ∈ e₂.source)
    (hfx : f x ∈ e'.source) (v : E) :
    dMB (e' ∘ f ∘ e₂.symm) (e₂ x, dMB (e₂ ∘ e₁.symm) (e₁ x, v)) =
      dMB (e' ∘ f ∘ e₁.symm) (e₁ x, v) := by
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  set U := e₁.target ∩ e₁.symm ⁻¹' (e₂.source ∩ f ⁻¹' e'.source)
  have hU : IsOpen U :=
    e₁.isOpen_inter_preimage_symm (e₂.open_source.inter (e'.open_source.preimage hfc))
  have hxU : e₁ x ∈ U := ⟨e₁.map_source hx₁, by simp [e₁.left_inv hx₁, hx₂, hfx]⟩
  have hg₀ : ContDiffMBOn 1 (e₂ ∘ e₁.symm) U :=
    (smoothMBOn_transition he₁ he₂ 1).mono fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hg₁ : ContDiffMBOn 1 (e' ∘ f ∘ e₂.symm) (chartDomain f univ e₂ e') :=
    hf.contDiffMBOn_chart isOpen_univ he₂ he'
  have hmaps : MapsTo (e₂ ∘ e₁.symm) U (chartDomain f univ e₂ e') := by
    rintro z ⟨-, hz₂, hzf⟩
    exact ⟨e₂.map_source hz₂, by simp [e₂.left_inv hz₂, hzf]⟩
  have hh : e' ∘ f ∘ e₁.symm =ᶠ[𝓝 (e₁ x)] (e' ∘ f ∘ e₂.symm) ∘ (e₂ ∘ e₁.symm) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun z hz ↦ by
      simp [e₂.left_inv hz.2.1]
  rw [dMB_eq_comp_of_eventuallyEq (isOpen_chartDomain isOpen_univ hf.1 e₂ e') hg₁ hg₀ hmaps
    hxU hh v]
  simp [e₁.left_inv hx₁]

/-- Changing the chart of the target: `d(e₂' e₁'⁻¹)(e₁' f x) ∘ d(e₁' f e⁻¹)(e x) = d(e₂' f e⁻¹)(e x)`. -/
theorem dMB_comp_chart (hf : ContMDiffMB E F 1 f) {e : OpenPartialHomeomorph M E}
    (he : e ∈ atlas E M) {e₁' e₂' : OpenPartialHomeomorph N F} (he₁' : e₁' ∈ atlas F N)
    (he₂' : e₂' ∈ atlas F N) {x : M} (hx : x ∈ e.source) (hfx₁ : f x ∈ e₁'.source)
    (hfx₂ : f x ∈ e₂'.source) (v : E) :
    dMB (e₂' ∘ e₁'.symm) (e₁' (f x), dMB (e₁' ∘ f ∘ e.symm) (e x, v)) =
      dMB (e₂' ∘ f ∘ e.symm) (e x, v) := by
  have hfc : Continuous f := continuousOn_univ.mp hf.1
  set U := e.target ∩ e.symm ⁻¹' (f ⁻¹' (e₁'.source ∩ e₂'.source))
  have hU : IsOpen U :=
    e.isOpen_inter_preimage_symm ((e₁'.open_source.inter e₂'.open_source).preimage hfc)
  have hxU : e x ∈ U := ⟨e.map_source hx, by simp [e.left_inv hx, hfx₁, hfx₂]⟩
  have hg₀ : ContDiffMBOn 1 (e₁' ∘ f ∘ e.symm) U :=
    (hf.contDiffMBOn_chart isOpen_univ he he₁').mono fun z hz ↦ ⟨hz.1, mem_univ _, hz.2.1⟩
  have hg₁ : ContDiffMBOn 1 (e₂' ∘ e₁'.symm) (e₁'.target ∩ e₁'.symm ⁻¹' e₂'.source) :=
    smoothMBOn_transition he₁' he₂' 1
  have hmaps : MapsTo (e₁' ∘ f ∘ e.symm) U (e₁'.target ∩ e₁'.symm ⁻¹' e₂'.source) := by
    rintro z ⟨-, hz₁, hz₂⟩
    exact ⟨e₁'.map_source hz₁, by simp [e₁'.left_inv hz₁, hz₂]⟩
  have hh : e₂' ∘ f ∘ e.symm =ᶠ[𝓝 (e x)] (e₂' ∘ e₁'.symm) ∘ (e₁' ∘ f ∘ e.symm) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun z hz ↦ by
      simp [e₁'.left_inv hz.2.1]
  rw [dMB_eq_comp_of_eventuallyEq (e₁'.isOpen_inter_preimage_symm e₂'.open_source) hg₁ hg₀
    hmaps hxU hh v]
  simp [e.left_inv hx]

end Charts

end LCManifolds
