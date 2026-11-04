/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Metric.Finsler
import LCManifolds.TangentMap

/-!
# Lifting curves versus lifting neighborhoods

References: G. Larotonda, *The metric geometry of infinite dimensional Lie groups and their
homogeneous spaces*, Forum Math. 31 (2019), §3, Lemma 3.19.

This file explains where the two continuity conditions of `LCManifolds.Metric.Finsler` come
from. Let `π : N → M` be a `C¹` map (written `pr` in the code, since `π` denotes the real
number) and `μ` a field of Finsler seminorms on `M`. Typically `μ` is defined through `π`, as a
quotient metric
`μ(w) = inf {μ_N(v) : Tπ v = w}`, and what one controls is the function `μ ∘ Tπ` on `TN`.

* **Lifting curves gives a Finsler length structure**
  (`FinslerSeminormField.toFinslerLengthStructureOfLifts`). If every `C¹` curve in `M` has, near
  each time, a `C¹` lift `Γ` to `N` (`π ∘ Γ = γ`), and `μ ∘ Tπ` is continuous along the velocities
  of `C¹` curves of `N`, then `μ` is a Finsler length structure. The point is the chain rule
  `γ̇ = Tπ(Γ̇)` (`tangentMap_velocity`).
* **Lifting neighborhoods gives a Finsler metric**
  (`FinslerSeminormField.toFinslerMetricOfIsQuotientMap`). If `Tπ : TN → TM` is a quotient map
  and `μ ∘ Tπ` is continuous on `TN`, then `μ` is continuous on `TM`: it is a Finsler metric.

**Submersions.** For Banach manifolds, a submersion (surjective differential with complemented
kernel) has local smooth sections through every point, by the inverse function theorem. Then
`Tπ` is open, hence a quotient map, and curves lift; both conditions hold and the two notions
agree for quotient metrics. On locally convex manifolds there is no inverse function theorem:
curves may lift (for instance through the exponential map of a Lie group, or by solving a
differential equation along the curve) while neighborhoods do not. This is the situation of
homogeneous spaces `G/K` of infinite dimensional Lie groups, where the quotient metric is a
Finsler length structure, and it is a Finsler metric when `π_*` is a quotient map (Larotonda,
Lemma 3.19; there the continuity of `μ ∘ Tπ` comes from the uniformity of the metric of `G`).

The difference between the two notions is not specific to infinite dimensions: on `ℝ²` there is a
Finsler length structure that is not a Finsler metric (`LCManifolds.Examples.FinslerCusp`).
-/

open Set Filter Bundle
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

/-- The velocity at `t` only depends on the germ of the curve at `t`. -/
theorem velocity_congr {γ₁ γ₂ : ℝ → M} {t : ℝ} (h : γ₁ =ᶠ[𝓝 t] γ₂) :
    velocity E γ₁ t = velocity E γ₂ t := by
  have ht : γ₁ t = γ₂ t := h.self_of_nhds
  have hd : dMB (chartAt E (γ₂ t) ∘ γ₁) (t, 1) = dMB (chartAt E (γ₂ t) ∘ γ₂) (t, 1) :=
    dMB_congr_of_eventuallyEq (h.fun_comp _) 1
  unfold velocity
  rw [ht, hd]

/-- **The chain rule for velocities**: `Tπ (Γ̇ t) = (π ∘ Γ)˙ t`. -/
theorem tangentMap_velocity {pr : N → M} (hpr : ContMDiffMB F E 1 pr) {Γ : ℝ → N}
    (hΓ : IsCkCurve F 1 Γ) (t : ℝ) :
    tangentMap F E pr (velocity F Γ t) = velocity E (pr ∘ Γ) t := by
  set c := chartAt F (Γ t)
  set c' := chartAt E (pr (Γ t))
  have hprc : Continuous pr := continuousOn_univ.mp hpr.1
  set O := Γ ⁻¹' (c.source ∩ pr ⁻¹' c'.source)
  have hO : IsOpen O := (c.open_source.inter (c'.open_source.preimage hprc)).preimage hΓ.1
  have htO : t ∈ O := ⟨mem_chart_source F _, mem_chart_source E _⟩
  set D := chartDomain pr univ c c'
  have hD : IsOpen D := isOpen_chartDomain isOpen_univ hpr.1 c c'
  have hh : ContDiffMBOn 1 (c' ∘ pr ∘ c.symm) D := hpr.2 (Γ t) (mem_univ _)
  have hcΓ : ContDiffMBOn 1 (c ∘ Γ) O :=
    (hΓ.2 ⟨c, chart_mem_atlas F _⟩).mono fun s hs ↦ hs.1
  have hmaps : MapsTo (c ∘ Γ) O D := fun s hs ↦
    ⟨c.map_source hs.1, by simp [c.left_inv hs.1, hs.2]⟩
  have hev : c' ∘ (pr ∘ Γ) =ᶠ[𝓝 t] (c' ∘ pr ∘ c.symm) ∘ (c ∘ Γ) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds htO) fun s hs ↦ by
      simp [c.left_inv hs.1]
  have key : dMB (c' ∘ pr ∘ c.symm) (c (Γ t), dMB (c ∘ Γ) (t, 1)) =
      dMB (c' ∘ (pr ∘ Γ)) (t, 1) := by
    rw [dMB_congr_of_eventuallyEq hev, ContDiffMBOn.dMB_comp hD hh hcΓ hmaps htO 1]
    rfl
  exact congrArg (fun v : E ↦ (⟨pr (Γ t), v⟩ : TangentBundle E M)) key

namespace FinslerSeminormField

/-- **Lifting curves gives a Finsler length structure.** Let `π : N → M` be `C¹`. If every `C¹`
curve of `M` has, near each time, a `C¹` lift to `N`, and `μ ∘ Tπ` is continuous along the
velocities of `C¹` curves of `N`, then the field `μ` is a Finsler length structure. Nothing is
claimed about continuity on `TM`. -/
def toFinslerLengthStructureOfLifts (μ : FinslerSeminormField E M) {pr : N → M}
    (hpr : ContMDiffMB F E 1 pr)
    (hlift : ∀ γ : ℝ → M, IsCkCurve E 1 γ → ∀ t₀ : ℝ,
      ∃ Γ : ℝ → N, IsCkCurve F 1 Γ ∧ ∀ᶠ t in 𝓝 t₀, pr (Γ t) = γ t)
    (hcont : ∀ Γ : ℝ → N, IsCkCurve F 1 Γ →
      Continuous fun t ↦ μ.toFun (tangentMap F E pr (velocity F Γ t))) :
    FinslerLengthStructure E M where
  toFinslerSeminormField := μ
  continuous_velocity' γ hγ := by
    rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨Γ, hΓ, hev⟩ := hlift γ hγ t₀
    have hev' : ∀ᶠ t in 𝓝 t₀, μ.toFun (velocity E γ t) =
        μ.toFun (tangentMap F E pr (velocity F Γ t)) := by
      filter_upwards [hev.eventually_nhds] with t ht
      have hgerm : γ =ᶠ[𝓝 t] pr ∘ Γ := ht.mono fun s hs ↦ hs.symm
      rw [velocity_congr hgerm, tangentMap_velocity hpr hΓ t]
    exact ((hcont Γ hΓ).continuousAt).congr (hev'.mono fun t ht ↦ ht.symm)

/-- **Lifting neighborhoods gives a Finsler metric.** If `Tπ : TN → TM` is a quotient map and
`μ ∘ Tπ` is continuous on `TN`, then `μ` is continuous on `TM`: it is a Finsler metric. -/
def toFinslerMetricOfIsQuotientMap (μ : FinslerSeminormField E M) {pr : N → M}
    (hq : Topology.IsQuotientMap (tangentMap F E pr))
    (hcont : Continuous (μ.toFun ∘ tangentMap F E pr)) : FinslerMetric E M where
  toFinslerSeminormField := μ
  continuous' := hq.continuous_iff.mpr hcont

end FinslerSeminormField

end LCManifolds
