/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.BundleSection

/-!
# Bundle metrics and metric connections

A **bundle metric** on a vector bundle `V` with fiber `F` is given in the trivialization over each
chart `i` by a smooth family of symmetric bilinear forms `hᵢ(y) : F × F → ℝ`, invariant under the
coordinate changes: `hⱼ(τ y)(g ξ, g η) = hᵢ(y)(ξ, η)` (`BundleMetric`). We do not ask for
positivity or nondegeneracy in the definitions: positive definite forms give (weak) Riemannian
bundle metrics (`BundleMetric.IsPositive`), and indefinite ones are allowed.

A connection is **metric** if `∂_a h(ξ, η) = −h(Γ(a, ξ), η) − h(ξ, Γ(a, η))` in every
trivialization (`BundleConnection.IsMetric`); equivalently, `X h(s, t) = h(∇_X s, t) +
h(s, ∇_X t)` for sections (`localCompat_sections`).

**An infinite-dimensional subtlety.** For a weak metric (one whose flat map `F → F'` is only
injective) a metric connection need not exist, and even the Levi-Civita connection of a weak
Riemannian metric on `TM` may fail to exist. The results below are statements *about* metric
connections, and do not assume existence.

## Main results

* `localCompat_sections`: compatibility with the metric, for sections;
* `IsLocalBundleMetric.bundleCurv_skew` and `BundleConnection.IsMetric.curvLoc_skew`: **the
  curvature of a metric connection is skew-adjoint**,
  `h(Ω(u, v) ξ, η) + h(ξ, Ω(u, v) η) = 0`. The proof differentiates the compatibility condition
  twice and uses the symmetry of second derivatives;
* `BundleConnection.IsMetric.curvature_skew`: the same for the global curvature `R(X, Y)`.

No completeness of `E` or `F` is assumed.
-/

open Set Function Filter
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

section Local

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- A smooth family of symmetric bilinear forms `h(y) : F × F → ℝ` on an open set `U ⊆ E`. -/
structure IsLocalBundleMetric (h : E → F → F → ℝ) (U : Set E) : Prop where
  smooth : SmoothMBOn (fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2) (U ×ˢ univ)
  add_left : ∀ y ξ ξ' η, h y (ξ + ξ') η = h y ξ η + h y ξ' η
  smul_left : ∀ y (c : ℝ) ξ η, h y (c • ξ) η = c • h y ξ η
  symm : ∀ y ξ η, h y ξ η = h y η ξ

/-- The derivative of the metric in the base point: `∂_b h(y)(ξ, η)`. -/
def metricD (h : E → F → F → ℝ) (y b : E) (ξ η : F) : ℝ :=
  dMB (fun z ↦ h z ξ η) (y, b)

/-- Compatibility of the symbols `Γ` with the metric `h` on `U`:
`∂_a h(ξ, η) = −h(Γ(a, ξ), η) − h(ξ, Γ(a, η))`. -/
def IsLocalCompatible (Γ : E → E → F → F) (h : E → F → F → ℝ) (U : Set E) : Prop :=
  ∀ y ∈ U, ∀ a ξ η, metricD h y a ξ η = -h y (Γ y a ξ) η - h y ξ (Γ y a η)

namespace IsLocalBundleMetric

variable {h : E → F → F → ℝ} {U : Set E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem add_right (hh : IsLocalBundleMetric h U) (y : E) (ξ η η' : F) :
    h y ξ (η + η') = h y ξ η + h y ξ η' := by
  rw [hh.symm, hh.add_left, hh.symm y η, hh.symm y η']

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem smul_right (hh : IsLocalBundleMetric h U) (y : E) (c : ℝ) (ξ η : F) :
    h y ξ (c • η) = c • h y ξ η := by
  rw [hh.symm, hh.smul_left, hh.symm y η]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem sub_left (hh : IsLocalBundleMetric h U) (y : E) (ξ ξ' η : F) :
    h y (ξ - ξ') η = h y ξ η - h y ξ' η := by
  rw [sub_eq_add_neg, hh.add_left, ← neg_one_smul ℝ ξ', hh.smul_left, smul_eq_mul, neg_one_mul,
    ← sub_eq_add_neg]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem sub_right (hh : IsLocalBundleMetric h U) (y : E) (ξ η η' : F) :
    h y ξ (η - η') = h y ξ η - h y ξ η' := by
  rw [hh.symm, hh.sub_left, hh.symm y η, hh.symm y η']

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem zero_right (hh : IsLocalBundleMetric h U) (y : E) (ξ : F) : h y ξ 0 = 0 := by
  have := hh.smul_right y 0 ξ 0
  rwa [zero_smul, zero_smul] at this

theorem mono (hh : IsLocalBundleMetric h U) {U' : Set E} (hU' : U' ⊆ U) :
    IsLocalBundleMetric h U' :=
  ⟨fun k ↦ (hh.smooth k).mono (prod_mono hU' subset_rfl), hh.add_left, hh.smul_left, hh.symm⟩

/-- Composition of the metric with smooth maps. -/
theorem contDiffMBOn_comp (hh : IsLocalBundleMetric h U) (hU : IsOpen U) {P Q : E → F} {k : ℕ}
    (hP : ContDiffMBOn k P U) (hQ : ContDiffMBOn k Q U) :
    ContDiffMBOn k (fun z ↦ h z (P z) (Q z)) U :=
  ContDiffMBOn.comp (g := fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2)
    (f := fun z ↦ (z, (P z, Q z))) hU (hU.prod isOpen_univ) (hh.smooth k)
    (((ContinuousLinearMap.id ℝ E).contDiffMBOn k U).prodMk hU (hP.prodMk hU hQ))
    fun _ hz ↦ ⟨hz, mem_univ _⟩

omit [LocallyConvexSpace ℝ F] in
/-- **Product rule for the metric**: the derivative of `z ↦ h(z)(P z, Q z)` is
`∂_b h(P y, Q y) + h(dP(y) b, Q y) + h(P y, dQ(y) b)`. -/
theorem dMB_apply (hh : IsLocalBundleMetric h U) (hU : IsOpen U) {P Q : E → F}
    (hP : ContDiffMBOn 1 P U) (hQ : ContDiffMBOn 1 Q U) {y : E} (hy : y ∈ U) (b : E) :
    dMB (fun z ↦ h z (P z) (Q z)) (y, b) =
      metricD h y b (P y) (Q y) + h y (dMB P (y, b)) (Q y) + h y (P y) (dMB Q (y, b)) := by
  have hUU : IsOpen (U ×ˢ (univ : Set (F × F))) := hU.prod isOpen_univ
  have hh1 : ContDiffMBOn 1 (fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2) (U ×ˢ univ) := hh.smooth 1
  have htrip : ContDiffMBOn 1 (fun z ↦ (z, (P z, Q z))) U :=
    ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU (hP.prodMk hU hQ)
  have hcomp := ContDiffMBOn.dMB_comp (g := fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2)
    (f := fun z ↦ (z, (P z, Q z))) hUU hh1 htrip (fun z hz ↦ ⟨hz, mem_univ _⟩) hy b
  have hdtrip : dMB (fun z ↦ (z, (P z, Q z))) (y, b) = (b, (dMB P (y, b), dMB Q (y, b))) :=
    (((ContinuousLinearMap.id ℝ E).hasDirDerivAt y b).prodMk
      ((hP.hasDirDerivAt hy b).prodMk (hQ.hasDirDerivAt hy b))).dMB_eq
  have hsplit : (b, (dMB P (y, b), dMB Q (y, b))) =
      ((b, ((0 : F), (0 : F))) + ((0 : E), (dMB P (y, b), (0 : F)))) +
        ((0 : E), ((0 : F), dMB Q (y, b))) := by simp
  have hp : (y, (P y, Q y)) ∈ U ×ˢ (univ : Set (F × F)) := ⟨hy, mem_univ _⟩
  have hbase : dMB (fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2) ((y, (P y, Q y)), (b, (0, 0))) =
      metricD h y b (P y) (Q y) := by
    simp only [metricD, dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  have hleft : HasDirDerivAt (fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2) (y, (P y, Q y))
      (0, (dMB P (y, b), 0)) (h y (dMB P (y, b)) (Q y)) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hh.add_left, hh.smul_left,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hright : HasDirDerivAt (fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2) (y, (P y, Q y))
      (0, (0, dMB Q (y, b))) (h y (P y) (dMB Q (y, b))) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hh.add_right, hh.smul_right,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  change dMB ((fun p : E × (F × F) ↦ h p.1 p.2.1 p.2.2) ∘ fun z ↦ (z, (P z, Q z))) (y, b) = _
  rw [hcomp, hdtrip, hsplit, hh1.dMB_add hUU hp, hh1.dMB_add hUU hp, hbase, hleft.dMB_eq,
    hright.dMB_eq]

omit [LocallyConvexSpace ℝ F] in
/-- **Compatibility for sections**: for a compatible connection,
`d(h(s, t))(a) = h(∇_a s, t) + h(s, ∇_a t)`. -/
theorem localCompat_sections (hh : IsLocalBundleMetric h U) (hU : IsOpen U)
    {Γ : E → E → F → F} (hc : IsLocalCompatible Γ h U) {s t : E → F}
    (hs : ContDiffMBOn 1 s U) (ht : ContDiffMBOn 1 t U) {y : E} (hy : y ∈ U) (a : E) :
    dMB (fun z ↦ h z (s z) (t z)) (y, a) =
      h y (dMB s (y, a) - Γ y a (s y)) (t y) + h y (s y) (dMB t (y, a) - Γ y a (t y)) := by
  rw [hh.dMB_apply hU hs ht hy, hc y hy, hh.sub_left, hh.sub_right]
  ring

/-- **The curvature of a metric connection is skew-adjoint**:
`h(Ω(u, v) ξ, η) + h(ξ, Ω(u, v) η) = 0`. -/
theorem bundleCurv_skew (hh : IsLocalBundleMetric h U) (hU : IsOpen U) {Γ : E → E → F → F}
    (hΓ : IsLocalSymbol Γ U) (hc : IsLocalCompatible Γ h U) {y : E} (hy : y ∈ U) (u v : E)
    (ξ η : F) :
    h y (bundleCurv Γ y u v ξ) η + h y ξ (bundleCurv Γ y u v η) = 0 := by
  have hconst : ∀ ζ : F, ContDiffMBOn 1 (fun _ : E ↦ ζ) U := fun ζ ↦ contDiffMBOn_const 1 ζ U
  have h0 : ∀ ζ : F, ∀ c, dMB (fun _ : E ↦ ζ) (y, c) = 0 := fun ζ c ↦
    (show HasDirDerivAt (fun _ : E ↦ ζ) y c 0 from
      tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp)).dMB_eq
  have hzl : ∀ ζ : F, h y 0 ζ = 0 := fun ζ ↦ by rw [hh.symm, hh.zero_right]
  -- the second derivative `D(a, c) = ∂_c ∂_a h(ξ, η)`
  set f : E → ℝ := fun z ↦ h z ξ η
  have hf : ContDiffMBOn 2 f U := hh.contDiffMBOn_comp hU (contDiffMBOn_const 2 ξ U)
    (contDiffMBOn_const 2 η U)
  have hD : ∀ a c, dMB (dMB f) ((y, a), (c, 0)) =
      -(metricD h y c (Γ y a ξ) η + h y (symbD Γ y c a ξ) η) -
        (metricD h y c ξ (Γ y a η) + h y ξ (symbD Γ y c a η)) := by
    intro a c
    have hslice : dMB (dMB f) ((y, a), (c, 0)) = dMB (fun z ↦ dMB f (z, a)) (y, c) := by
      simp only [dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
    have hev : (fun z ↦ dMB f (z, a)) =ᶠ[𝓝 y]
        fun z ↦ -h z (Γ z a ξ) η - h z ξ (Γ z a η) :=
      eventuallyEq_of_mem (hU.mem_nhds hy) fun z hz ↦ hc z hz a ξ η
    have hP := hΓ.contDiffMBOn_slice hU a ξ 1
    have hQ := hΓ.contDiffMBOn_slice hU a η 1
    have h1 := (hh.contDiffMBOn_comp hU hP (hconst η)).hasDirDerivAt (k := 0) hy c
    have h2 := (hh.contDiffMBOn_comp hU (hconst ξ) hQ).hasDirDerivAt (k := 0) hy c
    have hz : HasDirDerivAt (fun _ : E ↦ (0 : ℝ)) y c 0 :=
      tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp)
    have hfun : (fun z ↦ -h z (Γ z a ξ) η - h z ξ (Γ z a η)) =
        fun z ↦ (0 : ℝ) - h z (Γ z a ξ) η - h z ξ (Γ z a η) := funext fun z ↦ by ring
    rw [hslice, dMB_congr_of_eventuallyEq hev, hfun, ((hz.sub h1).sub h2).dMB_eq,
      hh.dMB_apply hU hP (hconst η) hy, hh.dMB_apply hU (hconst ξ) hQ hy, h0, h0,
      hh.zero_right, hzl]
    simp only [symbD]
    ring
  have hsym := hf.dMB_dMB_symm hU hy u v
  rw [hD, hD, hc y hy, hc y hy, hc y hy, hc y hy] at hsym
  simp only [bundleCurv, hh.sub_left, hh.sub_right, hh.add_left, hh.add_right]
  linarith [hh.symm y (Γ y u ξ) (Γ y v η), hh.symm y (Γ y v ξ) (Γ y u η)]

end IsLocalBundleMetric

end Local

/-! ### Global bundle metrics -/

section Global

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- A **bundle metric**: in each trivialization a smooth family of symmetric bilinear forms,
invariant under the coordinate changes, `hⱼ(τ y)(g ξ, g η) = hᵢ(y)(ξ, η)`. -/
structure BundleMetric (V : MBVectorBundleCore E M F) where
  /-- The metric in the trivialization over the chart `i`. -/
  h : atlas E M → E → F → F → ℝ
  isLocal : ∀ i, IsLocalBundleMetric (h i) i.1.target
  transition : ∀ i j : atlas E M, ∀ y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source, ∀ ξ η,
    h j ((j.1 ∘ i.1.symm) y) (V.coordChange i j (i.1.symm y) ξ)
      (V.coordChange i j (i.1.symm y) η) = h i y ξ η

namespace BundleMetric

variable {V : MBVectorBundleCore E M F} (g : BundleMetric V)

/-- A (weak) Riemannian bundle metric: positive definite on every fiber. -/
def IsPositive : Prop := ∀ i : atlas E M, ∀ y ∈ i.1.target, ∀ ξ, ξ ≠ 0 → 0 < g.h i y ξ ξ

end BundleMetric

namespace BundleConnection

variable {V : MBVectorBundleCore E M F} (C : BundleConnection V)

/-- A connection is **metric** for a bundle metric if its symbols are compatible with the metric
in every trivialization. -/
def IsMetric (g : BundleMetric V) : Prop :=
  ∀ i : atlas E M, IsLocalCompatible (C.Γ i) (g.h i) i.1.target

omit [MBManifold E M] in
/-- **The curvature of a metric connection is skew-adjoint** in every trivialization. -/
theorem IsMetric.curvLoc_skew {g : BundleMetric V} (hC : C.IsMetric g) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) (u v : E) (ξ η : F) :
    g.h i y (bundleCurv (C.Γ i) y u v ξ) η + g.h i y ξ (bundleCurv (C.Γ i) y u v η) = 0 :=
  (g.isLocal i).bundleCurv_skew i.1.open_target (C.isLocalSymbol i) (hC i) hy u v ξ η

/-- **The curvature of a metric connection is skew-adjoint**: for `C²` fields and sections,
`h(R(X, Y) s, t) + h(s, R(X, Y) t) = 0`, in the preferred chart at `x`. -/
theorem IsMetric.curvature_skew {g : BundleMetric V} (hC : C.IsMetric g)
    {X Y : M → TangentBundle E M} {s t : M → V.TotalSpace} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hsv : V.IsSection s) (htv : V.IsSection t)
    (hX : ContMDiffMB E (E × E) 2 X) (hY : ContMDiffMB E (E × E) 2 Y)
    (hs : ContMDiffMB E (E × F) 2 s) (ht : ContMDiffMB E (E × F) 2 t) (x : M) :
    g.h ⟨chartAt E x, chart_mem_atlas E x⟩ (chartAt E x x) (C.curvature X Y s x) (t x).2 +
      g.h ⟨chartAt E x, chart_mem_atlas E x⟩ (chartAt E x x) (s x).2 (C.curvature X Y t x) =
      0 := by
  rw [C.curvature_eq hXv hYv hsv hX hY hs, C.curvature_eq hXv hYv htv hX hY ht,
    ← V.localRep_chartAt hsv, ← V.localRep_chartAt htv]
  exact hC.curvLoc_skew _ _ ((chartAt E x).map_source (mem_chart_source E x)) _ _ _ _

end BundleConnection

end Global

end LocallyConvex.Manifolds
