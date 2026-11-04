/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Projector
import LCAnalysis.MBFrechet

/-!
# Example: the unit sphere of a Hilbert space

Let `H` be a real inner product space (completeness is not needed) and `e ∈ H` a unit
vector. The unit sphere is an embedded
submanifold of `H` modeled on `e^⊥`. The slice charts are explicit, with no inverse function
theorem: on the hemisphere `⟪q, e⟫ > 0`,

  `φ_e(q) = q - √(1 - ‖q - ⟪q, e⟫ e‖²) e`,   `φ_e⁻¹(r) = r + √(1 - ‖r - ⟪r, e⟫ e‖²) e`,

and `q` lies on the sphere iff `φ_e(q) ∈ e^⊥` (Pythagoras). Charts at other points are obtained
by composing with Householder reflections.
-/

open Set Filter
open scoped Topology Manifold RealInnerProductSpace ContDiff
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace Sphere

variable {e : H}

/-- The component of `q` orthogonal to `e`. -/
def tang (e q : H) : H := q - ⟪q, e⟫ • e

/-- The height function `√(1 - ‖q - ⟪q, e⟫ e‖²)` of the hemisphere around `e`. -/
def height (e q : H) : ℝ := Real.sqrt (1 - ‖tang e q‖ ^ 2)

theorem inner_tang (he : ‖e‖ = 1) (q : H) : ⟪tang e q, e⟫ = 0 := by
  simp [tang, inner_sub_left, inner_smul_left, he]

theorem tang_add_smul (he : ‖e‖ = 1) (q : H) (c : ℝ) : tang e (q + c • e) = tang e q := by
  have : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  simp only [tang, inner_add_left, inner_smul_left, this, RCLike.conj_to_real, mul_one, add_smul]
  abel

/-- Pythagoras: `‖q‖² = ‖tang e q‖² + ⟪q, e⟫²`. -/
theorem norm_sq_eq (he : ‖e‖ = 1) (q : H) : ‖q‖ ^ 2 = ‖tang e q‖ ^ 2 + ⟪q, e⟫ ^ 2 := by
  have hq : q = tang e q + ⟪q, e⟫ • e := by simp [tang]
  conv_lhs => rw [hq]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have h0 := inner_tang he q
  have h0' : ⟪e, tang e q⟫ = 0 := by rw [real_inner_comm]; exact h0
  have : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h0, h0', this,
    RCLike.conj_to_real]
  ring

theorem height_add_smul (he : ‖e‖ = 1) (q : H) (c : ℝ) : height e (q + c • e) = height e q := by
  simp only [height, tang_add_smul he]

theorem inner_add_smul (he : ‖e‖ = 1) (q : H) (c : ℝ) : ⟪q + c • e, e⟫ = ⟪q, e⟫ + c := by
  simp [inner_add_left, inner_smul_left, he]

theorem continuous_tang (e : H) : Continuous (tang e) := by
  unfold tang; fun_prop

theorem continuous_height (e : H) : Continuous (height e) := by
  unfold height; have := continuous_tang e; fun_prop

/-- The slice chart of the hemisphere around `e`. -/
def chart (he : ‖e‖ = 1) : OpenPartialHomeomorph H H where
  toFun q := q + (-height e q) • e
  invFun r := r + height e r • e
  source := {q | ‖tang e q‖ < 1 ∧ 0 < ⟪q, e⟫}
  target := {r | ‖tang e r‖ < 1 ∧ 0 < ⟪r, e⟫ + height e r}
  map_source' q hq := by
    refine ⟨by rw [tang_add_smul he]; exact hq.1, ?_⟩
    rw [inner_add_smul he, height_add_smul he]
    linarith [hq.2]
  map_target' r hr := by
    refine ⟨by rw [tang_add_smul he]; exact hr.1, ?_⟩
    rw [inner_add_smul he]
    exact hr.2
  left_inv' q _ := by
    rw [height_add_smul he, add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  right_inv' r _ := by
    rw [height_add_smul he, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  open_source := by
    have h1 : Continuous fun q : H ↦ ‖tang e q‖ := continuous_norm.comp (continuous_tang e)
    have h2 : Continuous fun q : H ↦ ⟪q, e⟫ := continuous_id.inner continuous_const
    exact (isOpen_lt h1 continuous_const).inter (isOpen_lt continuous_const h2)
  open_target := by
    have h1 : Continuous fun q : H ↦ ‖tang e q‖ := continuous_norm.comp (continuous_tang e)
    have h2 : Continuous fun q : H ↦ ⟪q, e⟫ + height e q :=
      (continuous_id.inner continuous_const).add (continuous_height e)
    exact (isOpen_lt h1 continuous_const).inter (isOpen_lt continuous_const h2)
  continuousOn_toFun :=
    (continuous_id.add ((continuous_height e).neg.smul continuous_const)).continuousOn
  continuousOn_invFun :=
    (continuous_id.add ((continuous_height e).smul continuous_const)).continuousOn

theorem contDiff_tang (e : H) : ContDiff ℝ ∞ (tang e) := by
  unfold tang
  exact contDiff_id.sub ((contDiff_id.inner ℝ contDiff_const).smul contDiff_const)

/-- `height e` is smooth where `‖tang e q‖ < 1`. -/
theorem contDiffOn_height (e : H) :
    ContDiffOn ℝ ∞ (height e) {q | ‖tang e q‖ < 1} := by
  unfold height
  refine ContDiffOn.sqrt ?_ fun q hq ↦ ?_
  · exact (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_tang e))).contDiffOn
  · have : ‖tang e q‖ ^ 2 < 1 := by
      have h0 := norm_nonneg (tang e q)
      nlinarith [hq.out]
    linarith

/-- The chart is smooth, with smooth inverse. -/
theorem chart_mem (he : ‖e‖ = 1) : chart he ∈ mbGroupoid H := by
  have hs : IsOpen (chart he).source := (chart he).open_source
  have ht : IsOpen (chart he).target := (chart he).open_target
  refine ⟨(smoothMBOn_iff_contDiffOn hs).mpr ?_, (smoothMBOn_iff_contDiffOn ht).mpr ?_⟩
  · exact contDiffOn_id.add (((contDiffOn_height e).mono
      fun q (hq : q ∈ (chart he).source) ↦ hq.1).neg.smul contDiffOn_const)
  · exact contDiffOn_id.add (((contDiffOn_height e).mono
      fun q (hq : q ∈ (chart he).target) ↦ hq.1).smul contDiffOn_const)

/-- On the hemisphere, `q` lies on the sphere iff `φ_e(q) ∈ e^⊥`. -/
theorem norm_eq_one_iff (he : ‖e‖ = 1) {q : H} (hq : q ∈ (chart he).source) :
    ‖q‖ = 1 ↔ chart he q ∈ (ℝ ∙ e)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  change ‖q‖ = 1 ↔ ⟪e, q + (-height e q) • e⟫ = 0
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  rw [inner_add_right, inner_smul_right, hee, real_inner_comm]
  have hpos : 0 < ⟪q, e⟫ := hq.2
  have ht : ‖tang e q‖ ^ 2 < 1 := by
    have h0 := norm_nonneg (tang e q)
    nlinarith [hq.1]
  have hpy := norm_sq_eq he q
  constructor
  · intro h1
    have : height e q = ⟪q, e⟫ := by
      rw [height, Real.sqrt_eq_iff_eq_sq (by linarith) hpos.le]
      rw [h1] at hpy
      linarith
    rw [this]; ring
  · intro h0
    have hh : height e q = ⟪q, e⟫ := by linarith
    rw [height, Real.sqrt_eq_iff_eq_sq (by linarith) hpos.le] at hh
    have : ‖q‖ ^ 2 = 1 := by linarith
    have hn := norm_nonneg q
    nlinarith [sq_nonneg (‖q‖ - 1)]

/-- The Householder reflection exchanging `p` and `e` (when `‖p‖ = ‖e‖`). -/
def refl (e p : H) : H ≃ₗᵢ[ℝ] H := Submodule.reflection (ℝ ∙ (p - e))ᗮ

/-- The slice chart around `p`: the Householder reflection, then the chart around `e`. -/
def chartAt' (he : ‖e‖ = 1) (p : H) : OpenPartialHomeomorph H H :=
  (refl e p).toHomeomorph.toOpenPartialHomeomorph.trans (chart he)


theorem refl_mem (e p : H) : (refl e p).toHomeomorph.toOpenPartialHomeomorph ∈ mbGroupoid H := by
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · exact (refl e p).toContinuousLinearEquiv.toContinuousLinearMap.contDiffMBOn k _
  · exact (refl e p).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiffMBOn k _

theorem chartAt'_mem (he : ‖e‖ = 1) (p : H) : chartAt' he p ∈ mbGroupoid H :=
  (mbGroupoid H).trans (refl_mem e p) (chart_mem he)

theorem mem_chartAt'_source (he : ‖e‖ = 1) {p : H} (hp : ‖p‖ = 1) :
    p ∈ (chartAt' he p).source := by
  have hR : refl e p p = e := Submodule.reflection_sub (by rw [hp, he])
  refine ⟨mem_univ _, ?_⟩
  change refl e p p ∈ (chart he).source
  rw [hR]
  have : tang e e = 0 := by simp [tang, he]
  refine ⟨by simp [this], ?_⟩
  rw [real_inner_self_eq_norm_sq, he]
  norm_num

end Sphere

open Sphere in
/-- **The unit sphere of a Hilbert space is an embedded submanifold**, modeled on `e^⊥` for any
unit vector `e`. -/
theorem isEmbeddedSubmanifold_sphere {e : H} (he : ‖e‖ = 1) :
    IsEmbeddedSubmanifold (Metric.sphere (0 : H) 1) (ℝ ∙ e)ᗮ := by
  refine ⟨Submodule.isClosed_orthogonal _, fun p hp ↦ ⟨chartAt' he p, ⟨?_, fun q hq ↦ ?_⟩, ?_⟩⟩
  · exact StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ (chartAt'_mem he p)
  · rw [mem_sphere_zero_iff_norm, ← (refl e p).norm_map q]
    exact norm_eq_one_iff he hq.2
  · exact mem_chartAt'_source he (mem_sphere_zero_iff_norm.mp hp)

namespace Sphere

/-- The chart around `e` has derivative the identity at `e`. -/
theorem hasFDerivAt_chart (he : ‖e‖ = 1) :
    HasFDerivAt (chart he) (ContinuousLinearMap.id ℝ H) e := by
  have htang : HasFDerivAt (tang e) (ContinuousLinearMap.id ℝ H -
      (innerSL ℝ e).smulRight e) e := by
    have h1 := (hasFDerivAt_id e).sub (((innerSL ℝ e).hasFDerivAt (x := e)).smul_const e)
    convert h1 using 1
    funext q
    simp [tang, real_inner_comm]
  have h0 : tang e e = 0 := by simp [tang, he]
  have hsq := htang.norm_sq
  rw [h0] at hsq
  have hf : HasFDerivAt (fun q ↦ 1 - ‖tang e q‖ ^ 2) (0 : H →L[ℝ] ℝ) e := by
    convert hsq.const_sub 1 using 1
    simp
  have hne : (fun q ↦ 1 - ‖tang e q‖ ^ 2) e ≠ 0 := by simp [h0]
  have hh : HasFDerivAt (height e) (0 : H →L[ℝ] ℝ) e := by
    have hfun : height e = fun y ↦ Real.sqrt (1 - ‖tang e y‖ ^ 2) := rfl
    rw [hfun]
    convert hf.sqrt hne using 1
    simp
  have := (hasFDerivAt_id e).add (hh.neg.smul_const e)
  convert this using 1
  · funext v
    change v + (-height e v) • e = v + (-height e v) • e
    rfl
  · ext v
    simp

theorem dMB_chart_at (he : ‖e‖ = 1) (v : H) : dMB (chart he) (e, v) = v :=
  ((hasFDerivAt_chart he).hasDirDerivAt v).dMB_eq

theorem refl_apply_self (he : ‖e‖ = 1) {p : H} (hp : ‖p‖ = 1) : refl e p p = e :=
  Submodule.reflection_sub (by rw [hp, he])

/-- The derivative of the chart around `p`, at `p`, is the reflection. -/
theorem dMB_chartAt'_at (he : ‖e‖ = 1) {p : H} (hp : ‖p‖ = 1) (w : H) :
    dMB (chartAt' he p) (p, w) = refl e p w := by
  have hc : HasFDerivAt (chart he) (ContinuousLinearMap.id ℝ H) (refl e p p) := by
    rw [refl_apply_self he hp]
    exact hasFDerivAt_chart he
  have hR := (refl e p).toContinuousLinearEquiv.hasFDerivAt (x := p)
  have hcomp := hc.comp p hR
  change dMB (chart he ∘ refl e p) (p, w) = _
  rw [(hcomp.hasDirDerivAt w).dMB_eq]
  rfl

end Sphere

open Sphere in
/-- **The tangent space of the sphere at `p` is `p^⊥`.** -/
theorem tangentSpace_sphere {e : H} (he : ‖e‖ = 1) (p : Metric.sphere (0 : H) 1) :
    (isEmbeddedSubmanifold_sphere he).tangentSpace p = {w | ⟪(p : H), w⟫ = 0} := by
  have hp : ‖(p : H)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  ext w
  have hsl : IsSliceChart (Metric.sphere (0 : H) 1) (ℝ ∙ e)ᗮ (chartAt' he p) :=
    ⟨StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ (chartAt'_mem he p), fun q hq ↦ by
      rw [mem_sphere_zero_iff_norm, ← (refl e p).norm_map q]
      exact norm_eq_one_iff he hq.2⟩
  rw [(isEmbeddedSubmanifold_sphere he).mem_tangentSpace_iff p hsl (mem_chartAt'_source he hp),
    dMB_chartAt'_at he hp, Submodule.mem_orthogonal_singleton_iff_inner_right]
  change ⟪e, refl e p w⟫ = 0 ↔ ⟪(p : H), w⟫ = 0
  have : ⟪e, refl e p w⟫ = ⟪(p : H), w⟫ := by
    calc ⟪e, refl e p w⟫ = ⟪refl e p p, refl e p w⟫ := by rw [refl_apply_self he hp]
      _ = ⟪(p : H), w⟫ := (refl e p).inner_map_map _ _
  rw [this]

namespace Sphere

end Sphere

end LCManifolds
