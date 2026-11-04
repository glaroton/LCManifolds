/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Projector
import LCAnalysis.MBFrechet

/-!
# Example: the unit sphere of an inner product space

Let `H` be a real inner product space and `e ∈ H` a unit vector.

**Completeness.** If `H` is complete (a Hilbert space), `H` is a Hilbert manifold and the sphere is
a Hilbert submanifold of it. If `H` is not complete, `H` is still a manifold in the sense of this
library, whose model spaces need not be complete (see `LCManifolds.Basic`), but it is **not** a
Hilbert or Banach manifold, and neither is the sphere. The construction below does not use
completeness, so it covers both cases; the statements about Hilbert manifolds are the case
`[CompleteSpace H]`.
 The unit sphere is an embedded
submanifold of `H` modeled on `e^⊥`. The slice charts are explicit, with no inverse function
theorem: on the hemisphere `⟪q, e⟫ > 0`,

  `φ_e(q) = q - √(1 - ‖q - ⟪q, e⟫ e‖²) e`,   `φ_e⁻¹(r) = r + √(1 - ‖r - ⟪r, e⟫ e‖²) e`,

and `q` lies on the sphere iff `φ_e(q) ∈ e^⊥` (Pythagoras). Charts at other points are obtained
by composing with Householder reflections.

Main results:

* `isEmbeddedSubmanifold_sphere`: the sphere is an embedded submanifold modeled on `e^⊥`;
* `tangentSpace_sphere`: `T_p S = p^⊥`;
* `projectorField_sphere`: the orthogonal projections `w ↦ w - ⟪w, p⟫ p` form a field of
  projectors;
* `isGeodesic_sphere_iff`: for the connection they define, a curve is a geodesic iff its
  acceleration is normal, `α̈ = ⟪α̈, α⟫ α`;
* `isGeodesic_greatCircle`: great circles `t ↦ cos t • p + sin t • v` (`v ⊥ p` unit) are
  geodesics.
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
/-- **The unit sphere of a real inner product space is an embedded submanifold**, modeled on
`e^⊥` for any unit vector `e`. No completeness is assumed. -/
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

/-- The orthogonal projection onto `p^⊥`: `w ↦ w - ⟪w, p⟫ p`. -/
def sphereProj (p w : H) : H := w - ⟪w, p⟫ • p

/-- **The orthogonal projections onto the tangent spaces form a field of projectors.** -/
def projectorField_sphere {e : H} (he : ‖e‖ = 1) :
    ProjectorField (isEmbeddedSubmanifold_sphere he) where
  E p w := sphereProj p w
  map_add p w w' := by simp only [sphereProj, inner_add_left, add_smul]; abel
  map_smul p c w := by simp only [sphereProj, inner_smul_left, smul_sub, mul_smul]; simp
  idem p w := by
    have hp : ⟪(p : H), (p : H)⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp p.2, one_pow]
    simp only [sphereProj, inner_sub_left, inner_smul_left, hp]
    simp
  range_eq p := by
    have hp : ⟪(p : H), (p : H)⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp p.2, one_pow]
    rw [tangentSpace_sphere he p]
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      change ⟪(p : H), v - ⟪v, (p : H)⟫ • (p : H)⟫ = 0
      rw [inner_sub_right, inner_smul_right, hp, real_inner_comm]
      ring
    · intro hw
      refine ⟨w, ?_⟩
      change w - ⟪w, (p : H)⟫ • (p : H) = w
      rw [real_inner_comm, hw.out, zero_smul, sub_zero]
  smooth {φ} hφ p₀ := by
    set D : Set ((ℝ ∙ e)ᗮ) := Subtype.val ⁻¹' φ.target
    have hD : IsOpen D := ProjectorField.isOpen_dom φ
    have hDD : IsOpen (D ×ˢ (univ : Set H)) := hD.prod isOpen_univ
    -- the parametrization `ψ = φ⁻¹|_S` is Fréchet smooth
    have hψ : ContDiffOn ℝ ∞ (ProjectorField.param φ) D :=
      (smoothMBOn_iff_contDiffOn hD).mp (ProjectorField.smoothMBOn_param hφ)
    have hψ1 : ContDiffOn ℝ ∞ (fun q : (ℝ ∙ e)ᗮ × H ↦ ProjectorField.param φ q.1)
        (D ×ˢ univ) := hψ.comp contDiffOn_fst fun q hq ↦ hq.1
    have hG : ContDiffOn ℝ ∞ (fun q : (ℝ ∙ e)ᗮ × H ↦
        q.2 - ⟪q.2, ProjectorField.param φ q.1⟫ • ProjectorField.param φ q.1) (D ×ˢ univ) :=
      contDiffOn_snd.sub ((contDiffOn_snd.inner ℝ hψ1).smul hψ1)
    refine (smoothMBOn_iff_contDiffOn hDD).mpr (hG.congr fun q hq ↦ ?_)
    have hx : (((sliceChart hφ p₀).symm q.1 : Metric.sphere (0 : H) 1) : H) = φ.symm q.1 :=
      sliceChart_symm_apply_coe hφ p₀ hq.1
    change sphereProj (((sliceChart hφ p₀).symm q.1 : Metric.sphere (0 : H) 1) : H) q.2 = _
    rw [hx]
    rfl

/-- **Geodesics of the sphere**: a curve with smooth ambient curve is a geodesic iff its
acceleration is normal, `α̈ = ⟪α̈, α⟫ α`. -/
theorem isGeodesic_sphere_iff {e : H} (he : ‖e‖ = 1) {α : ℝ → Metric.sphere (0 : H) 1}
    (hα : SmoothMBOn (Subtype.val ∘ α) univ) :
    letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
    haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
    (projectorField_sphere he).connection.IsGeodesic α ↔
      ∀ t, dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1) =
        ⟪dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1), (α t : H)⟫ • (α t : H) := by
  let := (isEmbeddedSubmanifold_sphere he).chartedSpace
  have := (isEmbeddedSubmanifold_sphere he).mbManifold
  rw [ProjectorField.connection_isGeodesic_iff _
    ((isEmbeddedSubmanifold_sphere he).isCkCurve_of_smooth hα 2)]
  refine forall_congr' fun t ↦ ?_
  change sphereProj _ _ = 0 ↔ _
  rw [sphereProj, sub_eq_zero]

/-- The derivative of a Fréchet differentiable curve. -/
theorem dMB_eq_of_hasDerivAt {f : ℝ → H} {f' : H} {t : ℝ} (hf : HasDerivAt f f' t) :
    dMB f (t, 1) = f' := by
  rw [(hf.hasFDerivAt.hasDirDerivAt 1).dMB_eq]
  simp

theorem norm_greatCircle {p v : H} (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : ⟪p, v⟫ = 0) (t : ℝ) :
    ‖Real.cos t • p + Real.sin t • v‖ = 1 := by
  have hvp : ⟪v, p⟫ = 0 := by rw [real_inner_comm]; exact hpv
  have h2 : ‖Real.cos t • p + Real.sin t • v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hp, hv, hpv, hvp, RCLike.conj_to_real]
    nlinarith [Real.sin_sq_add_cos_sq t]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (h2.trans (one_pow 2).symm)

/-- The great circle through `p` with unit velocity `v ⊥ p`. -/
def greatCircle {p v : H} (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : ⟪p, v⟫ = 0) :
    ℝ → Metric.sphere (0 : H) 1 :=
  fun t ↦ ⟨Real.cos t • p + Real.sin t • v,
    mem_sphere_zero_iff_norm.mpr (norm_greatCircle hp hv hpv t)⟩

/-- **Great circles are geodesics of the sphere.** -/
theorem isGeodesic_greatCircle {e : H} (he : ‖e‖ = 1) {p v : H} (hp : ‖p‖ = 1) (hv : ‖v‖ = 1)
    (hpv : ⟪p, v⟫ = 0) :
    letI := (isEmbeddedSubmanifold_sphere he).chartedSpace
    haveI := (isEmbeddedSubmanifold_sphere he).mbManifold
    (projectorField_sphere he).connection.IsGeodesic (greatCircle hp hv hpv) := by
  have hval : Subtype.val ∘ greatCircle hp hv hpv =
      fun t ↦ Real.cos t • p + Real.sin t • v := rfl
  have hsmooth : SmoothMBOn (Subtype.val ∘ greatCircle hp hv hpv) univ := by
    rw [hval, smoothMBOn_iff_contDiffOn isOpen_univ]
    exact ((Real.contDiff_cos.smul contDiff_const).add
      (Real.contDiff_sin.smul contDiff_const)).contDiffOn
  rw [isGeodesic_sphere_iff he hsmooth]
  intro t
  have h1 : (fun s ↦ dMB (Subtype.val ∘ greatCircle hp hv hpv) (s, 1)) =
      fun s ↦ -Real.sin s • p + Real.cos s • v := by
    funext s
    rw [hval]
    exact dMB_eq_of_hasDerivAt (((Real.hasDerivAt_cos s).smul_const p).add
      ((Real.hasDerivAt_sin s).smul_const v))
  have h2 : dMB (fun s ↦ -Real.sin s • p + Real.cos s • v) (t, 1) =
      -(Real.cos t • p + Real.sin t • v) := by
    have hd := (((Real.hasDerivAt_sin t).neg).smul_const p).add
      ((Real.hasDerivAt_cos t).smul_const v)
    have hfun : (fun s ↦ -Real.sin s • p + Real.cos s • v) =
        ((fun y ↦ (-Real.sin) y • p) + fun y ↦ Real.cos y • v) := rfl
    rw [hfun, dMB_eq_of_hasDerivAt hd, neg_smul, neg_smul, neg_add]
  rw [h1, h2]
  change _ = ⟪-(Real.cos t • p + Real.sin t • v), Real.cos t • p + Real.sin t • v⟫ •
    (Real.cos t • p + Real.sin t • v)
  rw [inner_neg_left, real_inner_self_eq_norm_sq, norm_greatCircle hp hv hpv t]
  simp only [one_pow, neg_smul, one_smul]

end LCManifolds
