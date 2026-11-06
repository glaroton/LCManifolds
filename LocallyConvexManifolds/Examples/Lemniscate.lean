/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.SubmanifoldNotions
import LocallyConvexAnalysis.MBFrechet

/-!
# Counterexample: the figure eight is an injective immersion that is not initial

Let `θ(t) = 2 arctan t ∈ (-π, π)` and `j(t) = (sin θ, sin 2θ)`. Then `j : ℝ → ℝ²` is an injective
immersion whose image is the figure eight (`isImmersedSubmanifold_lemniscate`). It is not an
initial submanifold (`not_isInitialSubmanifold_lemniscate`): near the origin the image has two
branches, and the smooth curve `f(s) = (sin σ, -sin 2σ)`, `σ = (arctan s) / 2`, crosses the
origin along the branch that `j` only reaches as `t → ±∞`. Its lift `g` with `j ∘ g = f` jumps
from `g(s) > 1` (for `s > 0`) to `g(0) = 0`.
-/

open Set Filter Real
open scoped Topology Manifold ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

namespace Lemniscate

/-- The angle `θ(t) = 2 arctan t ∈ (-π, π)`. -/
def angle (t : ℝ) : ℝ := 2 * arctan t

theorem angle_mem (t : ℝ) : -π < angle t ∧ angle t < π := by
  have h1 := neg_pi_div_two_lt_arctan t
  have h2 := arctan_lt_pi_div_two t
  constructor <;> (unfold angle; linarith)

/-- The figure eight `j(t) = (sin θ, sin 2θ)`. -/
def j (t : ℝ) : ℝ × ℝ := (sin (angle t), sin (2 * angle t))

/-- On `(-π, π)`, `(sin a, sin 2a)` determines `a`. -/
theorem eq_of_sin_eq {a b : ℝ} (ha : -π < a ∧ a < π) (hb : -π < b ∧ b < π)
    (h1 : sin a = sin b) (h2 : sin (2 * a) = sin (2 * b)) : a = b := by
  by_cases hs : sin a = 0
  · have ha0 := (sin_eq_zero_iff_of_lt_of_lt ha.1 ha.2).mp hs
    have hb0 := (sin_eq_zero_iff_of_lt_of_lt hb.1 hb.2).mp (h1 ▸ hs)
    rw [ha0, hb0]
  · rw [sin_two_mul, sin_two_mul, ← h1] at h2
    have hcos : cos a = cos b := by
      have : 2 * sin a * (cos a - cos b) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linarith : sin a = 0) hs
      · linarith
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · -- both in `(-π, 0)`
      have ha' : a < 0 := by
        by_contra h
        exact absurd (sin_nonneg_of_nonneg_of_le_pi (not_lt.mp h) ha.2.le) (not_le.mpr hneg)
      have hb' : b < 0 := by
        by_contra h
        exact absurd (sin_nonneg_of_nonneg_of_le_pi (not_lt.mp h) hb.2.le) (not_le.mpr (h1 ▸ hneg))
      have := injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        (show cos (-a) = cos (-b) by rw [cos_neg, cos_neg, hcos])
      linarith
    · have ha' : 0 < a := by
        by_contra h
        exact absurd (sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.mp h) ha.1.le) (not_le.mpr hpos)
      have hb' : 0 < b := by
        by_contra h
        exact absurd (sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.mp h) hb.1.le)
          (not_le.mpr (h1 ▸ hpos))
      exact injOn_cos ⟨ha'.le, ha.2.le⟩ ⟨hb'.le, hb.2.le⟩ hcos

theorem j_injective : Function.Injective j := by
  intro s t h
  have h1 : sin (angle s) = sin (angle t) := congrArg Prod.fst h
  have h2 : sin (2 * angle s) = sin (2 * angle t) := congrArg Prod.snd h
  have := eq_of_sin_eq (angle_mem s) (angle_mem t) h1 h2
  unfold angle at this
  exact arctan_injective (by linarith)

theorem contDiff_j : ContDiff ℝ ∞ j := by
  unfold j angle
  exact ((contDiff_const.mul contDiff_arctan).sin).prodMk
    ((contDiff_const.mul (contDiff_const.mul contDiff_arctan)).sin)

/-- A Fréchet smooth map between model spaces is a smooth map of manifolds. -/
theorem smoothMBM_of_contDiff {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) :
    SmoothMBM E F f := fun k ↦
  (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).mpr
    ((smoothMBOn_iff_contDiffOn isOpen_univ).mpr hf.contDiffOn k)

/-- The velocity of `j`. -/
def vel (t : ℝ) : ℝ × ℝ :=
  (cos (angle t) * (2 * (1 / (1 + t ^ 2))), cos (2 * angle t) * (2 * (2 * (1 / (1 + t ^ 2)))))

theorem hasDerivAt_j (t : ℝ) : HasDerivAt j (vel t) t := by
  have ha : HasDerivAt angle (2 * (1 / (1 + t ^ 2))) t := (hasDerivAt_arctan t).const_mul 2
  exact ha.sin.prodMk (ha.const_mul 2).sin

theorem vel_ne_zero (t : ℝ) : vel t ≠ 0 := by
  intro h
  have hc : 0 < 2 * (1 / (1 + t ^ 2)) := by positivity
  have h1 : cos (angle t) = 0 := by
    have := congrArg Prod.fst h
    simp only [vel, Prod.fst_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  have h2 : cos (2 * angle t) = 0 := by
    have := congrArg Prod.snd h
    simp only [vel, Prod.snd_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  rw [cos_two_mul, h1] at h2
  norm_num at h2

/-- In the (identity) charts, the differential of `j` at `t` is `v ↦ v • j'(t)`. -/
theorem dMB_chart_j (t : ℝ) :
    (fun v : ℝ ↦ dMB (chartAt (ℝ × ℝ) (j t) ∘ j ∘ (chartAt ℝ t).symm) (chartAt ℝ t t, v)) =
      fun v ↦ v • vel t := by
  funext v
  change dMB j (t, v) = v • vel t
  rw [((hasDerivAt_j t).hasFDerivAt.hasDirDerivAt v).dMB_eq]
  simp

/-- **The figure eight is an injectively immersed submanifold.** -/
theorem isImmersedSubmanifold_lemniscate : IsImmersedSubmanifold ℝ (ℝ × ℝ) j := by
  refine ⟨j_injective, smoothMBM_of_contDiff contDiff_j, fun t ↦ ?_⟩
  rw [dMB_chart_j]
  have he := isClosedEmbedding_smul_left (𝕜 := ℝ) (vel_ne_zero t)
  exact ⟨he.isClosed_range, he.isEmbedding⟩

/-! ### The lift that jumps -/

/-- The test curve `f(s) = (sin σ, -sin 2σ)`, `σ = (arctan s) / 2`, through the origin along the
second branch. -/
def f (s : ℝ) : ℝ × ℝ := (sin (arctan s / 2), -sin (2 * (arctan s / 2)))

/-- The angle of the lift: `π - σ` for `s > 0`, `-π - σ` for `s < 0`, `0` at `0`. -/
def liftAngle (s : ℝ) : ℝ :=
  if 0 < s then π - arctan s / 2 else if s < 0 then -π - arctan s / 2 else 0

/-- The lift `g = tan (liftAngle / 2)`, with `j ∘ g = f`. -/
def g (s : ℝ) : ℝ := tan (liftAngle s / 2)

theorem liftAngle_half_mem (s : ℝ) : -(π / 2) < liftAngle s / 2 ∧ liftAngle s / 2 < π / 2 := by
  have h1 := neg_pi_div_two_lt_arctan s
  have h2 := arctan_lt_pi_div_two s
  unfold liftAngle
  split_ifs with hs hs'
  · have : 0 < arctan s := arctan_pos.mpr hs
    constructor <;> linarith
  · have : arctan s < 0 := by
      have := arctan_strictMono hs'
      rwa [arctan_zero] at this
    constructor <;> linarith
  · constructor <;> linarith [pi_pos]

theorem angle_g (s : ℝ) : angle (g s) = liftAngle s := by
  unfold angle g
  rw [arctan_tan (liftAngle_half_mem s).1 (liftAngle_half_mem s).2]
  ring

theorem j_g (s : ℝ) : j (g s) = f s := by
  unfold j f
  rw [angle_g]
  unfold liftAngle
  split_ifs with hs hs'
  · refine Prod.ext ?_ ?_
    · exact sin_pi_sub _
    · change sin (2 * (π - arctan s / 2)) = -sin (2 * (arctan s / 2))
      rw [show 2 * (π - arctan s / 2) = 2 * π - 2 * (arctan s / 2) by ring, sin_two_pi_sub]
  · refine Prod.ext ?_ ?_
    · change sin (-π - arctan s / 2) = sin (arctan s / 2)
      rw [show -π - arctan s / 2 = -(arctan s / 2 + π) by ring, sin_neg, sin_add_pi, neg_neg]
    · change sin (2 * (-π - arctan s / 2)) = -sin (2 * (arctan s / 2))
      rw [show 2 * (-π - arctan s / 2) = -(2 * (arctan s / 2)) + (-1 : ℤ) * (2 * π) by
        push_cast; ring, sin_add_int_mul_two_pi, sin_neg]
  · have : s = 0 := by linarith [not_lt.mp hs, not_lt.mp hs']
    subst this
    simp

theorem contDiff_f : ContDiff ℝ ∞ f := by
  unfold f
  exact (contDiff_arctan.div_const 2).sin.prodMk
    ((contDiff_const.mul (contDiff_arctan.div_const 2)).sin.neg)

theorem one_lt_g {s : ℝ} (hs : 0 < s) : 1 < g s := by
  have hpi := pi_pos
  have h2 := arctan_lt_pi_div_two s
  have hpos : 0 < arctan s := arctan_pos.mpr hs
  have hmem := liftAngle_half_mem s
  have hθ : liftAngle s = π - arctan s / 2 := by simp [liftAngle, hs]
  rw [g, ← tan_pi_div_four]
  refine strictMonoOn_tan ⟨by linarith, by linarith⟩ ⟨hmem.1, hmem.2⟩ ?_
  rw [hθ]
  linarith

theorem g_zero : g 0 = 0 := by simp [g, liftAngle]

/-- **The figure eight is not an initial submanifold**: `j ∘ g = f` is smooth, but `g` is not
even continuous at `0`. -/
theorem not_isInitialSubmanifold_lemniscate : ¬ IsInitialSubmanifold ℝ (ℝ × ℝ) j := by
  intro h
  have hjg : SmoothMBM ℝ (ℝ × ℝ) (j ∘ g) := by
    have : j ∘ g = f := funext j_g
    rw [this]
    exact smoothMBM_of_contDiff contDiff_f
  have hg : SmoothMBM ℝ ℝ g := h.2.2 g hjg
  have hgc : Continuous g := continuousOn_univ.mp (hg 0).1
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have := (hgc.continuousAt (x := 0)).tendsto
    rw [g_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 1 ≤ g s :=
    eventually_nhdsWithin_of_forall fun s hs ↦ (one_lt_g hs).le
  have := ge_of_tendsto hlim hev
  linarith

end Lemniscate

end LocallyConvex.Manifolds
