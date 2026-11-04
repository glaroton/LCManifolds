/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Examples.PeriodicSmooth
import LCManifolds.Examples.OpenAndGraph

/-!
# The group `Diff⁺(S¹)` as an open subset of `C^∞_per`

An orientation preserving diffeomorphism of the circle `S¹ = ℝ / ℤ` lifts to a diffeomorphism
`φ = id + u` of `ℝ` with `u` smooth and `1`-periodic and `φ' = 1 + u' > 0`. We identify
`Diff⁺(S¹)` (more precisely, its universal cover: the lifts are determined up to integer
translations) with the set

  `Ω = {u ∈ C^∞_per | 1 + u'(x) > 0 for all x}`.

Main results:

* `DiffCircle.isOpen_domain`: `Ω` is open in the Fréchet space `C^∞_per`. Hence `Ω` is a
  manifold modeled on `C^∞_per` (`DiffCircle.Ω`, an `Opens`, with its induced charted space and
  `MBManifold` structure). It is a **Fréchet manifold**: the model is complete
  (`CInfPer.instCompleteSpace`), but not normable, so it is not a Banach manifold.
* For `u ∈ Ω`, the lift `φ = id + u` is an increasing homeomorphism of `ℝ`, smooth with smooth
  inverse, commuting with the translation by `1` (`DiffCircle.liftHomeomorph`,
  `DiffCircle.contDiff_liftHomeomorph_symm`).
* `Ω` is closed under the group operations: the inverse `φ⁻¹ = id + v` has `v ∈ Ω`
  (`DiffCircle.inv_mem`) and the composition `(id + u) ∘ (id + w) = id + (w + u ∘ (id + w))`
  lies in `Ω` (`DiffCircle.comp_mem`), with `1 + (w + u ∘ φ_w)' = (1 + u' ∘ φ_w)(1 + w')`.

The smoothness of composition and inversion as maps `Ω × Ω → Ω`, `Ω → Ω` (which makes `Ω` a Lie
group) is not proved here; it belongs to the theory of Lie groups.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace LCManifolds

namespace DiffCircle

open CInfPer

theorem differentiable (u : CInfPer) : Differentiable ℝ u := by
  simpa using u.differentiable_iteratedDeriv 0

theorem continuous_deriv (u : CInfPer) : Continuous (deriv u) := by
  simpa using u.continuous_iteratedDeriv 1

theorem periodic_deriv (u : CInfPer) : Periodic (deriv u) 1 := by
  simpa using u.periodic_iteratedDeriv 1

/-- The domain `Ω = {u | 1 + u' > 0}`. -/
def domain : Set CInfPer := {u | ∀ x, 0 < 1 + deriv u x}

/-- On `Ω`, `1 + u'` is bounded below by a positive constant (compactness of the circle). -/
theorem exists_pos_le {u : CInfPer} (hu : u ∈ domain) : ∃ c > 0, ∀ x, c ≤ 1 + deriv u x := by
  have hc : Continuous fun x ↦ 1 + deriv u x := continuous_const.add (continuous_deriv u)
  have hp : Periodic (fun x ↦ 1 + deriv u x) 1 := fun x ↦ by
    simp only [periodic_deriv u x]
  obtain ⟨c, ⟨x₀, rfl⟩, hle⟩ :=
    (hp.compact_of_continuous one_ne_zero hc).exists_isLeast (range_nonempty _)
  exact ⟨_, hu x₀, fun x ↦ hle ⟨x, rfl⟩⟩

/-- **`Ω` is open in `C^∞_per`**: a perturbation of `u'` smaller than `min (1 + u')` keeps
`1 + u'` positive. -/
theorem isOpen_domain : IsOpen domain := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  obtain ⟨c, hc, hle⟩ := exists_pos_le hu
  have hV : IsOpen (derivBCF 1 ⁻¹' Metric.ball (derivBCF 1 u) c) :=
    Metric.isOpen_ball.preimage (continuous_derivBCF 1)
  refine Filter.mem_of_superset (hV.mem_nhds (Metric.mem_ball_self hc)) fun v hv x ↦ ?_
  have hd := lt_of_le_of_lt ((derivBCF 1 v).dist_coe_le_dist x) hv
  simp only [coe_derivBCF, iteratedDeriv_one, Real.dist_eq] at hd
  have := abs_lt.mp hd
  linarith [hle x, this.1]

/-- `Ω` as an open subset of `C^∞_per`: a manifold modeled on `C^∞_per`. -/
def Ω : TopologicalSpace.Opens CInfPer := ⟨domain, isOpen_domain⟩

example : ChartedSpace CInfPer Ω := inferInstance
example : MBManifold CInfPer Ω := inferInstance

theorem zero_mem : (0 : CInfPer) ∈ domain := fun x ↦ by simp

/-! ### The lifts `id + u` -/

/-- The lift `φ_u = id + u` of a circle map. -/
def lift (u : CInfPer) (x : ℝ) : ℝ := x + u x

theorem lift_add_one (u : CInfPer) (x : ℝ) : lift u (x + 1) = lift u x + 1 := by
  simp only [lift, u.periodic x]; ring

theorem hasDerivAt_lift (u : CInfPer) (x : ℝ) : HasDerivAt (lift u) (1 + deriv u x) x :=
  (hasDerivAt_id x).add ((differentiable u x).hasDerivAt)

theorem contDiff_lift (u : CInfPer) : ContDiff ℝ ∞ (lift u) := contDiff_id.add u.contDiff

theorem continuous_lift (u : CInfPer) : Continuous (lift u) := (contDiff_lift u).continuous

theorem strictMono_lift {u : CInfPer} (hu : u ∈ domain) : StrictMono (lift u) :=
  strictMono_of_deriv_pos fun x ↦ by rw [(hasDerivAt_lift u x).deriv]; exact hu x

theorem surjective_lift (u : CInfPer) : Surjective (lift u) := by
  obtain ⟨C, hC⟩ := u.exists_bound 0
  simp only [iteratedDeriv_zero, Real.norm_eq_abs] at hC
  refine (continuous_lift u).surjective ?_ ?_
  · refine tendsto_atTop_mono (fun x ↦ ?_) (tendsto_atTop_add_const_right _ (-C) tendsto_id)
    have := (abs_le.mp (hC x)).1
    simp only [lift, id]; linarith
  · refine tendsto_atBot_mono (fun x ↦ ?_) (tendsto_atBot_add_const_right _ C tendsto_id)
    have := (abs_le.mp (hC x)).2
    simp only [lift, id]; linarith

/-- For `u ∈ Ω`, the lift `id + u` as an (increasing) homeomorphism of `ℝ`. -/
def liftHomeomorph {u : CInfPer} (hu : u ∈ domain) : ℝ ≃ₜ ℝ :=
  ((strictMono_lift hu).orderIsoOfSurjective _ (surjective_lift u)).toHomeomorph

@[simp] theorem liftHomeomorph_apply {u : CInfPer} (hu : u ∈ domain) (x : ℝ) :
    liftHomeomorph hu x = lift u x := rfl

/-- **The inverse of the lift is smooth**: `id + u` is a diffeomorphism of `ℝ`. -/
theorem contDiff_liftHomeomorph_symm {u : CInfPer} (hu : u ∈ domain) :
    ContDiff ℝ ∞ (liftHomeomorph hu).symm :=
  (liftHomeomorph hu).contDiff_symm_deriv (fun x ↦ (hu x).ne') (hasDerivAt_lift u)
    (contDiff_lift u)

theorem liftHomeomorph_symm_add_one {u : CInfPer} (hu : u ∈ domain) (y : ℝ) :
    (liftHomeomorph hu).symm (y + 1) = (liftHomeomorph hu).symm y + 1 := by
  apply (liftHomeomorph hu).injective
  rw [Homeomorph.apply_symm_apply, liftHomeomorph_apply, lift_add_one, ← liftHomeomorph_apply hu,
    Homeomorph.apply_symm_apply]

/-! ### Inverses and compositions stay in `Ω` -/

/-- The periodic part `v = φ⁻¹ - id` of the inverse of the lift. -/
def inv {u : CInfPer} (hu : u ∈ domain) : CInfPer :=
  mk (fun y ↦ (liftHomeomorph hu).symm y - y)
    ((contDiff_liftHomeomorph_symm hu).sub contDiff_id)
    (fun y ↦ by simp only [liftHomeomorph_symm_add_one]; ring)

theorem lift_inv {u : CInfPer} (hu : u ∈ domain) : lift (inv hu) = (liftHomeomorph hu).symm := by
  funext y
  change y + ((liftHomeomorph hu).symm y - y) = _
  ring

/-- **`Ω` is closed under inversion**: `(id + u)⁻¹ = id + v` with `v ∈ Ω`, since
`(φ⁻¹)'(y) = 1 / φ'(φ⁻¹ y) > 0`. -/
theorem inv_mem {u : CInfPer} (hu : u ∈ domain) : inv hu ∈ domain := by
  intro y
  set g := (liftHomeomorph hu).symm
  have hg : HasDerivAt g (1 + deriv u (g y))⁻¹ y :=
    HasDerivAt.of_local_left_inverse g.continuous.continuousAt (hasDerivAt_lift u (g y))
      (hu (g y)).ne' (Eventually.of_forall fun z ↦ (liftHomeomorph hu).apply_symm_apply z)
  have hv : HasDerivAt (lift (inv hu)) (1 + deriv u (g y))⁻¹ y := by rw [lift_inv]; exact hg
  rw [← (hasDerivAt_lift (inv hu) y).deriv, hv.deriv]
  exact inv_pos.mpr (hu (g y))

/-- The periodic part of the composition `(id + u) ∘ (id + w) = id + (w + u ∘ (id + w))`. -/
def comp (u w : CInfPer) : CInfPer :=
  mk (fun x ↦ w x + u (lift w x)) (w.contDiff.add (u.contDiff.comp (contDiff_lift w)))
    (fun x ↦ by
      change w (x + 1) + u (lift w (x + 1)) = w x + u (lift w x)
      rw [lift_add_one, w.periodic x, u.periodic (lift w x)])

theorem lift_comp (u w : CInfPer) : lift (comp u w) = lift u ∘ lift w := by
  funext x
  simp only [lift, comp, coe_mk, Function.comp_apply]
  ring

/-- **`Ω` is closed under composition**: `1 + (w + u ∘ φ_w)' = (1 + u' ∘ φ_w) (1 + w') > 0`. -/
theorem comp_mem {u w : CInfPer} (hu : u ∈ domain) (hw : w ∈ domain) : comp u w ∈ domain := by
  intro x
  have h : HasDerivAt (lift (comp u w)) ((1 + deriv u (lift w x)) * (1 + deriv w x)) x := by
    rw [lift_comp]
    exact (hasDerivAt_lift u (lift w x)).comp x (hasDerivAt_lift w x)
  rw [← (hasDerivAt_lift (comp u w) x).deriv, h.deriv]
  exact mul_pos (hu _) (hw x)

end DiffCircle

end LCManifolds
