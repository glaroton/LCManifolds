/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Examples.PeriodicSmooth
import LCManifolds.Examples.OpenAndGraph

/-!
# The group `Diff⁺(S¹)` as an open subset of `C^∞_per`

References: A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §1.3
(Prop. 1.30, homotopy lifting; Prop. 1.33, lifting criterion; Prop. 1.34, uniqueness of lifts);
A. Katok, B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, Cambridge
University Press (1995), §11.1 (lifts and degree of circle maps); M. R. Herman, *Sur la
conjugaison différentiable des difféomorphismes du cercle à des rotations*, Publ. Math. IHÉS 49
(1979), Ch. II; R. S. Hamilton, *The inverse function theorem of Nash and Moser*, Bull. Amer.
Math. Soc. 7 (1982), Part I, §4.6; B. Khesin, R. Wendt, *The Geometry of Infinite-Dimensional
Groups*, Springer (2009), Ch. II; H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*
(arXiv:2602.12362). In Mathlib, the monotone lifts `φ (x + 1) = φ x + 1` of circle maps are
`CircleDeg1Lift` (`Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`).

## From the circle to its lifts (covering theory; not formalized here)

Let `π : ℝ → S¹ = ℝ / ℤ` be the projection, a covering map and a local diffeomorphism. The
following facts are classical and are **not** formalized in this file; we work directly with
the lifts.

* *Existence and uniqueness of lifts.* Since `ℝ` is simply connected, every continuous
  `f : S¹ → S¹` has a continuous lift `φ : ℝ → ℝ`, `π ∘ φ = f ∘ π`, by the lifting criterion
  (Hatcher, Prop. 1.33), and two lifts differ by an integer constant (Hatcher, Prop. 1.34).
* *Degree.* `φ (x + 1) - φ x` is a continuous integer valued function, hence a constant `d`, the
  degree of `f` (Katok–Hasselblatt, §11.1). A homeomorphism has degree `±1`, and it preserves
  the orientation exactly when `d = 1`, i.e. `φ (x + 1) = φ x + 1`; then `φ = id + u` with `u`
  `1`-periodic.
* *Smoothness.* Since `π` is a local diffeomorphism, `φ` is smooth if and only if `f` is, and
  `φ` is a diffeomorphism of `ℝ` exactly when `f` is a diffeomorphism of `S¹` (the inverse of
  `f` lifts to the inverse of `φ`).

So `Diff⁺(S¹) ≅ Ω / ℤ`, where `n ∈ ℤ` acts by `u ↦ u + n` (Herman, Ch. II; Hamilton,
I.4.6). The set `Ω` below is convex (`DiffCircle.convex_domain`), hence contractible, and
`Ω → Diff⁺(S¹)` is the universal cover `\widetilde{Diff}⁺(S¹)` (Khesin–Wendt, Ch. II).

## The lifts

An orientation preserving diffeomorphism of the circle lifts to a diffeomorphism
`φ = id + u` of `ℝ` with `u` smooth and `1`-periodic and `φ' = 1 + u' > 0`. We identify
the universal cover of `Diff⁺(S¹)` with the set

  `Ω = {u ∈ C^∞_per | 1 + u'(x) > 0 for all x}`.

Main results:

* `DiffCircle.isOpen_domain`, `DiffCircle.convex_domain`: `Ω` is open and convex in the Fréchet space `C^∞_per`. Hence `Ω` is a
  manifold modeled on `C^∞_per` (`DiffCircle.Ω`, an `Opens`, with its induced charted space and
  `MBManifold` structure). It is a **Fréchet manifold**: the model is complete
  (`CInfPer.instCompleteSpace`), but not normable, so it is not a Banach manifold.
* For `u ∈ Ω`, the lift `φ = id + u` is an increasing homeomorphism of `ℝ`, smooth with smooth
  inverse, commuting with the translation by `1` (`DiffCircle.liftHomeomorph`,
  `DiffCircle.contDiff_liftHomeomorph_symm`).
* `Ω` is closed under the group operations: the inverse `φ⁻¹ = id + v` has `v ∈ Ω`
  (`DiffCircle.inv_mem`) and the composition `(id + u) ∘ (id + w) = id + (w + u ∘ (id + w))`
  lies in `Ω` (`DiffCircle.comp_mem`), with `1 + (w + u ∘ φ_w)' = (1 + u' ∘ φ_w)(1 + w')`.
* Conversely, every diffeomorphism `φ` of `ℝ` with `φ (x + 1) = φ x + 1` is `id + u` for a unique
  `u ∈ Ω` (`DiffCircle.existsUnique_mem_domain_lift_eq`). More precisely, `u ∈ Ω` if and only if
  `id + u` has a differentiable left inverse (`DiffCircle.mem_domain_iff`); monotonicity is
  automatic. So `Ω` is exactly the group of diffeomorphisms of `ℝ` commuting with the
  translation by `1`.

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

/-- `Ω` is convex: `1 + (a u + b v)' = a (1 + u') + b (1 + v')`. In particular it is
contractible, so it is the universal cover of `Diff⁺(S¹)`. -/
theorem convex_domain : Convex ℝ domain := by
  intro u hu v hv a b ha hb hab x
  have hd : deriv (⇑(a • u + b • v)) x = a * deriv u x + b * deriv v x := by
    rw [coe_add, coe_smul, coe_smul]
    exact (((differentiable u x).hasDerivAt.const_smul a).add
      ((differentiable v x).hasDerivAt.const_smul b)).deriv
  rw [hd]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hv x
  · have := hu x
    nlinarith [hv x]

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

/-! ### The converse: every lift of a diffeomorphism comes from `Ω` -/

theorem lift_injective : Injective lift := by
  intro u v h
  ext x
  have := congrFun h x
  simp only [lift] at this
  linarith

/-- **Characterization of `Ω`.** For `u ∈ C^∞_per`, the following are equivalent:
`1 + u' > 0` everywhere, and `id + u` has a differentiable left inverse. No monotonicity is
assumed: a continuous injective map of `ℝ` is strictly monotone, and it cannot be decreasing
since it commutes with the translation by `1`; so `(id + u)' ≥ 0`, and the chain rule
`ψ'(φ x) φ'(x) = 1` excludes zeros. -/
theorem mem_domain_iff (u : CInfPer) :
    u ∈ domain ↔ ∃ ψ : ℝ → ℝ, Differentiable ℝ ψ ∧ LeftInverse ψ (lift u) := by
  constructor
  · intro hu
    exact ⟨(liftHomeomorph hu).symm, (contDiff_liftHomeomorph_symm hu).differentiable (by simp),
      (liftHomeomorph hu).symm_apply_apply⟩
  rintro ⟨ψ, hψ, hinv⟩ x
  have hd := hasDerivAt_lift u x
  have hmono : StrictMono (lift u) := by
    rcases (continuous_lift u).strictMono_of_inj hinv.injective with h | h
    · exact h
    · have := h (lt_add_one x)
      rw [lift_add_one] at this
      linarith
  have hnonneg := hd.nonneg_of_monotone hmono.monotone
  have hchain : HasDerivAt (ψ ∘ lift u) (deriv ψ (lift u x) * (1 + deriv u x)) x :=
    (hψ (lift u x)).hasDerivAt.comp x hd
  rw [show ψ ∘ lift u = id from funext hinv] at hchain
  have h1 := (hasDerivAt_id x).unique hchain
  have hne : 1 + deriv u x ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact one_ne_zero h1
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The periodic part `φ - id` of a smooth map commuting with the translation by `1`. -/
def ofLift (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hper : ∀ x, φ (x + 1) = φ x + 1) : CInfPer :=
  mk (fun x ↦ φ x - x) (hφ.sub contDiff_id) (fun x ↦ by
    change φ (x + 1) - (x + 1) = φ x - x
    rw [hper]
    ring)

theorem lift_ofLift {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : ∀ x, φ (x + 1) = φ x + 1) :
    lift (ofLift φ hφ hper) = φ := by
  funext x
  change x + (φ x - x) = φ x
  ring

/-- **Every diffeomorphism of `ℝ` commuting with the translation by `1` is the lift `id + u` of a
unique `u ∈ Ω`.** The diffeomorphism `φ` is only asked to be smooth with a differentiable left
inverse; it is then automatically increasing, i.e. it lifts an orientation preserving
diffeomorphism of the circle (lifts of orientation reversing ones satisfy
`φ (x + 1) = φ x - 1`). Together with `DiffCircle.liftHomeomorph` and
`DiffCircle.contDiff_liftHomeomorph_symm`, this identifies `Ω` with the group of diffeomorphisms
of `ℝ` that commute with the translation by `1`, i.e. with the universal cover of `Diff⁺(S¹)`. -/
theorem existsUnique_mem_domain_lift_eq {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hper : ∀ x, φ (x + 1) = φ x + 1) (hψ : Differentiable ℝ ψ) (hinv : LeftInverse ψ φ) :
    ∃! u, u ∈ domain ∧ lift u = φ := by
  refine ⟨ofLift φ hφ hper, ⟨?_, lift_ofLift hφ hper⟩, fun v hv ↦ ?_⟩
  · rw [mem_domain_iff, lift_ofLift hφ hper]
    exact ⟨ψ, hψ, hinv⟩
  · exact lift_injective (hv.2.trans (lift_ofLift hφ hper).symm)

end DiffCircle

end LCManifolds
