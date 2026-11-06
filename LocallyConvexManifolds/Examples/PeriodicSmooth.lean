/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Basic

/-!
# The Fréchet space of smooth periodic functions

`C^∞_per` is the space of smooth `1`-periodic functions `u : ℝ → ℝ` (smooth functions on the
circle `S¹ = ℝ / ℤ`), with the topology of uniform convergence of all the derivatives, that is,
the topology of the seminorms

  `p_k(u) = sup_x |u^{(k)}(x)|`,   `k ∈ ℕ`.

It is a **Fréchet space**: locally convex, Hausdorff, metrizable and complete
(`CInfPer.instCompleteSpace`, `CInfPer.instMetrizableSpace`). It is not normable, and it is the
model space of the group `Diff⁺(S¹)` (see `LocallyConvexManifolds.Examples.DiffCircle`).

**Construction.** The topology (and the uniform structure) is induced by the linear embedding

  `J : C^∞_per → ∏_k BC(ℝ), u ↦ (u, u', u'', …)`

into a countable product of Banach spaces of bounded continuous functions. All the
structure is inherited from the product, except completeness, which amounts to the range of `J`
being closed: if `u_n^{(k)} → g_k` uniformly for every `k`, then `g_0` is smooth and periodic with
`g_0^{(k)} = g_k` (`CInfPer.isClosed_range_J`, via the theorem on uniform limits of derivatives).

Main results:

* `CInfPer.tendsto_iff`: convergence in `C^∞_per` is uniform convergence of every derivative;
* `CInfPer.seminorm`: the seminorms `p_k`, with `norm_iteratedDeriv_le_seminorm`;
* instances: `IsTopologicalAddGroup`, `ContinuousSMul ℝ`, `LocallyConvexSpace ℝ`, `T2Space`,
  `MetrizableSpace`, `CompleteSpace`.
-/

open Set Filter Function
open scoped Topology ContDiff BoundedContinuousFunction

noncomputable section

namespace LocallyConvex.Manifolds

/-- Smooth `1`-periodic functions, as a submodule of `ℝ → ℝ`. -/
def perSmoothSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | ContDiff ℝ ∞ u ∧ Periodic u 1}
  add_mem' hu hv := ⟨hu.1.add hv.1, hu.2.add hv.2⟩
  zero_mem' := ⟨contDiff_const, fun _ ↦ rfl⟩
  smul_mem' c _ hu := ⟨hu.1.const_smul c, hu.2.smul c⟩

/-- The space `C^∞_per` of smooth `1`-periodic functions. It is a type synonym of the submodule,
so that it does not inherit the topology of pointwise convergence. -/
def CInfPer : Type := perSmoothSubmodule

namespace CInfPer

instance : AddCommGroup CInfPer := inferInstanceAs (AddCommGroup perSmoothSubmodule)
instance : Module ℝ CInfPer := inferInstanceAs (Module ℝ perSmoothSubmodule)

instance : CoeFun CInfPer (fun _ ↦ ℝ → ℝ) := ⟨fun u ↦ (u : perSmoothSubmodule).1⟩

theorem contDiff (u : CInfPer) : ContDiff ℝ ∞ u := (u : perSmoothSubmodule).2.1

theorem periodic (u : CInfPer) : Periodic u 1 := (u : perSmoothSubmodule).2.2

/-- A smooth periodic function as an element of `C^∞_per`. -/
def mk (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Periodic f 1) : CInfPer :=
  (⟨f, hf, hp⟩ : perSmoothSubmodule)

@[simp] theorem coe_mk (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hp : Periodic f 1) :
    ⇑(mk f hf hp) = f := rfl

@[ext] theorem ext {u v : CInfPer} (h : ∀ x, u x = v x) : u = v :=
  Subtype.ext (funext h)

@[simp] theorem coe_add (u v : CInfPer) : ⇑(u + v) = u + v := rfl
@[simp] theorem coe_smul (c : ℝ) (u : CInfPer) : ⇑(c • u) = c • ⇑u := rfl
@[simp] theorem coe_zero : ⇑(0 : CInfPer) = 0 := rfl
@[simp] theorem coe_neg (u : CInfPer) : ⇑(-u) = -⇑u := rfl
@[simp] theorem coe_sub (u v : CInfPer) : ⇑(u - v) = u - v := rfl

theorem contDiff_nat (u : CInfPer) (k : ℕ) : ContDiff ℝ k u :=
  u.contDiff.of_le (mod_cast le_top)

/-! ### The derivatives as bounded continuous functions -/

theorem continuous_iteratedDeriv (u : CInfPer) (k : ℕ) : Continuous (iteratedDeriv k u) :=
  (u.contDiff_nat k).continuous_iteratedDeriv' k

theorem differentiable_iteratedDeriv (u : CInfPer) (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k u) :=
  u.contDiff.differentiable_iteratedDeriv k (mod_cast WithTop.coe_lt_top _)

theorem periodic_iteratedDeriv (u : CInfPer) (k : ℕ) : Periodic (iteratedDeriv k u) 1 := by
  intro x
  have h := congrFun (iteratedDeriv_comp_add_const (n := k) (f := ⇑u) (s := 1)) x
  have hu : (fun z ↦ u (z + 1)) = ⇑u := funext u.periodic
  rw [hu] at h
  exact h.symm

theorem exists_bound (u : CInfPer) (k : ℕ) : ∃ C, ∀ x, ‖iteratedDeriv k u x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    ((u.periodic_iteratedDeriv k).compact_of_continuous one_ne_zero
      (u.continuous_iteratedDeriv k)).isBounded
  exact ⟨C, fun x ↦ hC _ ⟨x, rfl⟩⟩

/-- The `k`-th derivative of `u`, as a bounded continuous function. -/
def derivBCF (k : ℕ) (u : CInfPer) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (iteratedDeriv k u)
    (u.continuous_iteratedDeriv k) (u.exists_bound k).choose (u.exists_bound k).choose_spec

@[simp] theorem coe_derivBCF (k : ℕ) (u : CInfPer) : ⇑(derivBCF k u) = iteratedDeriv k u := rfl

/-- `u ↦ u^{(k)}`, as a linear map `C^∞_per → BC(ℝ)`. -/
def derivL (k : ℕ) : CInfPer →ₗ[ℝ] (ℝ →ᵇ ℝ) where
  toFun := derivBCF k
  map_add' u v := by
    ext x
    simp only [coe_derivBCF, FunLike.coe_add, Pi.add_apply, coe_add]
    exact iteratedDeriv_add ((u.contDiff_nat k).contDiffAt) ((v.contDiff_nat k).contDiffAt)
  map_smul' c u := by
    ext x
    simp only [coe_derivBCF, FunLike.coe_smul, coe_smul, RingHom.id_apply]
    exact iteratedDeriv_const_smul ((u.contDiff_nat k).contDiffAt) c

/-- The embedding `u ↦ (u^{(k)})_k` into a countable product of Banach spaces. -/
def J : CInfPer →ₗ[ℝ] (ℕ → ℝ →ᵇ ℝ) := LinearMap.pi derivL

theorem J_apply (u : CInfPer) (k : ℕ) : J u k = derivBCF k u := rfl

theorem J_injective : Injective J := by
  intro u v h
  ext x
  have := congrArg (fun G : ℕ → ℝ →ᵇ ℝ ↦ G 0 x) h
  simpa [J_apply] using this

/-! ### Topology and uniform structure -/

/-- The uniform structure induced by `J` (uniform convergence of every derivative). -/
instance : UniformSpace CInfPer := UniformSpace.comap J inferInstance

theorem isUniformInducing_J : IsUniformInducing J := ⟨rfl⟩

theorem isEmbedding_J : Topology.IsEmbedding J :=
  ⟨isUniformInducing_J.isInducing, J_injective⟩

instance : IsUniformAddGroup CInfPer := IsUniformAddGroup.comap J.toAddMonoidHom

instance : ContinuousSMul ℝ CInfPer := continuousSMul_induced J

instance : LocallyConvexSpace ℝ CInfPer := LocallyConvexSpace.induced J

instance : T2Space CInfPer := isEmbedding_J.t2Space

instance : TopologicalSpace.MetrizableSpace CInfPer := isEmbedding_J.metrizableSpace

theorem continuous_derivBCF (k : ℕ) : Continuous (derivBCF k) :=
  (continuous_apply k).comp isUniformInducing_J.isInducing.continuous

/-- **Convergence in `C^∞_per` is uniform convergence of every derivative.** -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} {u : ι → CInfPer} {v : CInfPer} :
    Tendsto u l (𝓝 v) ↔
      ∀ k, TendstoUniformly (fun i ↦ iteratedDeriv k (u i)) (iteratedDeriv k v) l := by
  rw [isUniformInducing_J.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  refine forall_congr' fun k ↦ ?_
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly

/-- The seminorm `p_k(u) = sup_x |u^{(k)}(x)|`. -/
def seminorm (k : ℕ) : Seminorm ℝ CInfPer := (normSeminorm ℝ (ℝ →ᵇ ℝ)).comp (derivL k)

theorem seminorm_apply (k : ℕ) (u : CInfPer) : seminorm k u = ‖derivBCF k u‖ := rfl

theorem norm_iteratedDeriv_le_seminorm (k : ℕ) (u : CInfPer) (x : ℝ) :
    ‖iteratedDeriv k u x‖ ≤ seminorm k u :=
  (derivBCF k u).norm_coe_le_norm x

theorem seminorm_le_iff {k : ℕ} {u : CInfPer} {C : ℝ} (hC : 0 ≤ C) :
    seminorm k u ≤ C ↔ ∀ x, ‖iteratedDeriv k u x‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

/-! ### Completeness -/

/-- **The range of `J` is closed**: if `u_n^{(k)} → g_k` uniformly for every `k`, then `g_0` is
smooth and periodic, with `g_0^{(k)} = g_k`. -/
theorem isClosed_range_J : IsClosed (range J) := by
  refine IsSeqClosed.isClosed fun {U} {G} hU hlim ↦ ?_
  choose u hu using hU
  have hunif : ∀ k, TendstoUniformly (fun n ↦ iteratedDeriv k (u n)) (G k) atTop := by
    intro k
    have h := ((continuous_apply k).tendsto G).comp hlim
    have h' : Tendsto (fun n ↦ derivBCF k (u n)) atTop (𝓝 (G k)) := by
      refine h.congr fun n ↦ ?_
      simp only [comp_apply, ← hu n, J_apply]
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h'
  have hderiv : ∀ k x, HasDerivAt (G k) (G (k + 1) x) x := by
    intro k x
    refine hasDerivAt_of_tendstoUniformly (hunif (k + 1)) (Eventually.of_forall fun n y ↦ ?_)
      (fun y ↦ (hunif k).tendsto_at y) x
    rw [iteratedDeriv_succ]
    exact ((u n).differentiable_iteratedDeriv k y).hasDerivAt
  have hiter : ∀ k, iteratedDeriv k (G 0) = G k := by
    intro k
    induction k with
    | zero => rw [iteratedDeriv_zero]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hderiv k x).deriv
  have hsm : ContDiff ℝ ∞ (G 0) := by
    refine contDiff_of_differentiable_iteratedDeriv (n := ⊤) fun m _ ↦ ?_
    rw [hiter m]
    exact fun x ↦ (hderiv m x).differentiableAt
  have hper : Periodic (G 0) 1 := by
    intro x
    have h1 := (hunif 0).tendsto_at (x + 1)
    have h2 := (hunif 0).tendsto_at x
    simp only [iteratedDeriv_zero] at h1 h2
    have h1' : Tendsto (fun n ↦ u n x) atTop (𝓝 (G 0 (x + 1))) :=
      h1.congr fun n ↦ (u n).periodic x
    exact tendsto_nhds_unique h1' h2
  refine ⟨mk (G 0) hsm hper, funext fun k ↦ ?_⟩
  ext x
  rw [J_apply, coe_derivBCF, coe_mk, hiter k]

instance : CompleteSpace CInfPer :=
  (completeSpace_iff_isComplete_range isUniformInducing_J).mpr isClosed_range_J.isComplete

end CInfPer

end LocallyConvex.Manifolds
