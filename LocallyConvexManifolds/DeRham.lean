/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.DifferentialForm

/-!
# De Rham cohomology

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, §3.6.

Since `d ∘ d = 0`, the space `B^n_dR(M, F)` of exact `n`-forms is contained in the space
`Z^n_dR(M, F)` of closed ones, and the `F`-valued de Rham cohomology is the quotient
`H^n_dR(M, F) = Z^n_dR(M, F) / B^n_dR(M, F)`, with `B^0_dR(M, F) = 0` (Glöckner–Neeb,
Definition 3.6.11).

## Main definitions and results

* `closedForms`, `exactForms`, `exactForms_le_closedForms`;
* `DeRham E M F n`: the de Rham cohomology space;
* `deRhamMap`: a smooth map `φ : N → M` induces linear maps `φ* : H^n_dR(M, F) → H^n_dR(N, F)`,
  since pullbacks of closed (exact) forms are closed (exact) by Lemma 3.6.13; this is
  functorial (`deRhamMap_id`, `deRhamMap_comp`). This is the functoriality stated at the
  beginning of the subsection on the Poincaré Lemma in Glöckner–Neeb;
* `isClosed_iff_isLocallyConstant`: a function is closed if and only if it is locally constant
  (Glöckner–Neeb, Remark 3.6.12 (b)), and `deRhamZeroEquiv : H^0_dR(M, F) ≃ Z^0_dR(M, F)`.

The proof of Remark 3.6.12 (b) uses that the model space is locally convex: a `C¹` map with
vanishing derivative is constant on convex open sets.
-/

open Set Function Filter
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace DifferentialForm

variable (E M F) in
/-- The closed `n`-forms `Z^n_dR(M, F) = ker d` (Glöckner–Neeb, Definition 3.6.11). -/
def closedForms (n : ℕ) : Submodule ℝ (DifferentialForm E M F n) :=
  LinearMap.ker (dLinear E M F n)

variable (E M F) in
/-- The exact `n`-forms `B^n_dR(M, F) = d(Ω^{n-1}(M, F))`, with `B^0_dR(M, F) = 0`
(Glöckner–Neeb, Definition 3.6.11). -/
def exactForms : (n : ℕ) → Submodule ℝ (DifferentialForm E M F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dLinear E M F n)

theorem mem_closedForms {n : ℕ} {ω : DifferentialForm E M F n} :
    ω ∈ closedForms E M F n ↔ ω.IsClosed :=
  ⟨fun h x v ↦ by rw [show ω.d = 0 from h]; rfl, fun h ↦ ext h⟩

theorem mem_exactForms_succ {n : ℕ} {ω : DifferentialForm E M F (n + 1)} :
    ω ∈ exactForms E M F (n + 1) ↔ ω.IsExact :=
  Iff.rfl

/-- Exact forms are closed. -/
theorem exactForms_le_closedForms (n : ℕ) : exactForms E M F n ≤ closedForms E M F n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨η, rfl⟩
    exact mem_closedForms.mpr (IsExact.isClosed ⟨η, rfl⟩)

end DifferentialForm

open DifferentialForm

variable (E M F) in
/-- The `F`-valued de Rham cohomology `H^n_dR(M, F) = Z^n_dR(M, F) / B^n_dR(M, F)`
(Glöckner–Neeb, Definition 3.6.11). -/
abbrev DeRham (n : ℕ) : Type _ :=
  closedForms E M F n ⧸ (exactForms E M F n).comap (closedForms E M F n).subtype

/-- The cohomology class of a closed form. -/
abbrev DeRham.mk {n : ℕ} (ω : DifferentialForm E M F n) (hω : ω.IsClosed) : DeRham E M F n :=
  Submodule.Quotient.mk ⟨ω, mem_closedForms.mpr hω⟩

/-- Two closed forms define the same class if and only if they differ by an exact form. -/
theorem DeRham.mk_eq_mk_iff {n : ℕ} {ω η : DifferentialForm E M F n} (hω : ω.IsClosed)
    (hη : η.IsClosed) : DeRham.mk ω hω = DeRham.mk η hη ↔ ω - η ∈ exactForms E M F n := by
  rw [Submodule.Quotient.eq]
  rfl

/-! ### Remark 3.6.12 (b): closed functions are the locally constant ones -/

namespace DifferentialForm

/-- The underlying function of a `0`-form. -/
def toFunction (ω : DifferentialForm E M F 0) (x : M) : F := ω x Fin.elim0

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem localRep_zero (ω : DifferentialForm E M F 0) (i : atlas E M) (z : E) (w : Fin 0 → E) :
    ω.localRep i (z, w) = ω.toFunction (i.1.symm z) := by
  simp only [localRep, formLocalRep, toFunction]
  congr 1
  exact Subsingleton.elim _ _

/-- The exterior derivative of a `0`-form is the derivative of its local representative. -/
theorem d_zero_apply (ω : DifferentialForm E M F 0) (x : M) (v : Fin 1 → E) :
    ω.d x v = dMB (ω.toFunction ∘ (chartAt E x).symm) (chartAt E x x, v 0) := by
  rw [d_apply, IsLocalForm.dLoc_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, localRep_zero]
  rfl

/-- **Closed functions are the locally constant ones** (Glöckner–Neeb, Remark 3.6.12 (b)). -/
theorem isClosed_iff_isLocallyConstant (ω : DifferentialForm E M F 0) :
    ω.IsClosed ↔ IsLocallyConstant ω.toFunction := by
  constructor
  · intro hω
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    set c := chartAt E x
    set i : atlas E M := prefChart x
    have hT := c.open_target
    have hcx : c x ∈ c.target := c.map_source (mem_chart_source E x)
    -- the local representative `g = f ∘ c⁻¹` is `C¹` with vanishing derivative
    set g := ω.toFunction ∘ c.symm
    have hg : ContDiffMBOn 1 g c.target := by
      have h := (ω.isLocalForm_localRep i).smooth_slice hT Fin.elim0 1
      exact ContDiffMBOn.congr_of_isOpen hT (fun z _ ↦ localRep_zero ω i z _) h
    have hdg : ∀ z ∈ c.target, ∀ u, dMB g (z, u) = 0 := by
      intro z hz u
      have h := ω.localRep_d i hz ![u]
      rw [IsLocalForm.dLoc_apply, Fin.sum_univ_one] at h
      simp only [Fin.val_zero, pow_zero, one_smul, localRep_zero] at h
      have h0 : ω.d.localRep i (z, ![u]) = 0 := hω _ _
      rw [h0] at h
      exact h.symm
    -- a convex open neighbourhood of `c x` in the chart
    obtain ⟨C, ⟨hC, hCconv⟩, hCT⟩ :=
      (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (c x)).mem_iff.mp (hT.mem_nhds hcx)
    have hCo : IsOpen (interior C) := isOpen_interior
    have hxC : c x ∈ interior C := mem_interior_iff_mem_nhds.mpr hC
    have hconst : ∀ z ∈ interior C, g z = g (c x) := fun z hz ↦
      ContDiffMBOn.eqOn_of_dMB_eq_zero hCo hCconv.interior.isPreconnected
        (hg.mono (interior_subset.trans hCT))
        (fun z' hz' u ↦ hdg z' (hCT (interior_subset hz')) u) hz hxC
    have hnhds : c.source ∩ c ⁻¹' interior C ∈ 𝓝 x :=
      (c.continuousOn.isOpen_inter_preimage c.open_source hCo).mem_nhds
        ⟨mem_chart_source E x, hxC⟩
    filter_upwards [hnhds] with y hy
    have h := hconst _ hy.2
    simp only [g, comp_apply, c.left_inv hy.1, c.left_inv (mem_chart_source E x)] at h
    exact h
  · intro hf x v
    rw [d_zero_apply]
    set c := chartAt E x
    have hcx : c x ∈ c.target := c.map_source (mem_chart_source E x)
    have hev : ω.toFunction ∘ c.symm =ᶠ[𝓝 (c x)] fun _ ↦ ω.toFunction x := by
      have h1 : ∀ᶠ y in 𝓝 x, ω.toFunction y = ω.toFunction x :=
        (IsLocallyConstant.iff_eventually_eq _).mp hf x
      have h2 : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
        have := c.continuousAt_symm hcx
        rwa [ContinuousAt, c.left_inv (mem_chart_source E x)] at this
      exact h2.eventually h1
    rw [dMB_congr_of_eventuallyEq hev]
    have h0 : HasDirDerivAt (fun _ : E ↦ ω.toFunction x) (c x) (v 0) 0 := by
      simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
    exact h0.dMB_eq

end DifferentialForm

/-- `H^0_dR(M, F) ≃ Z^0_dR(M, F)`, the space of closed, i.e. locally constant, functions
(Glöckner–Neeb, Remark 3.6.12 (b)). -/
def deRhamZeroEquiv : DeRham E M F 0 ≃ₗ[ℝ] closedForms E M F 0 :=
  Submodule.quotEquivOfEqBot _ (by simp [exactForms])

/-! ### Functoriality -/

section Functoriality

variable {E₀ : Type u} [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀]
  [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E₀ N] [MBManifold E₀ N] {φ : N → M}

namespace DifferentialForm

/-- Pullbacks of closed forms are closed. -/
theorem IsClosed.pullback (hφ : SmoothMBM E₀ E φ) {n : ℕ} {ω : DifferentialForm E M F n}
    (hω : ω.IsClosed) : (ω.pullback hφ).IsClosed := by
  intro x v
  rw [d_pullback, show ω.d = 0 from ext hω]
  rfl

/-- Pullbacks of exact forms are exact. -/
theorem IsExact.pullback (hφ : SmoothMBM E₀ E φ) {n : ℕ} {ω : DifferentialForm E M F (n + 1)}
    (hω : ω.IsExact) : (ω.pullback hφ).IsExact := by
  obtain ⟨η, rfl⟩ := hω
  exact ⟨η.pullback hφ, d_pullback hφ η⟩

theorem pullbackLinear_mem_exactForms (hφ : SmoothMBM E₀ E φ) {n : ℕ}
    {ω : DifferentialForm E M F n} (hω : ω ∈ exactForms E M F n) :
    pullbackLinear n hφ ω ∈ exactForms E₀ N F n := by
  cases n with
  | zero =>
    rw [exactForms, Submodule.mem_bot] at hω ⊢
    rw [hω, map_zero]
  | succ n => exact IsExact.pullback hφ hω

end DifferentialForm

/-- The pullback of closed forms, as a linear map. -/
def closedPullback (hφ : SmoothMBM E₀ E φ) (n : ℕ) :
    closedForms E M F n →ₗ[ℝ] closedForms E₀ N F n :=
  (pullbackLinear n hφ).restrict fun _ hω ↦
    mem_closedForms.mpr ((mem_closedForms.mp hω).pullback hφ)

/-- The linear map `φ* : H^n_dR(M, F) → H^n_dR(N, F)` induced by a smooth map `φ : N → M`. -/
def deRhamMap (hφ : SmoothMBM E₀ E φ) (n : ℕ) : DeRham E M F n →ₗ[ℝ] DeRham E₀ N F n :=
  Submodule.mapQ _ _ (closedPullback hφ n) fun _ hω ↦
    pullbackLinear_mem_exactForms hφ hω

theorem deRhamMap_mk (hφ : SmoothMBM E₀ E φ) {n : ℕ} (ω : DifferentialForm E M F n)
    (hω : ω.IsClosed) :
    deRhamMap hφ n (DeRham.mk ω hω) = DeRham.mk (ω.pullback hφ) (hω.pullback hφ) :=
  rfl

omit [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  [MBManifold E₀ N] in
/-- `id* = id` on de Rham cohomology. -/
theorem deRhamMap_id (n : ℕ) :
    deRhamMap (F := F) (fun k ↦ smoothMBMOn_id (E := E) (M := M) isOpen_univ k) n =
      LinearMap.id := by
  ext ⟨ω, hω⟩
  simp only [LinearMap.coe_comp, comp_apply, Submodule.mkQ_apply, LinearMap.id_comp]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (pullback_id ω)

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {P : Type*} [TopologicalSpace P] [ChartedSpace E₁ P] [MBManifold E₁ P] {ψ : P → N}

/-- `(φ ∘ ψ)* = ψ* ∘ φ*` on de Rham cohomology. -/
theorem deRhamMap_comp (hφ : SmoothMBM E₀ E φ) (hψ : SmoothMBM E₁ E₀ ψ) (n : ℕ) :
    deRhamMap (F := F) (hφ.comp hψ) n = (deRhamMap hψ n).comp (deRhamMap hφ n) := by
  ext ⟨ω, hω⟩
  simp only [LinearMap.coe_comp, comp_apply, Submodule.mkQ_apply]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (pullback_pullback hφ hψ ω).symm

end Functoriality

end LocallyConvex.Manifolds
