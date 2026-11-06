/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexAnalysis.Higher
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Differential forms on open subsets of locally convex spaces

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, §3.6.

Let `E`, `F` be Hausdorff locally convex spaces and `U ⊆ E` open. A *local `n`-form* on `U` is a
map `ω : E × Eⁿ → F` which is smooth on `U × Eⁿ` in the sense of Michal–Bastiani and alternating
`n`-linear in the vectors (`IsLocalForm`); these are the local representatives of differential
forms on manifolds (Glöckner–Neeb, (3.26)).

## Main definitions and results

* `dLoc`: the local exterior derivative
  `dω(y)(v₀, …, vₙ) = ∑ᵢ (-1)ⁱ ∂_{vᵢ} ω(y)(v₀, …, v̂ᵢ, …, vₙ)` (Glöckner–Neeb, (3.33)), where
  `∂_{vᵢ}` differentiates in the base point;
* `IsLocalForm.dLoc`: `dω` is a local `(n + 1)`-form;
* `IsLocalForm.dLoc_dLoc`: `d ∘ d = 0`, from the symmetry of second derivatives;
* `pullbackLoc`, `IsLocalForm.pullback`: the pullback
  `(τ*ω)(y)(v₁, …, vₙ) = ω(τ y)(dτ(y) v₁, …, dτ(y) vₙ)` along a smooth map `τ : U → V`;
* `IsLocalForm.dLoc_pullbackLoc`: naturality, `d(τ*ω) = τ*(dω)`. The terms with the second
  derivative of `τ` cancel because it is symmetric
  (`AlternatingMap.sum_neg_one_pow_smul_sum_update_eq_zero`).

The signs follow Mathlib's `AlternatingMap.alternatizeUncurryFin`, which is also the formula of
Mathlib's `extDeriv` on normed spaces. No completeness of `E` or `F` is assumed.
-/

open Set Function Fin

namespace AlternatingMap

variable {R : Type*} {M M' N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup M']
  [AddCommGroup N] [Module R M] [Module R M'] [Module R N] {n : ℕ}

/-- Inserting a vector at the `k`-th place of a tuple from which the `k`-th entry was removed
replaces that entry. -/
theorem map_update_eq_neg_one_pow_smul (α : M [⋀^Fin (n + 1)]→ₗ[R] N) (z : Fin (n + 1) → M)
    (k : Fin (n + 1)) (x : M) :
    α (update z k x) = (-1) ^ (k : ℕ) • α (Matrix.vecCons x (k.removeNth z)) := by
  rw [← map_insertNth, insertNth_removeNth]

/-- The terms with a symmetric bilinear map `h` cancel in the alternating sum:
`∑ᵢ (-1)ⁱ ∑ₖ α(T w₁, …, h(wₖ, vᵢ), …, T wₙ) = 0`, where `w` is `v` with `vᵢ` removed. This is
the algebraic fact behind the naturality of the exterior derivative: the second derivative of a
change of variables drops out because it is symmetric. -/
theorem sum_neg_one_pow_smul_sum_update_eq_zero (α : M [⋀^Fin n]→ₗ[R] N) (T : M' →ₗ[R] M)
    (h : M' →ₗ[R] M' →ₗ[R] M) (hsymm : ∀ a b, h a b = h b a) (v : Fin (n + 1) → M') :
    ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • ∑ k : Fin n,
      α (update (T ∘ i.removeNth v) k (h (i.removeNth v k) (v i))) = 0 := by
  cases n with
  | zero => simp
  | succ m =>
    -- `G u b` is the `m`-form `w ↦ α(h(b, u), T w₁, …, T wₘ)`
    let G : M' →ₗ[R] M' →ₗ[R] M' [⋀^Fin m]→ₗ[R] N :=
      LinearMap.mk₂ R (fun u b ↦ (α.curryLeft (h b u)).compLinearMap T)
        (fun u u' b ↦ by ext w; simp)
        (fun c u b ↦ by ext w; simp)
        (fun u b b' ↦ by ext w; simp)
        (fun c u b ↦ by ext w; simp)
    have hG : ∀ u b, G u b = G b u := fun u b ↦ by
      ext w; simp [G, hsymm b u]
    have key : ∀ (u : M') (w : Fin (m + 1) → M'),
        ∑ k : Fin (m + 1), α (update (T ∘ w) k (h (w k) u)) =
          alternatizeUncurryFin (G u) w := by
      intro u w
      rw [alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_update_eq_neg_one_pow_smul]
      simp [G, comp_def]; rfl
    have := alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
      (f := G) hG
    have hv := congrArg (fun A ↦ A v) this
    simp only [alternatizeUncurryFin_apply, LinearMap.coe_comp, comp_apply,
      alternatizeUncurryFinLM_apply, zero_apply] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [key, alternatizeUncurryFin_apply]

end AlternatingMap

namespace LocallyConvex.Manifolds

open Filter LocallyConvex.Analysis
open scoped Topology

/-- The double alternating sum of a function that is symmetric in its first two arguments
vanishes: `∑ᵢ (-1)ⁱ ∑ⱼ (-1)ʲ S(vᵢ, wⱼ, w without wⱼ) = 0`, where `w` is `v` without `vᵢ`.
This is the combinatorial fact behind `d ∘ d = 0`; no linearity of `S` is needed. -/
theorem sum_neg_one_pow_smul_sum_eq_zero_of_symm {R M N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {n : ℕ} (S : M → M → (Fin n → M) → N) (hS : ∀ a b w, S a b w = S b a w)
    (v : Fin (n + 2) → M) :
    ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) •
      S (v i) (i.removeNth v j) (j.removeNth (i.removeNth v)) = 0 := by
  simp only [Finset.smul_sum, smul_smul, ← pow_add]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_Ici] at hj
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  have hw : j.removeNth (i.castSucc.removeNth v) = i.removeNth (j.succ.removeNth v) := by
    rw [Fin.removeNth_removeNth_eq_swap, H₁, H₂]
  have h₁ : i.castSucc.removeNth v j = v j.succ := by simp [Fin.removeNth, H₁]
  have h₂ : j.succ.removeNth v i = v i.castSucc := by simp [Fin.removeNth, H₃]
  rw [hw, h₁, h₂, hS (v j.succ), Fin.val_castSucc, Fin.val_succ,
    show (j : ℕ) + 1 + i = (i + j) + 1 by omega, pow_succ, mul_neg_one, neg_smul,
    add_neg_cancel]

universe u

section Pi

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem hasDirDerivAt_pi {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    {n : ℕ} {f : E₁ → Fin n → F} {x h : E₁} {y : Fin n → F} :
    HasDirDerivAt f x h y ↔ ∀ k, HasDirDerivAt (fun z ↦ f z k) x h (y k) := by
  simp only [HasDirDerivAt, tendsto_pi_nhds]
  rfl

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasDirDerivAt.sum {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    {ι : Type*} (s : Finset ι) {f : ι → E₁ → F} {x h : E₁} {y : ι → F}
    (hf : ∀ i ∈ s, HasDirDerivAt (f i) x h (y i)) :
    HasDirDerivAt (fun z ↦ ∑ i ∈ s, f i z) x h (∑ i ∈ s, y i) := by
  refine (tendsto_finsetSum s hf).congr fun t ↦ ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Maps into `Fⁿ` whose components are `C^k` are `C^k`. -/
theorem ContDiffMBOn.pi {n : ℕ} : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → Fin n → F} {U : Set E₁},
    IsOpen U → (∀ i, ContDiffMBOn k (fun x ↦ f x i) U) → ContDiffMBOn k f U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ f U _ hf
    exact continuousOn_pi.mpr hf
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U hU hf
    have hd : ∀ x ∈ U, ∀ h,
        HasDirDerivAt f x h (fun i ↦ dMB (fun z ↦ f z i) (x, h)) :=
      fun x hx h ↦ hasDirDerivAt_pi.mpr fun i ↦ (hf i).2.1 x hx h
    have hdeq : EqOn (fun p i ↦ dMB (fun z ↦ f z i) p) (dMB f) (U ×ˢ univ) :=
      fun p hp ↦ ((hd p.1 hp.1 p.2).dMB_eq).symm
    refine ⟨continuousOn_pi.mpr fun i ↦ (hf i).1, fun x hx h ↦ ?_,
      ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) hdeq
        (ih (hU.prod isOpen_univ) fun i ↦ (hf i).2.2)⟩
    rw [← hdeq ⟨hx, mem_univ h⟩]
    exact hd x hx h

theorem ContDiffMBOn.const_smul {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U : Set E₁} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (c : ℝ) : ContDiffMBOn k (fun x ↦ c • f x) U :=
  ContDiffMBOn.comp hU isOpen_univ ((c • ContinuousLinearMap.id ℝ F).contDiffMBOn k univ) hf
    (mapsTo_univ _ _)

end Pi

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {n : ℕ}

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- The signs `(-1)ᵏ` act in the same way as real scalars and as integers. -/
theorem neg_one_pow_smul_eq_zsmul (k : ℕ) (x : F) : (-1 : ℝ) ^ k • x = (-1 : ℤ) ^ k • x := by
  rw [← Int.cast_smul_eq_zsmul ℝ]
  push_cast
  rfl

/-! ### Directional derivatives of linear combinations -/

section LinearCombination

variable {g g₁ g₂ : E → F} {U : Set E} {y : E}

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
theorem dMB_eq_add_of_eqOn (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffMBOn 1 g₁ U)
    (h₂ : ContDiffMBOn 1 g₂ U) (hg : EqOn g (fun z ↦ g₁ z + g₂ z) U) (u : E) :
    dMB g (y, u) = dMB g₁ (y, u) + dMB g₂ (y, u) :=
  (((h₁.2.1 y hy u).add (h₂.2.1 y hy u)).congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
theorem dMB_eq_smul_of_eqOn (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffMBOn 1 g₁ U) (c : ℝ)
    (hg : EqOn g (fun z ↦ c • g₁ z) U) (u : E) : dMB g (y, u) = c • dMB g₁ (y, u) :=
  (((h₁.2.1 y hy u).const_smul c).congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
theorem dMB_eq_zero_of_eqOn (hU : IsOpen U) (hy : y ∈ U) (hg : EqOn g 0 U) (u : E) :
    dMB g (y, u) = 0 := by
  have h0 : HasDirDerivAt (fun _ : E ↦ (0 : F)) y u 0 := by
    simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
  exact (h0.congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

end LinearCombination

/-! ### Local forms -/

/-- A smooth `F`-valued `n`-form on an open set `U ⊆ E`, given as a function on `U × Eⁿ`
(Glöckner–Neeb, (3.26)): smooth, and alternating `n`-linear in the vectors. -/
structure IsLocalForm (n : ℕ) (ω : E × (Fin n → E) → F) (U : Set E) : Prop where
  smooth : SmoothMBOn ω (U ×ˢ univ)
  alternating : ∀ y ∈ U, ∃ A : E [⋀^Fin n]→ₗ[ℝ] F, ∀ v, ω (y, v) = A v

/-- The local exterior derivative (Glöckner–Neeb, (3.33)):
`dω(y)(v₀, …, vₙ) = ∑ᵢ (-1)ⁱ ∂_{vᵢ} ω(y)(v₀, …, v̂ᵢ, …, vₙ)`, where `∂_{vᵢ}` differentiates in
the base point. -/
noncomputable def dLoc (ω : E × (Fin n → E) → F) (p : E × (Fin (n + 1) → E)) : F :=
  ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) • dMB (fun z ↦ ω (z, i.removeNth p.2)) (p.1, p.2 i)

namespace IsLocalForm

variable {ω : E × (Fin n → E) → F} {U : Set E}

theorem smooth_slice (hω : IsLocalForm n ω U) (hU : IsOpen U) (w : Fin n → E) :
    SmoothMBOn (fun z ↦ ω (z, w)) U := fun k ↦
  (hω.smooth k).comp hU (hU.prod isOpen_univ)
    (ContDiffMBOn.prodMk hU (smoothMBOn_id U k) (contDiffMBOn_const k w U))
    fun _ hz ↦ ⟨hz, mem_univ _⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem map_update_add (hω : IsLocalForm n ω U) {z : E} (hz : z ∈ U) (w : Fin n → E)
    (k : Fin n) (a b : E) :
    ω (z, update w k (a + b)) = ω (z, update w k a) + ω (z, update w k b) := by
  obtain ⟨A, hA⟩ := hω.alternating z hz
  simp only [hA, AlternatingMap.map_update_add]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem map_update_smul (hω : IsLocalForm n ω U) {z : E} (hz : z ∈ U) (w : Fin n → E)
    (k : Fin n) (c : ℝ) (a : E) :
    ω (z, update w k (c • a)) = c • ω (z, update w k a) := by
  obtain ⟨A, hA⟩ := hω.alternating z hz
  simp only [hA, AlternatingMap.map_update_smul]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem map_eq_zero_of_eq (hω : IsLocalForm n ω U) {z : E} (hz : z ∈ U) {w : Fin n → E}
    {i j : Fin n} (hw : w i = w j) (hij : i ≠ j) : ω (z, w) = 0 := by
  obtain ⟨A, hA⟩ := hω.alternating z hz
  rw [hA, A.map_eq_zero_of_eq w hw hij]

/-- The partial derivative `u ↦ (w ↦ ∂ᵤ ω(y)(w))` is linear in `u` with values in alternating
maps. -/
theorem exists_partial (hω : IsLocalForm n ω U) (hU : IsOpen U) {y : E} (hy : y ∈ U) :
    ∃ L : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] F, ∀ u w, dMB (fun z ↦ ω (z, w)) (y, u) = L u w := by
  classical
  have h1 : ∀ w, ContDiffMBOn 1 (fun z ↦ ω (z, w)) U := fun w ↦ hω.smooth_slice hU w 1
  let A : E → E [⋀^Fin n]→ₗ[ℝ] F := fun u ↦
    { toFun := fun w ↦ dMB (fun z ↦ ω (z, w)) (y, u)
      map_update_add' := fun w k a b ↦ by
        convert dMB_eq_add_of_eqOn hU hy (h1 _) (h1 _)
          (fun z hz ↦ hω.map_update_add hz w k a b) u
      map_update_smul' := fun w k c a ↦ by
        convert dMB_eq_smul_of_eqOn hU hy (h1 _) c
          (fun z hz ↦ hω.map_update_smul hz w k c a) u
      map_eq_zero_of_eq' := fun w i j hw hij ↦
        dMB_eq_zero_of_eqOn hU hy (fun z hz ↦ hω.map_eq_zero_of_eq hz hw hij) u }
  refine ⟨{ toFun := A, map_add' := fun u u' ↦ ?_, map_smul' := fun c u ↦ ?_ }, fun u w ↦ rfl⟩
  · ext w; exact (h1 w).dMB_add hU hy u u'
  · ext w; exact (h1 w).dMB_smul hy c u

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem dLoc_eq_alternatizeUncurryFin {y : E}
    {L : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] F} (hL : ∀ u w, dMB (fun z ↦ ω (z, w)) (y, u) = L u w)
    (v : Fin (n + 1) → E) : dLoc ω (y, v) = AlternatingMap.alternatizeUncurryFin L v := by
  simp only [dLoc, hL, AlternatingMap.alternatizeUncurryFin_apply, neg_one_pow_smul_eq_zsmul]

/-- The removal of the `i`-th vector, as a continuous linear map. -/
noncomputable def removeNthCLM (i : Fin (n + 1)) : (Fin (n + 1) → E) →L[ℝ] (Fin n → E) :=
  ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (i.succAbove j)

/-- `(y, v) ↦ ((y, v without vᵢ), (vᵢ, 0))`, the point and direction of the `i`-th term of
`dLoc`. -/
noncomputable def termCLM (i : Fin (n + 1)) :
    E × (Fin (n + 1) → E) →L[ℝ] (E × (Fin n → E)) × (E × (Fin n → E)) :=
  ((ContinuousLinearMap.fst ℝ E _).prod
      (removeNthCLM i ∘L ContinuousLinearMap.snd ℝ E _)).prod
    (((ContinuousLinearMap.proj i) ∘L ContinuousLinearMap.snd ℝ E _).prod 0)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem dLoc_eq_sum_dMB (ω : E × (Fin n → E) → F) :
    dLoc ω = fun p ↦ ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) • dMB ω (termCLM i p) := by
  funext p
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← dMB_slice]
  rfl

theorem smoothMBOn_dLoc (hω : IsLocalForm n ω U) (hU : IsOpen U) :
    SmoothMBOn (dLoc ω) (U ×ˢ univ) := by
  intro k
  have hU' : IsOpen (U ×ˢ (univ : Set (Fin (n + 1) → E))) := hU.prod isOpen_univ
  rw [dLoc_eq_sum_dMB]
  refine ContDiffMBOn.sum _ hU' fun i _ ↦ ContDiffMBOn.const_smul hU' ?_ _
  have h := ((hω.smooth (k + 1)).2.2).comp_clm (termCLM i)
    ((hU.prod isOpen_univ).prod isOpen_univ)
  have hpre : (termCLM (E := E) i) ⁻¹' ((U ×ˢ univ) ×ˢ univ) = U ×ˢ univ := by
    ext p; simp [termCLM]
  rw [hpre] at h
  exact h

/-- The exterior derivative of a local form is a local form. -/
theorem dLoc (hω : IsLocalForm n ω U) (hU : IsOpen U) : IsLocalForm (n + 1) (dLoc ω) U := by
  refine ⟨hω.smoothMBOn_dLoc hU, fun y hy ↦ ?_⟩
  obtain ⟨L, hL⟩ := hω.exists_partial hU hy
  exact ⟨AlternatingMap.alternatizeUncurryFin L, dLoc_eq_alternatizeUncurryFin hL⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem dLoc_apply (ω : E × (Fin n → E) → F) (y : E) (v : Fin (n + 1) → E) :
    LocallyConvex.Manifolds.dLoc ω (y, v) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) • dMB (fun z ↦ ω (z, i.removeNth v)) (y, v i) :=
  rfl

/-! ### `d ∘ d = 0` -/

theorem hasDirDerivAt_dMB_slice (hω : IsLocalForm n ω U) (hU : IsOpen U) {y : E} (hy : y ∈ U)
    (w : Fin n → E) (a u : E) :
    HasDirDerivAt (fun z ↦ dMB (fun z' ↦ ω (z', w)) (z, a)) y u
      (dMB (dMB fun z' ↦ ω (z', w)) ((y, a), (u, 0))) :=
  hasDirDerivAt_slice.mp (((hω.smooth_slice hU w 2).2.2).2.1 (y, a) ⟨hy, mem_univ _⟩ (u, 0))

/-- The derivative of `dω` in the base point, in terms of second derivatives of `ω`. -/
theorem dMB_dLoc (hω : IsLocalForm n ω U) (hU : IsOpen U) {y : E} (hy : y ∈ U)
    (w : Fin (n + 1) → E) (u : E) :
    dMB (fun z ↦ LocallyConvex.Manifolds.dLoc ω (z, w)) (y, u) =
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) •
        dMB (dMB fun z' ↦ ω (z', j.removeNth w)) ((y, w j), (u, 0)) := by
  simp only [dLoc_apply]
  exact (HasDirDerivAt.sum Finset.univ fun j _ ↦
    (hω.hasDirDerivAt_dMB_slice hU hy _ _ u).const_smul _).dMB_eq

/-- `d ∘ d = 0` for local forms (Glöckner–Neeb, Remark 3.6.10): the second derivatives of `ω`
are symmetric. -/
theorem dLoc_dLoc (hω : IsLocalForm n ω U) (hU : IsOpen U) {y : E} (hy : y ∈ U)
    (v : Fin (n + 2) → E) :
    LocallyConvex.Manifolds.dLoc (LocallyConvex.Manifolds.dLoc ω) (y, v) = 0 := by
  rw [dLoc_apply]
  simp only [hω.dMB_dLoc hU hy]
  exact sum_neg_one_pow_smul_sum_eq_zero_of_symm
    (fun a b w ↦ dMB (dMB fun z' ↦ ω (z', w)) ((y, b), (a, 0)))
    (fun a b w ↦ (hω.smooth_slice hU w 2).dMB_dMB_symm hU hy b a) v

end IsLocalForm

/-! ### Pullbacks and naturality -/

section Pullback

variable {E' : Type u} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  {τ : E → E'} {U : Set E} {V : Set E'} {y : E}

/-- The derivative `dτ(y)` of a `C¹` map, as a linear map. -/
noncomputable def dMBLinear (hτ : ContDiffMBOn 1 τ U) (hU : IsOpen U) (hy : y ∈ U) :
    E →ₗ[ℝ] E' where
  toFun u := dMB τ (y, u)
  map_add' u u' := hτ.dMB_add hU hy u u'
  map_smul' c u := hτ.dMB_smul hy c u

/-- The second derivative `d²τ(y)`, as a bilinear map. -/
noncomputable def dMBBilinear (hτ : ContDiffMBOn 2 τ U) (hU : IsOpen U) (hy : y ∈ U) :
    E →ₗ[ℝ] E →ₗ[ℝ] E' :=
  have hd : ContDiffMBOn 1 (dMB τ) (U ×ˢ univ) := hτ.2.2
  have hU2 : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hya : ∀ a, (y, a) ∈ U ×ˢ (univ : Set E) := fun a ↦ ⟨hy, mem_univ a⟩
  have hsymm : ∀ a b, dMB (dMB τ) ((y, a), (b, 0)) = dMB (dMB τ) ((y, b), (a, 0)) :=
    fun a b ↦ hτ.dMB_dMB_symm hU hy a b
  have hadd : ∀ a b b', dMB (dMB τ) ((y, a), (b + b', 0)) =
      dMB (dMB τ) ((y, a), (b, 0)) + dMB (dMB τ) ((y, a), (b', 0)) := fun a b b' ↦ by
    rw [← hd.dMB_add hU2 (hya a)]; simp
  have hsmul : ∀ (c : ℝ) a b, dMB (dMB τ) ((y, a), (c • b, 0)) =
      c • dMB (dMB τ) ((y, a), (b, 0)) := fun c a b ↦ by
    rw [← hd.dMB_smul (hya a)]; simp
  LinearMap.mk₂ ℝ (fun a b ↦ dMB (dMB τ) ((y, a), (b, 0)))
    (fun a a' b ↦ by simp only [hsymm _ b, hadd])
    (fun c a b ↦ by simp only [hsymm _ b, hsmul])
    (fun a b b' ↦ hadd a b b')
    (fun c a b ↦ hsmul c a b)

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem dMBBilinear_symm (hτ : ContDiffMBOn 2 τ U) (hU : IsOpen U) (hy : y ∈ U) (a b : E) :
    dMBBilinear hτ hU hy a b = dMBBilinear hτ hU hy b a :=
  hτ.dMB_dMB_symm hU hy a b

/-- The pullback `τ*ω` of a local form: `(τ*ω)(y)(v₁, …, vₙ) = ω(τ y)(dτ(y) v₁, …, dτ(y) vₙ)`
(Glöckner–Neeb, Definition 3.6.6, in a chart). -/
noncomputable def pullbackLoc (τ : E → E') (ω : E' × (Fin n → E') → F)
    (p : E × (Fin n → E)) : F :=
  ω (τ p.1, fun k ↦ dMB τ (p.1, p.2 k))

variable {ω : E' × (Fin n → E') → F}

theorem smoothMBOn_pullbackLoc (hω : IsLocalForm n ω V) (hU : IsOpen U) (hV : IsOpen V)
    (hτ : SmoothMBOn τ U) (hUV : MapsTo τ U V) :
    SmoothMBOn (pullbackLoc τ ω) (U ×ˢ univ) := by
  intro k
  have hU' : IsOpen (U ×ˢ (univ : Set (Fin n → E))) := hU.prod isOpen_univ
  have h₁ : ContDiffMBOn k (fun p : E × (Fin n → E) ↦ τ p.1) (U ×ˢ univ) := by
    have := (hτ k).comp_clm (ContinuousLinearMap.fst ℝ E (Fin n → E)) hU
    rwa [show (ContinuousLinearMap.fst ℝ E (Fin n → E)) ⁻¹' U = U ×ˢ univ by ext; simp] at this
  have h₂ : ∀ j : Fin n, ContDiffMBOn k (fun p : E × (Fin n → E) ↦ dMB τ (p.1, p.2 j))
      (U ×ˢ univ) := fun j ↦ by
    let Φ : E × (Fin n → E) →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E (Fin n → E)).prod
      ((ContinuousLinearMap.proj j) ∘L ContinuousLinearMap.snd ℝ E (Fin n → E))
    have := ((hτ (k + 1)).2.2).comp_clm Φ (hU.prod isOpen_univ)
    rwa [show Φ ⁻¹' (U ×ˢ univ) = U ×ˢ univ by ext; simp [Φ]] at this
  have hΨ : ContDiffMBOn k (fun p : E × (Fin n → E) ↦ (τ p.1, fun j ↦ dMB τ (p.1, p.2 j)))
      (U ×ˢ univ) := ContDiffMBOn.prodMk hU' h₁ (ContDiffMBOn.pi hU' h₂)
  exact (hω.smooth k).comp hU' (hV.prod isOpen_univ) hΨ fun p hp ↦ ⟨hUV hp.1, mem_univ _⟩

/-- The pullback of a local form by a smooth map is a local form. -/
theorem IsLocalForm.pullback (hω : IsLocalForm n ω V) (hU : IsOpen U) (hV : IsOpen V)
    (hτ : SmoothMBOn τ U) (hUV : MapsTo τ U V) :
    IsLocalForm n (pullbackLoc τ ω) U := by
  refine ⟨smoothMBOn_pullbackLoc hω hU hV hτ hUV, fun y hy ↦ ?_⟩
  obtain ⟨A, hA⟩ := hω.alternating (τ y) (hUV hy)
  exact ⟨A.compLinearMap (dMBLinear (hτ 1) hU hy), fun v ↦ hA _⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [LocallyConvexSpace ℝ E'] [T2Space E'] in
/-- The derivative of `τ*ω` in the base point: a first-order term and a term with `d²τ`. -/
theorem IsLocalForm.dMB_pullbackLoc (hω : IsLocalForm n ω V) (hV : IsOpen V)
    (hτ : SmoothMBOn τ U) (hUV : MapsTo τ U V) (hy : y ∈ U) (w : Fin n → E) (u : E) :
    dMB (fun z ↦ pullbackLoc τ ω (z, w)) (y, u) =
      dMB (fun z ↦ ω (z, fun k ↦ dMB τ (y, w k))) (τ y, dMB τ (y, u)) +
        ∑ k : Fin n, ω (τ y, update (fun j ↦ dMB τ (y, w j)) k
          (dMB (dMB τ) ((y, w k), (u, 0)))) := by
  classical
  set W : Fin n → E' := fun j ↦ dMB τ (y, w j)
  set H : Fin n → E' := fun k ↦ dMB (dMB τ) ((y, w k), (u, 0))
  have hV' : IsOpen (V ×ˢ (univ : Set (Fin n → E'))) := hV.prod isOpen_univ
  have hω1 : ContDiffMBOn 1 ω (V ×ˢ univ) := hω.smooth 1
  -- the inner map `z ↦ (τ z, dτ(z) w)` and its derivative
  have hΨ : HasDirDerivAt (fun z ↦ (τ z, fun j ↦ dMB τ (z, w j))) y u (dMB τ (y, u), H) :=
    ((hτ 1).2.1 y hy u).prodMk (hasDirDerivAt_pi.mpr fun k ↦
      hasDirDerivAt_slice.mp (((hτ 2).2.2).2.1 (y, w k) ⟨hy, mem_univ _⟩ (u, 0)))
  have hchain := (hω1.hasDirDerivAt_comp hV' hΨ ⟨hUV hy, mem_univ _⟩).dMB_eq
  have hsplit : dMB ω ((τ y, W), (dMB τ (y, u), H)) =
      dMB ω ((τ y, W), (dMB τ (y, u), 0)) + dMB ω ((τ y, W), (0, H)) := by
    rw [← hω1.dMB_add hV' ⟨hUV hy, mem_univ _⟩]; simp
  -- the derivative in the vectors, by multilinearity
  have h0 : ContinuousOn ω (V ×ˢ univ) := hω.smooth 0
  have hcont : Continuous fun w' : Fin n → E' ↦ ω (τ y, w') :=
    continuousOn_univ.mp <| h0.comp (Continuous.continuousOn (by fun_prop))
      fun _ _ ↦ ⟨hUV hy, mem_univ _⟩
  have hmult := hasDirDerivAt_of_multilinear hcont
    (fun w' k a b ↦ hω.map_update_add (hUV hy) w' k a b)
    (fun w' k c a ↦ hω.map_update_smul (hUV hy) w' k c a) W H
  change dMB (ω ∘ fun z ↦ (τ z, fun j ↦ dMB τ (z, w j))) (y, u) = _
  rw [hchain, hsplit, dMB_slice, dMB_slice₂, hmult.dMB_eq]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **Naturality of the exterior derivative** (Glöckner–Neeb, Lemma 3.6.13, in charts):
`d(τ*ω) = τ*(dω)`. The terms with the second derivative of `τ` cancel because it is
symmetric. -/
theorem IsLocalForm.dLoc_pullbackLoc (hω : IsLocalForm n ω V) (hU : IsOpen U) (hV : IsOpen V)
    (hτ : SmoothMBOn τ U) (hUV : MapsTo τ U V) (hy : y ∈ U) (v : Fin (n + 1) → E) :
    LocallyConvex.Manifolds.dLoc (pullbackLoc τ ω) (y, v) =
      pullbackLoc τ (LocallyConvex.Manifolds.dLoc ω) (y, v) := by
  obtain ⟨A, hA⟩ := hω.alternating (τ y) (hUV hy)
  have hzero := AlternatingMap.sum_neg_one_pow_smul_sum_update_eq_zero A
    (dMBLinear (hτ 1) hU hy) (dMBBilinear (hτ 2) hU hy) (dMBBilinear_symm (hτ 2) hU hy) v
  rw [IsLocalForm.dLoc_apply]
  simp only [hω.dMB_pullbackLoc hV hτ hUV hy, smul_add, Finset.sum_add_distrib]
  have h2 : ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) • ∑ k : Fin n,
      ω (τ y, update (fun j ↦ dMB τ (y, i.removeNth v j)) k
        (dMB (dMB τ) ((y, i.removeNth v k), (v i, 0)))) = 0 := by
    simp only [neg_one_pow_smul_eq_zsmul, hA]
    exact hzero
  rw [h2, add_zero]
  rfl

end Pullback

end LocallyConvex.Manifolds
