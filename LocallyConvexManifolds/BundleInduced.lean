/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.BundleConnection
import LocallyConvexManifolds.HomBundle

/-!
# Induced connections on pullback and Hom bundles

* **Pullback connections.** Let `f : N → M` be smooth and `∇` a connection on a vector bundle `V`
  over `M`. In the trivialization of `f*V` over `k.source ∩ f⁻¹(Uᵢ)` its symbols are
  `(f*Γ)(y)(a, ξ) = Γᵢ(F y)(dF(y) a, ξ)`, where `F = φᵢ ∘ f ∘ k⁻¹` is the local representative of
  `f` (`BundleConnection.pullback`). The gauge transformation law follows from the one of `Γ` and
  the chain rule.
* **Connections on `Hom(V₁, V₂)`.** For connections on bundles with normed fibers, the symbols
  of the induced connection are `Γ^{Hom}(y)(a, A) = Γ₂(y)(a, A ·) − A Γ₁(y)(a, ·)`, the local
  form of `(∇_a A) ξ = ∇_a (A ξ) − A (∇_a ξ)` (`BundleConnection.hom`). Two points are not
  formal: `y ↦ Γ^{Hom}(y)` must be smooth for the operator norm, which follows from the theorem
  on operator-valued maps of lc-analysis (`contDiffMBOn_of_unc_clm`); and the gauge law involves
  the derivative of the inverse coordinate change, `∂(g⁻¹) = −g⁻¹ (∂g) g⁻¹`, obtained by
  differentiating `g(g⁻¹ ξ) = ξ` (`BundleConnection.hom_transition`).

The induced symbols are only defined on the domains of the local coordinates; off them we set
them to `0`, so that they are bilinear at every point, as `IsLocalSymbol` requires.

No completeness is assumed.
-/

open Set Function Filter
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v w

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {ι : Type w} {𝒰 : TrivializationCover E M ι}

/-! ### Pullback connections -/

section Pullback

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {E' : Type u}
  [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] [MBManifold E' N]

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousSMul ℝ F] in
/-- The symbols are continuous in the fiber variable. -/
theorem IsLocalSymbol.continuous_right {Γ : E → E → F → F} {U : Set E} (hΓ : IsLocalSymbol Γ U)
    {y : E} (hy : y ∈ U) (a : E) : Continuous (Γ y a) :=
  ((hΓ.smooth 0 : ContDiffMBOn 0 _ _) : ContinuousOn _ _).comp_continuous
    (f := fun ξ : F ↦ (y, (a, ξ))) (by fun_prop) fun _ ↦ ⟨hy, mem_univ _⟩

namespace TrivializationCover

variable (𝒰) in
/-- The local representative `φᵢ ∘ f ∘ k⁻¹` of `f` over the set `k.source ∩ f⁻¹(Uᵢ)` of the
pulled back cover. -/
def pullbackRep (f : N → M) (p : atlas E' N × ι) : E' → E :=
  (𝒰.chart p.2).1 ∘ f ∘ p.1.1.symm

theorem smoothMBOn_pullbackRep {f : N → M} (hf : SmoothMBM E' E f) (p : atlas E' N × ι) :
    SmoothMBOn (𝒰.pullbackRep f p) ((𝒰.pullback (E' := E') f hf.continuous).domain p) :=
  fun n ↦ ((hf n).contDiffMBOn_chart isOpen_univ p.1.2 (𝒰.chart p.2).2).mono fun _ hy ↦
    ⟨hy.1, mem_univ _, 𝒰.baseSet_subset p.2 hy.2.2⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [MBManifold E' N] in
theorem mapsTo_pullbackRep {f : N → M} (hf : Continuous f) (p : atlas E' N × ι) :
    MapsTo (𝒰.pullbackRep f p) ((𝒰.pullback (E' := E') f hf).domain p) (𝒰.domain p.2) :=
  fun _ hy ↦ 𝒰.chart_mem_domain hy.2.2

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [MBManifold E' N] in
theorem mapsTo_pullbackRep_transDomain {f : N → M} (hf : Continuous f)
    (p q : atlas E' N × ι) :
    MapsTo (𝒰.pullbackRep f p) ((𝒰.pullback (E' := E') f hf).transDomain p q)
      (𝒰.transDomain p.2 q.2) :=
  fun _ hy ↦ 𝒰.chart_mem_transDomain hy.2.1.2 hy.2.2.2

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [MBManifold E' N] in
theorem symm_pullbackRep {f : N → M} (hf : Continuous f) {p : atlas E' N × ι} {y : E'}
    (hy : y ∈ (𝒰.pullback (E' := E') f hf).domain p) :
    (𝒰.chart p.2).1.symm (𝒰.pullbackRep f p y) = f (p.1.1.symm y) :=
  (𝒰.chart p.2).1.left_inv (𝒰.baseSet_subset p.2 hy.2.2)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [MBManifold E' N] in
/-- The local representatives of `f` intertwine the coordinate changes:
`F_q ∘ τ' = τ ∘ F_p` on the overlap. -/
theorem pullbackRep_trans {f : N → M} (hf : Continuous f) {p q : atlas E' N × ι} {y : E'}
    (hy : y ∈ (𝒰.pullback (E' := E') f hf).transDomain p q) :
    𝒰.pullbackRep f q ((𝒰.pullback (E' := E') f hf).trans p q y) =
      𝒰.trans p.2 q.2 (𝒰.pullbackRep f p y) := by
  change (𝒰.chart q.2).1 (f (q.1.1.symm (q.1.1 (p.1.1.symm y)))) =
    (𝒰.chart q.2).1 ((𝒰.chart p.2).1.symm ((𝒰.chart p.2).1 (f (p.1.1.symm y))))
  have h₁ : p.1.1.symm y ∈ q.1.1.source := hy.2.2.1
  have h₂ : f (p.1.1.symm y) ∈ (𝒰.chart p.2).1.source := 𝒰.baseSet_subset p.2 hy.2.1.2
  rw [q.1.1.left_inv h₁, (𝒰.chart p.2).1.left_inv h₂]

end TrivializationCover

namespace BundleConnection

variable {V : MBVectorBundleCore 𝒰 F} (C : BundleConnection V) {f : N → M}
  (hf : SmoothMBM E' E f)

open scoped Classical in
/-- The symbols of the pullback connection: `Γᵢ(F y)(dF(y) a, ξ)` with `F = φᵢ ∘ f ∘ k⁻¹`, on the
domain of the local coordinates, and `0` off it. -/
def pullbackSymbol (p : atlas E' N × ι) (y a : E') (ξ : F) : F :=
  if y ∈ (𝒰.pullback (E' := E') f hf.continuous).domain p then
    C.Γ p.2 (𝒰.pullbackRep f p y) (dMB (𝒰.pullbackRep f p) (y, a)) ξ
  else 0

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E']
  [T2Space E'] [MBManifold E' N] in
theorem pullbackSymbol_of_mem {p : atlas E' N × ι} {y : E'}
    (hy : y ∈ (𝒰.pullback (E' := E') f hf.continuous).domain p) (a : E') (ξ : F) :
    C.pullbackSymbol hf p y a ξ =
      C.Γ p.2 (𝒰.pullbackRep f p y) (dMB (𝒰.pullbackRep f p) (y, a)) ξ := by
  simp [pullbackSymbol, hy]

theorem isLocalSymbol_pullbackSymbol (p : atlas E' N × ι) :
    IsLocalSymbol (C.pullbackSymbol hf p)
      ((𝒰.pullback (E' := E') f hf.continuous).domain p) := by
  set D := (𝒰.pullback (E' := E') f hf.continuous).domain p
  have hD : IsOpen D := TrivializationCover.isOpen_domain _ p
  have hF := 𝒰.smoothMBOn_pullbackRep hf p
  have hΓ := C.isLocalSymbol p.2
  refine ⟨fun n ↦ ?_, fun y a a' ξ ↦ ?_, fun y c a ξ ↦ ?_, fun y a ξ ξ' ↦ ?_,
    fun y c a ξ ↦ ?_⟩
  · have hDU : IsOpen (D ×ˢ (univ : Set (E' × F))) := hD.prod isOpen_univ
    have hfst := (ContinuousLinearMap.fst ℝ E' (E' × F)).contDiffMBOn n (D ×ˢ univ)
    have h₀ : ContDiffMBOn n (fun r : E' × (E' × F) ↦ 𝒰.pullbackRep f p r.1) (D ×ˢ univ) :=
      ContDiffMBOn.comp (g := 𝒰.pullbackRep f p) (f := ContinuousLinearMap.fst ℝ E' (E' × F))
        hDU hD (hF n) hfst fun r hr ↦ hr.1
    have hpair : ContDiffMBOn n (fun r : E' × (E' × F) ↦ (r.1, r.2.1)) (D ×ˢ univ) :=
      ((ContinuousLinearMap.fst ℝ E' (E' × F)).prod ((ContinuousLinearMap.fst ℝ E' F).comp
        (ContinuousLinearMap.snd ℝ E' (E' × F)))).contDiffMBOn n _
    have h₁ : ContDiffMBOn n (fun r : E' × (E' × F) ↦ dMB (𝒰.pullbackRep f p) (r.1, r.2.1))
        (D ×ˢ univ) :=
      ContDiffMBOn.comp (g := dMB (𝒰.pullbackRep f p)) hDU (hD.prod isOpen_univ) (hF (n + 1)).2.2
        hpair
        fun r hr ↦ ⟨hr.1, mem_univ _⟩
    have h₂ : ContDiffMBOn n (fun r : E' × (E' × F) ↦ r.2.2) (D ×ˢ univ) :=
      ((ContinuousLinearMap.snd ℝ E' F).comp
        (ContinuousLinearMap.snd ℝ E' (E' × F))).contDiffMBOn n _
    refine ContDiffMBOn.congr_of_isOpen hDU (fun r hr ↦ ?_)
      (hΓ.contDiffMBOn_comp hDU h₀ h₁ h₂ (𝒰.isOpen_domain p.2)
        fun r hr ↦ 𝒰.mapsTo_pullbackRep hf.continuous p hr.1)
    exact (C.pullbackSymbol_of_mem hf hr.1 _ _).symm
  · by_cases hy : y ∈ D
    · simp only [C.pullbackSymbol_of_mem hf hy, (hF 1).dMB_add hD hy, hΓ.add_left]
    · simp [pullbackSymbol, D, hy]
  · by_cases hy : y ∈ D
    · simp only [C.pullbackSymbol_of_mem hf hy, (hF 1).dMB_smul hy, hΓ.smul_left]
    · simp [pullbackSymbol, D, hy]
  · by_cases hy : y ∈ D
    · simp only [C.pullbackSymbol_of_mem hf hy, hΓ.add_right]
    · simp [pullbackSymbol, D, hy]
  · by_cases hy : y ∈ D
    · simp only [C.pullbackSymbol_of_mem hf hy, hΓ.smul_right]
    · simp [pullbackSymbol, D, hy]

/-- **The pullback connection** `f*∇` on `f*V`, with symbols `Γᵢ(F y)(dF(y) a, ξ)` in the
trivialization over `k.source ∩ f⁻¹(Uᵢ)`, where `F = φᵢ ∘ f ∘ k⁻¹`. -/
def pullback : BundleConnection (V.pullback f hf) where
  Γ := C.pullbackSymbol hf
  isLocalSymbol := C.isLocalSymbol_pullbackSymbol hf
  transition p q y hy a ξ := by
    set 𝒰' := 𝒰.pullback (E' := E') f hf.continuous
    set Fp := 𝒰.pullbackRep f p
    set Fq := 𝒰.pullbackRep f q
    have hT : IsOpen (𝒰'.transDomain p q) := 𝒰'.isOpen_transDomain p q
    have hyp : y ∈ 𝒰'.domain p := 𝒰'.transDomain_subset_domain p q hy
    have hyq : 𝒰'.trans p q y ∈ 𝒰'.domain q :=
      𝒰'.transDomain_subset_domain q p (𝒰'.mapsTo_trans p q hy)
    have hFp := 𝒰.smoothMBOn_pullbackRep hf p
    have hFq := 𝒰.smoothMBOn_pullbackRep hf q
    have hFpT : ContDiffMBOn 1 Fp (𝒰'.transDomain p q) :=
      (hFp 1).mono (𝒰'.transDomain_subset_domain p q)
    have hmapsT := 𝒰.mapsTo_pullbackRep_transDomain hf.continuous p q
    have hw : Fp y ∈ 𝒰.transDomain p.2 q.2 := hmapsT hy
    -- the coordinates of the base point
    have hsym : f (p.1.1.symm y) = (𝒰.chart p.2).1.symm (Fp y) :=
      (𝒰.symm_pullbackRep hf.continuous hyp).symm
    -- the derivative of the local representatives along the coordinate change
    have hd : dMB Fq (𝒰'.trans p q y, dMB (𝒰'.trans p q) (y, a)) =
        dMB (𝒰.trans p.2 q.2) (Fp y, dMB Fp (y, a)) := by
      have hev : Fq ∘ 𝒰'.trans p q =ᶠ[𝓝 y] 𝒰.trans p.2 q.2 ∘ Fp :=
        eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦
          𝒰.pullbackRep_trans hf.continuous hz
      rw [← ContDiffMBOn.dMB_comp (𝒰'.isOpen_domain q) (hFq 1) (𝒰'.smoothMBOn_trans p q 1)
          (fun z hz ↦ 𝒰'.transDomain_subset_domain q p (𝒰'.mapsTo_trans p q hz)) hy a,
        dMB_congr_of_eventuallyEq hev,
        ContDiffMBOn.dMB_comp (𝒰.isOpen_transDomain p.2 q.2) (𝒰.smoothMBOn_trans p.2 q.2 1)
          hFpT hmapsT hy a]
    -- the derivative of the coordinate change of `f*V`
    have hG : ContDiffMBOn 1 (fun z ↦ V.coordChange p.2 q.2 ((𝒰.chart p.2).1.symm z) ξ)
        (𝒰.transDomain p.2 q.2) :=
      ContDiffMBOn.comp (g := fun r : E × F ↦ V.coordChange p.2 q.2 ((𝒰.chart p.2).1.symm r.1) r.2)
        (f := fun z ↦ (z, ξ)) (𝒰.isOpen_transDomain p.2 q.2)
        ((𝒰.isOpen_transDomain p.2 q.2).prod isOpen_univ) (V.smooth p.2 q.2 1)
        (((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 _).prodMk (𝒰.isOpen_transDomain p.2 q.2)
          (contDiffMBOn_const 1 ξ _)) fun z hz ↦ ⟨hz, mem_univ _⟩
    have hdg : dMB (fun z ↦ V.coordChange p.2 q.2 (f (p.1.1.symm z)) ξ) (y, a) =
        dMB (fun z ↦ V.coordChange p.2 q.2 ((𝒰.chart p.2).1.symm z) ξ) (Fp y, dMB Fp (y, a)) := by
      have hev : (fun z ↦ V.coordChange p.2 q.2 (f (p.1.1.symm z)) ξ) =ᶠ[𝓝 y]
          (fun z ↦ V.coordChange p.2 q.2 ((𝒰.chart p.2).1.symm z) ξ) ∘ Fp :=
        eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦ by
          change _ = V.coordChange p.2 q.2 ((𝒰.chart p.2).1.symm (Fp z)) ξ
          rw [𝒰.symm_pullbackRep hf.continuous (𝒰'.transDomain_subset_domain p q hz)]
      rw [dMB_congr_of_eventuallyEq hev,
        ContDiffMBOn.dMB_comp (𝒰.isOpen_transDomain p.2 q.2) hG hFpT hmapsT hy a]
    have hTr := C.transition p.2 q.2 (Fp y) hw (dMB Fp (y, a)) ξ
    change C.pullbackSymbol hf q (𝒰'.trans p q y) (dMB (𝒰'.trans p q) (y, a))
        (V.coordChange p.2 q.2 (f (p.1.1.symm y)) ξ) =
      V.coordChange p.2 q.2 (f (p.1.1.symm y)) (C.pullbackSymbol hf p y a ξ) +
        dMB (fun z ↦ V.coordChange p.2 q.2 (f (p.1.1.symm z)) ξ) (y, a)
    rw [C.pullbackSymbol_of_mem hf hyq, C.pullbackSymbol_of_mem hf hyp, hdg, hd,
      𝒰.pullbackRep_trans hf.continuous hy, hsym]
    exact hTr

end BundleConnection

end Pullback

/-! ### Connections on Hom bundles -/

section Hom

variable {F₁ F₂ : Type u} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- Evaluation of operators, as a bilinear map. -/
private def evalBilin (G₁ G₂ : Type u) [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] : (G₁ →L[ℝ] G₂) →ₗ[ℝ] G₁ →ₗ[ℝ] G₂ :=
  LinearMap.mk₂ ℝ (fun A ξ ↦ A ξ) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun A ξ η ↦ A.map_add ξ η) (fun c A ξ ↦ A.map_smul c ξ)

private theorem evalBilin_apply (G₁ G₂ : Type u) [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] (A : G₁ →L[ℝ] G₂) (ξ : G₁) :
    evalBilin G₁ G₂ A ξ = A ξ :=
  rfl

private theorem continuous_evalBilin (G₁ G₂ : Type u) [NormedAddCommGroup G₁]
    [NormedSpace ℝ G₁] [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] :
    Continuous fun p : (G₁ →L[ℝ] G₂) × G₁ ↦ evalBilin G₁ G₂ p.1 p.2 :=
  continuous_fst.clm_apply continuous_snd

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
/-- Directional derivatives commute with continuous linear maps. -/
private theorem hasDirDerivAt_clm_comp {G H : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {g : E → G} {y a : E} {D : G}
    (h : HasDirDerivAt g y a D) (L : G →L[ℝ] H) : HasDirDerivAt (fun z ↦ L (g z)) y a (L D) :=
  ((L.continuous.tendsto D).comp h).congr fun t ↦ by
    simp only [Function.comp_apply, map_sub, map_smul]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
/-- The derivative of an operator-valued map, evaluated at a vector. -/
private theorem hasDirDerivAt_clm_apply {Φ : E → F₁ →L[ℝ] F₂} {y a : E} {D : F₁ →L[ℝ] F₂}
    (h : HasDirDerivAt Φ y a D) (ξ : F₁) : HasDirDerivAt (fun z ↦ Φ z ξ) y a (D ξ) :=
  hasDirDerivAt_clm_comp h (ContinuousLinearMap.apply ℝ F₂ ξ)

private theorem contDiffMBOn_sub' {X G : Type u} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
    [T2Space X] [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ} {f g : X → G} {U : Set X}
    (hU : IsOpen U) (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) :
    ContDiffMBOn k (fun x ↦ f x - g x) U :=
  ContDiffMBOn.congr_of_isOpen hU (fun _ _ ↦ by simp)
    (ContDiffMBOn.comp (F₁ := G × G) hU isOpen_univ
      ((ContinuousLinearMap.fst ℝ G G - ContinuousLinearMap.snd ℝ G G).contDiffMBOn k univ)
      (hf.prodMk hU hg) (mapsTo_univ _ _))

namespace BundleConnection

variable {V₁ : MBVectorBundleCore 𝒰 F₁} {V₂ : MBVectorBundleCore 𝒰 F₂}
  (C₁ : BundleConnection V₁) (C₂ : BundleConnection V₂)

/-- The symbols of the connection on `Hom(V₁, V₂)` at a point of the domain:
`ξ ↦ Γ₂(y)(a, A ξ) − A Γ₁(y)(a, ξ)`. -/
def homSymbolCLM (i : ι) {y : E} (hy : y ∈ 𝒰.domain i) (a : E) (A : F₁ →L[ℝ] F₂) :
    F₁ →L[ℝ] F₂ where
  toFun ξ := C₂.Γ i y a (A ξ) - A (C₁.Γ i y a ξ)
  map_add' ξ η := by
    simp only [map_add, (C₂.isLocalSymbol i).add_right, (C₁.isLocalSymbol i).add_right]
    abel
  map_smul' c ξ := by
    simp only [map_smul, (C₂.isLocalSymbol i).smul_right, (C₁.isLocalSymbol i).smul_right,
      RingHom.id_apply, smul_sub]
  cont := (((C₂.isLocalSymbol i).continuous_right hy a).comp A.continuous).sub
    (A.continuous.comp ((C₁.isLocalSymbol i).continuous_right hy a))

open scoped Classical in
/-- The symbols of the connection on `Hom(V₁, V₂)`: `Γ^{Hom}(y)(a, A) = Γ₂(y)(a, A ·) −
A Γ₁(y)(a, ·)` on the domain of the local coordinates, and `0` off it. -/
def homSymbol (i : ι) (y a : E) (A : F₁ →L[ℝ] F₂) : F₁ →L[ℝ] F₂ :=
  if hy : y ∈ 𝒰.domain i then C₁.homSymbolCLM C₂ i hy a A else 0

omit [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem homSymbol_apply (i : ι) {y : E} (hy : y ∈ 𝒰.domain i) (a : E) (A : F₁ →L[ℝ] F₂)
    (ξ : F₁) : C₁.homSymbol C₂ i y a A ξ = C₂.Γ i y a (A ξ) - A (C₁.Γ i y a ξ) := by
  simp only [homSymbol, hy, dite_true]
  rfl

omit [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem homSymbol_of_not_mem (i : ι) {y : E} (hy : y ∉ 𝒰.domain i) (a : E)
    (A : F₁ →L[ℝ] F₂) : C₁.homSymbol C₂ i y a A = 0 := by
  simp only [homSymbol, hy, dite_false]

omit [MBManifold E M] in
theorem isLocalSymbol_homSymbol (i : ι) : IsLocalSymbol (C₁.homSymbol C₂ i) (𝒰.domain i) := by
  set D := 𝒰.domain i
  have hD : IsOpen D := 𝒰.isOpen_domain i
  have hΓ₁ := C₁.isLocalSymbol i
  have hΓ₂ := C₂.isLocalSymbol i
  refine ⟨fun n ↦ ?_, fun y a a' A ↦ ?_, fun y c a A ↦ ?_, fun y a A B ↦ ?_, fun y c a A ↦ ?_⟩
  · have hDU : IsOpen (D ×ˢ (univ : Set (E × (F₁ →L[ℝ] F₂)))) := hD.prod isOpen_univ
    refine contDiffMBOn_of_unc_clm n hDU ?_
    have hW : IsOpen ((D ×ˢ (univ : Set (E × (F₁ →L[ℝ] F₂)))) ×ˢ (univ : Set F₁)) :=
      hDU.prod isOpen_univ
    refine ContDiffMBOn.congr_of_isOpen
      (f₁ := fun r : (E × (E × (F₁ →L[ℝ] F₂))) × F₁ ↦
        C₂.Γ i r.1.1 r.1.2.1 (r.1.2.2 r.2) - r.1.2.2 (C₁.Γ i r.1.1 r.1.2.1 r.2))
      hW (fun r hr ↦ (C₁.homSymbol_apply C₂ i hr.1.1 _ _ _).symm) ?_
    have hy : ContDiffMBOn (n + 1) (fun r : (E × (E × (F₁ →L[ℝ] F₂))) × F₁ ↦ r.1.1)
        ((D ×ˢ univ) ×ˢ univ) :=
      ((ContinuousLinearMap.fst ℝ E (E × (F₁ →L[ℝ] F₂))).comp
        (ContinuousLinearMap.fst ℝ _ F₁)).contDiffMBOn _ _
    have ha : ContDiffMBOn (n + 1) (fun r : (E × (E × (F₁ →L[ℝ] F₂))) × F₁ ↦ r.1.2.1)
        ((D ×ˢ univ) ×ˢ univ) :=
      ((ContinuousLinearMap.fst ℝ E (F₁ →L[ℝ] F₂)).comp
        ((ContinuousLinearMap.snd ℝ E (E × (F₁ →L[ℝ] F₂))).comp
          (ContinuousLinearMap.fst ℝ _ F₁))).contDiffMBOn _ _
    have hA : ContDiffMBOn (n + 1) (fun r : (E × (E × (F₁ →L[ℝ] F₂))) × F₁ ↦ r.1.2.2)
        ((D ×ˢ univ) ×ˢ univ) :=
      ((ContinuousLinearMap.snd ℝ E (F₁ →L[ℝ] F₂)).comp
        ((ContinuousLinearMap.snd ℝ E (E × (F₁ →L[ℝ] F₂))).comp
          (ContinuousLinearMap.fst ℝ _ F₁))).contDiffMBOn _ _
    have hξ : ContDiffMBOn (n + 1) (fun r : (E × (E × (F₁ →L[ℝ] F₂))) × F₁ ↦ r.2)
        ((D ×ˢ univ) ×ˢ univ) :=
      (ContinuousLinearMap.snd ℝ (E × (E × (F₁ →L[ℝ] F₂))) F₁).contDiffMBOn _ _
    have hmaps : MapsTo (fun r : (E × (E × (F₁ →L[ℝ] F₂))) × F₁ ↦ r.1.1)
        ((D ×ˢ univ) ×ˢ univ) D := fun r hr ↦ hr.1.1
    have hAξ := ContDiffMBOn.bilin (evalBilin F₁ F₂) (continuous_evalBilin F₁ F₂) hW hA hξ
    have h₂ := hΓ₂.contDiffMBOn_comp hW hy ha hAξ hD hmaps
    have h₁ := ContDiffMBOn.bilin (evalBilin F₁ F₂) (continuous_evalBilin F₁ F₂) hW hA
      (hΓ₁.contDiffMBOn_comp hW hy ha hξ hD hmaps)
    exact contDiffMBOn_sub' hW h₂ h₁
  · by_cases hy : y ∈ D
    · ext ξ
      simp only [FunLike.coe_add, Pi.add_apply, C₁.homSymbol_apply C₂ i hy, hΓ₁.add_left,
        hΓ₂.add_left, map_add]
      abel
    · simp [C₁.homSymbol_of_not_mem C₂ i hy]
  · by_cases hy : y ∈ D
    · ext ξ
      simp only [FunLike.coe_smul, Pi.smul_apply, C₁.homSymbol_apply C₂ i hy, hΓ₁.smul_left,
        hΓ₂.smul_left, map_smul, smul_sub]
    · simp [C₁.homSymbol_of_not_mem C₂ i hy]
  · by_cases hy : y ∈ D
    · ext ξ
      simp only [FunLike.coe_add, Pi.add_apply, C₁.homSymbol_apply C₂ i hy, hΓ₂.add_right]
      abel
    · simp [C₁.homSymbol_of_not_mem C₂ i hy]
  · by_cases hy : y ∈ D
    · ext ξ
      simp only [FunLike.coe_smul, Pi.smul_apply, C₁.homSymbol_apply C₂ i hy, hΓ₂.smul_right,
        smul_sub]
    · simp [C₁.homSymbol_of_not_mem C₂ i hy]

/-- **The gauge transformation law of the Hom connection.** With `g₁`, `g₂` the coordinate
changes of `V₁`, `V₂`, the derivative of `g₂ A g₁⁻¹` brings in the derivative of the inverse,
`∂(g₁⁻¹) = −g₁⁻¹ (∂g₁) g₁⁻¹`, obtained by differentiating `g₁(g₁⁻¹ ξ) = ξ`. -/
theorem hom_transition (i j : ι) (y : E) (hy : y ∈ 𝒰.transDomain i j) (a : E)
    (A : F₁ →L[ℝ] F₂) :
    C₁.homSymbol C₂ j (𝒰.trans i j y) (dMB (𝒰.trans i j) (y, a))
        ((homCore V₁ V₂).coordChange i j ((𝒰.chart i).1.symm y) A) =
      (homCore V₁ V₂).coordChange i j ((𝒰.chart i).1.symm y) (C₁.homSymbol C₂ i y a A) +
        dMB (fun z ↦ (homCore V₁ V₂).coordChange i j ((𝒰.chart i).1.symm z) A) (y, a) := by
  have hT : IsOpen (𝒰.transDomain i j) := 𝒰.isOpen_transDomain i j
  have hx : (𝒰.chart i).1.symm y ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j := hy.2
  have hxji : (𝒰.chart i).1.symm y ∈ 𝒰.baseSet j ∩ 𝒰.baseSet i := ⟨hx.2, hx.1⟩
  have hyi : y ∈ 𝒰.domain i := 𝒰.transDomain_subset_domain i j hy
  have hyj : 𝒰.trans i j y ∈ 𝒰.domain j :=
    𝒰.transDomain_subset_domain j i (𝒰.mapsTo_trans i j hy)
  -- the inverse coordinate changes of `V₁` are `C¹` in the base point
  have hH₁ : ∀ ξ : F₁, ContDiffMBOn 1
      (fun z ↦ V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ) (𝒰.transDomain i j) := fun ξ ↦
    ContDiffMBOn.congr_of_isOpen hT (fun z hz ↦ by
        rw [evalBilin_apply, V₁.coordCLM_apply j i ⟨hz.2.2, hz.2.1⟩ ξ])
      (ContDiffMBOn.bilin (evalBilin F₁ F₁) (continuous_evalBilin F₁ F₁) hT
        (V₁.smoothMBOn_coordCLM_symm i j 1) (contDiffMBOn_const 1 ξ _))
  -- `∂(g₁⁻¹ ξ) = −g₁⁻¹ (∂g₁)(g₁⁻¹ ξ)`
  have hdH₁ : ∀ ξ : F₁, dMB (fun z ↦ V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ) (y, a) =
      -V₁.coordChange j i ((𝒰.chart i).1.symm y)
        (dMB (fun z ↦ V₁.coordChange i j ((𝒰.chart i).1.symm z)
          (V₁.coordChange j i ((𝒰.chart i).1.symm y) ξ)) (y, a)) := by
    intro ξ
    have hconst : (fun z ↦ V₁.coordChange i j ((𝒰.chart i).1.symm z)
        (V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ)) =ᶠ[𝓝 y] fun _ ↦ ξ :=
      eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦
        (V₁.coordChange_comp j i j _ ⟨⟨hz.2.2, hz.2.1⟩, hz.2.2⟩ ξ).trans
          (V₁.coordChange_self j _ hz.2.2 ξ)
    have hc0 : HasDirDerivAt (fun _ : E ↦ ξ) y a 0 :=
      tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp)
    have h0 := dMB_fiber_comp hT hT subset_rfl (V₁.smooth i j 1)
      (fun z hz ↦ V₁.map_add i j _ hz.2) (fun z hz ↦ V₁.map_smul i j _ hz.2) (hH₁ ξ) hy a
    rw [dMB_congr_of_eventuallyEq hconst, hc0.dMB_eq] at h0
    have h1 := congrArg (V₁.coordChange j i ((𝒰.chart i).1.symm y)) h0
    have hz0 : V₁.coordChange j i ((𝒰.chart i).1.symm y) 0 = 0 :=
      map_zero (V₁.coordChangeLinear j i hxji)
    rw [V₁.map_add j i _ hxji, V₁.coordChange_comp i j i _ ⟨hx, hx.1⟩,
      V₁.coordChange_self i _ hx.1, hz0] at h1
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h1.symm
  ext ξ'
  -- the derivative of the coordinate change of `Hom(V₁, V₂)`, evaluated at `ξ'`
  have hΦ : ContDiffMBOn 1 (fun z ↦ (homCore V₁ V₂).coordChange i j ((𝒰.chart i).1.symm z) A)
      (𝒰.transDomain i j) :=
    ContDiffMBOn.comp (g := fun r : E × (F₁ →L[ℝ] F₂) ↦
        (homCore V₁ V₂).coordChange i j ((𝒰.chart i).1.symm r.1) r.2)
      (f := fun z ↦ (z, A)) hT (hT.prod isOpen_univ) ((homCore V₁ V₂).smooth i j 1)
      (((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 _).prodMk hT (contDiffMBOn_const 1 A _))
      fun z hz ↦ ⟨hz, mem_univ _⟩
  have hs : ContDiffMBOn 1
      (fun z ↦ A (V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ')) (𝒰.transDomain i j) :=
    ContDiffMBOn.comp (g := A) hT isOpen_univ (A.contDiffMBOn 1 univ) (hH₁ ξ')
      (mapsTo_univ _ _)
  have hdΦ : dMB (fun z ↦ (homCore V₁ V₂).coordChange i j ((𝒰.chart i).1.symm z) A) (y, a) ξ' =
      dMB (fun z ↦ V₂.coordChange i j ((𝒰.chart i).1.symm z)
        (A (V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ'))) (y, a) := by
    rw [← (hasDirDerivAt_clm_apply (hΦ.hasDirDerivAt hy a) ξ').dMB_eq]
    exact dMB_congr_of_eventuallyEq (eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦
      homCore_coordChange_apply V₁ V₂ i j hz.2 A ξ') a
  have hprod := dMB_fiber_comp hT hT subset_rfl (V₂.smooth i j 1)
    (fun z hz ↦ V₂.map_add i j _ hz.2) (fun z hz ↦ V₂.map_smul i j _ hz.2) hs hy a
  have hdA : dMB (fun z ↦ A (V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ')) (y, a) =
      A (dMB (fun z ↦ V₁.coordChange j i ((𝒰.chart i).1.symm z) ξ') (y, a)) :=
    (hasDirDerivAt_clm_comp ((hH₁ ξ').hasDirDerivAt hy a) A).dMB_eq
  -- the gauge laws of `Γ₁` and `Γ₂`
  have hGH : V₁.coordChange i j ((𝒰.chart i).1.symm y)
      (V₁.coordChange j i ((𝒰.chart i).1.symm y) ξ') = ξ' :=
    (V₁.coordChange_comp j i j _ ⟨hxji, hx.2⟩ ξ').trans (V₁.coordChange_self j _ hx.2 ξ')
  have hT₁ := C₁.transition i j y hy a (V₁.coordChange j i ((𝒰.chart i).1.symm y) ξ')
  rw [hGH] at hT₁
  have hT₂ := C₂.transition i j y hy a (A (V₁.coordChange j i ((𝒰.chart i).1.symm y) ξ'))
  have hHG : ∀ u, V₁.coordChange j i ((𝒰.chart i).1.symm y)
      (V₁.coordChange i j ((𝒰.chart i).1.symm y) u) = u := fun u ↦
    (V₁.coordChange_comp i j i _ ⟨hx, hx.1⟩ u).trans (V₁.coordChange_self i _ hx.1 u)
  have hG₂sub : ∀ u v, V₂.coordChange i j ((𝒰.chart i).1.symm y) (u - v) =
      V₂.coordChange i j ((𝒰.chart i).1.symm y) u -
        V₂.coordChange i j ((𝒰.chart i).1.symm y) v :=
    fun u v ↦ map_sub (V₂.coordChangeLinear i j hx) u v
  have hG₂neg : ∀ u, V₂.coordChange i j ((𝒰.chart i).1.symm y) (-u) =
      -V₂.coordChange i j ((𝒰.chart i).1.symm y) u :=
    fun u ↦ map_neg (V₂.coordChangeLinear i j hx) u
  rw [FunLike.coe_add, Pi.add_apply, C₁.homSymbol_apply C₂ j hyj,
    homCore_coordChange_apply V₁ V₂ i j hx, homCore_coordChange_apply V₁ V₂ i j hx,
    homCore_coordChange_apply V₁ V₂ i j hx, C₁.homSymbol_apply C₂ i hyi, hdΦ, hprod, hdA,
    hdH₁, hT₁, hT₂, V₁.map_add j i _ hxji, hHG, map_add, map_neg, hG₂sub, hG₂neg,
    V₂.map_add i j _ hx]
  abel

/-- **The connection on `Hom(V₁, V₂)`** induced by connections on `V₁` and `V₂` (normed fibers).
Its symbols are `Γ^{Hom}(y)(a, A) ξ = Γ₂(y)(a, A ξ) − A Γ₁(y)(a, ξ)` (`homSymbol_apply`), the
local form of `(∇_a A) ξ = ∇_a (A ξ) − A (∇_a ξ)`. -/
def hom : BundleConnection (homCore V₁ V₂) where
  Γ := C₁.homSymbol C₂
  isLocalSymbol := C₁.isLocalSymbol_homSymbol C₂
  transition := C₁.hom_transition C₂

end BundleConnection

end Hom

/-! ### The trivial connection and the dual connection -/

section Trivial

variable (𝒰) in
/-- The **trivial connection** `∇_a ξ = dξ(a)` on the trivial bundle `M × F`: all its symbols
vanish. -/
def BundleConnection.trivial (F : Type u) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] :
    BundleConnection (trivialCore 𝒰 F) where
  Γ _ _ _ _ := 0
  isLocalSymbol _ := ⟨fun k ↦ contDiffMBOn_const k 0 _, fun _ _ _ _ ↦ (add_zero 0).symm,
    fun _ c _ _ ↦ (smul_zero c).symm, fun _ _ _ _ ↦ (add_zero 0).symm,
    fun _ c _ _ ↦ (smul_zero c).symm⟩
  transition i j y hy a ξ := by
    have hc0 : HasDirDerivAt (fun _ : E ↦ ξ) y a 0 :=
      tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp)
    change (0 : F) = 0 + dMB (fun _ : E ↦ ξ) (y, a)
    rw [hc0.dMB_eq, add_zero]

end Trivial

section Dual

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {𝒰 : TrivializationCover E M ι} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : MBVectorBundleCore 𝒰 F}

/-- **The dual connection** on `V' = Hom(V, ℝ)`: the connection on `Hom(V, M × ℝ)` induced by a
connection on `V` and the trivial connection, `(∇_a α) ξ = d(α ξ)(a) − α(∇_a ξ)`. -/
def BundleConnection.dual (C : BundleConnection V) : BundleConnection (dualCore V) :=
  C.hom (BundleConnection.trivial 𝒰 ℝ)

/-- The symbols of the dual connection: `Γ'(y)(a, α) ξ = −α(Γ(y)(a, ξ))`. -/
theorem BundleConnection.dual_Γ_apply (C : BundleConnection V) (i : ι) {y : E}
    (hy : y ∈ 𝒰.domain i) (a : E) (α : F →L[ℝ] ℝ) (ξ : F) :
    C.dual.Γ i y a α ξ = -α (C.Γ i y a ξ) := by
  change C.homSymbol (BundleConnection.trivial 𝒰 ℝ) i y a α ξ = _
  rw [C.homSymbol_apply _ i hy]
  exact zero_sub _

end Dual

end LocallyConvex.Manifolds
