/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.BundleInduced

/-!
# Refinements of trivializing covers

A trivializing cover `𝒲` **refines** `𝒱` if every set of `𝒲` is contained in a set of `𝒱`, along
a chosen map of indices `r` (`TrivializationCover.Refines`). A vector bundle trivialized over `𝒱`
is then trivialized over `𝒲`, with coordinate changes `g_{r(w) r(w')}`
(`MBVectorBundleCore.refine`), and a connection on it gives a connection on the refined bundle,
with symbols `Γ_{r(w)}(F y)(dF(y) a, ξ)`, where `F = φ_{r(w)} ∘ φ_w⁻¹` is the change of charts
(`BundleConnection.refine`).

Any two covers have a **common refinement**, the cover by the intersections `Uᵢ ∩ Vₖ`
(`TrivializationCover.inf`). In particular, the Hom bundle of two bundles trivialized over
different covers is defined over their common refinement (`homCoreInf`), and so is the induced
connection (`BundleConnection.homInf`).

No completeness is assumed.
-/

open Set Function Filter
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v w w'

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {κ : Type w} {κ' : Type w'}

namespace TrivializationCover

/-- `𝒲` **refines** `𝒱`: each set `W_w` is contained in the set `V_{r(w)}`. -/
structure Refines (𝒲 : TrivializationCover E M κ') (𝒱 : TrivializationCover E M κ) where
  /-- The map of indices. -/
  map : κ' → κ
  subset : ∀ w, 𝒲.baseSet w ⊆ 𝒱.baseSet (map w)

variable {𝒲 : TrivializationCover E M κ'} {𝒱 : TrivializationCover E M κ}

/-- The change of charts `φ_{r(w)} ∘ φ_w⁻¹` from the coordinates of `𝒲` to those of `𝒱`. -/
def refineRep (r : 𝒲.Refines 𝒱) (w : κ') : E → E :=
  (𝒱.chart (r.map w)).1 ∘ (𝒲.chart w).1.symm

theorem smoothMBOn_refineRep (r : 𝒲.Refines 𝒱) (w : κ') :
    SmoothMBOn (refineRep r w) (𝒲.domain w) := fun n ↦
  (smoothMBOn_transition' (𝒲.chart w) (𝒱.chart (r.map w)) n).mono fun _ hy ↦
    ⟨hy.1, 𝒱.baseSet_subset _ (r.subset w hy.2)⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
theorem mapsTo_refineRep (r : 𝒲.Refines 𝒱) (w : κ') :
    MapsTo (refineRep r w) (𝒲.domain w) (𝒱.domain (r.map w)) :=
  fun _ hy ↦ 𝒱.chart_mem_domain (r.subset w hy.2)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
theorem mapsTo_refineRep_transDomain (r : 𝒲.Refines 𝒱) (w w₂ : κ') :
    MapsTo (refineRep r w) (𝒲.transDomain w w₂) (𝒱.transDomain (r.map w) (r.map w₂)) :=
  fun _ hy ↦ 𝒱.chart_mem_transDomain (r.subset w hy.2.1) (r.subset w₂ hy.2.2)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
theorem symm_refineRep (r : 𝒲.Refines 𝒱) {w : κ'} {y : E} (hy : y ∈ 𝒲.domain w) :
    (𝒱.chart (r.map w)).1.symm (refineRep r w y) = (𝒲.chart w).1.symm y :=
  (𝒱.chart (r.map w)).1.left_inv (𝒱.baseSet_subset _ (r.subset w hy.2))

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
/-- The changes of charts intertwine the coordinate changes of `𝒲` and `𝒱`. -/
theorem refineRep_trans (r : 𝒲.Refines 𝒱) {w w₂ : κ'} {y : E} (hy : y ∈ 𝒲.transDomain w w₂) :
    refineRep r w₂ (𝒲.trans w w₂ y) = 𝒱.trans (r.map w) (r.map w₂) (refineRep r w y) := by
  change (𝒱.chart (r.map w₂)).1 ((𝒲.chart w₂).1.symm ((𝒲.chart w₂).1 ((𝒲.chart w).1.symm y))) =
    (𝒱.chart (r.map w₂)).1 ((𝒱.chart (r.map w)).1.symm
      ((𝒱.chart (r.map w)).1 ((𝒲.chart w).1.symm y)))
  rw [(𝒲.chart w₂).1.left_inv (𝒲.baseSet_subset w₂ hy.2.2),
    (𝒱.chart (r.map w)).1.left_inv (𝒱.baseSet_subset _ (r.subset w hy.2.1))]

variable {ι : Type*}

/-- The **common refinement** of two covers: the sets `Uᵢ ∩ Vₖ`, with the charts of `𝒰`. -/
def inf (𝒰 : TrivializationCover E M ι) (𝒱 : TrivializationCover E M κ) :
    TrivializationCover E M (ι × κ) where
  chart p := 𝒰.chart p.1
  baseSet p := 𝒰.baseSet p.1 ∩ 𝒱.baseSet p.2
  isOpen_baseSet p := (𝒰.isOpen_baseSet p.1).inter (𝒱.isOpen_baseSet p.2)
  baseSet_subset p := inter_subset_left.trans (𝒰.baseSet_subset p.1)
  indexAt x := (𝒰.indexAt x, 𝒱.indexAt x)
  mem_baseSet_at x := ⟨𝒰.mem_baseSet_at x, 𝒱.mem_baseSet_at x⟩

/-- The common refinement refines the first cover. -/
def infLeft (𝒰 : TrivializationCover E M ι) (𝒱 : TrivializationCover E M κ) :
    (𝒰.inf 𝒱).Refines 𝒰 where
  map := Prod.fst
  subset _ := inter_subset_left

/-- The common refinement refines the second cover. -/
def infRight (𝒰 : TrivializationCover E M ι) (𝒱 : TrivializationCover E M κ) :
    (𝒰.inf 𝒱).Refines 𝒱 where
  map := Prod.snd
  subset _ := inter_subset_right

end TrivializationCover

variable {𝒲 : TrivializationCover E M κ'} {𝒱 : TrivializationCover E M κ}
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace MBVectorBundleCore

/-- A vector bundle trivialized over `𝒱`, **trivialized over a refinement** `𝒲`: the coordinate
changes are `g_{r(w) r(w')}`. -/
def refine (V : MBVectorBundleCore 𝒱 F) (r : 𝒲.Refines 𝒱) : MBVectorBundleCore 𝒲 F where
  coordChange w w₂ x := V.coordChange (r.map w) (r.map w₂) x
  map_add w w₂ x hx := V.map_add _ _ x ⟨r.subset w hx.1, r.subset w₂ hx.2⟩
  map_smul w w₂ x hx := V.map_smul _ _ x ⟨r.subset w hx.1, r.subset w₂ hx.2⟩
  coordChange_self w x hx := V.coordChange_self _ x (r.subset w hx)
  coordChange_comp w w₂ w₃ x hx :=
    V.coordChange_comp _ _ _ x ⟨⟨r.subset w hx.1.1, r.subset w₂ hx.1.2⟩, r.subset w₃ hx.2⟩
  smooth w w₂ n := by
    set i := r.map w
    set j := r.map w₂
    set D := 𝒲.transDomain w w₂
    have hD : IsOpen D := 𝒲.isOpen_transDomain w w₂
    have hDU : IsOpen (D ×ˢ (univ : Set F)) := hD.prod isOpen_univ
    have hFD : ContDiffMBOn n (TrivializationCover.refineRep r w) D :=
      (TrivializationCover.smoothMBOn_refineRep r w n).mono (𝒲.transDomain_subset_domain w w₂)
    have hfst : ContDiffMBOn n (ContinuousLinearMap.fst ℝ E F) (D ×ˢ univ) :=
      (ContinuousLinearMap.fst ℝ E F).contDiffMBOn n _
    have hsnd : ContDiffMBOn n (ContinuousLinearMap.snd ℝ E F) (D ×ˢ univ) :=
      (ContinuousLinearMap.snd ℝ E F).contDiffMBOn n _
    have h1 : ContDiffMBOn n
        (TrivializationCover.refineRep r w ∘ ContinuousLinearMap.fst ℝ E F) (D ×ˢ univ) :=
      ContDiffMBOn.comp (g := TrivializationCover.refineRep r w)
        (f := ContinuousLinearMap.fst ℝ E F) hDU hD hFD hfst fun q hq ↦ hq.1
    have h2 := (V.smooth i j n).comp hDU ((𝒱.isOpen_transDomain i j).prod isOpen_univ)
      (h1.prodMk hDU hsnd) fun q hq ↦
        ⟨TrivializationCover.mapsTo_refineRep_transDomain r w w₂ hq.1, mem_univ _⟩
    refine ContDiffMBOn.congr_of_isOpen hDU (fun q hq ↦ ?_) h2
    change V.coordChange i j ((𝒱.chart i).1.symm (TrivializationCover.refineRep r w q.1)) q.2 =
      V.coordChange i j ((𝒲.chart w).1.symm q.1) q.2
    rw [TrivializationCover.symm_refineRep r (𝒲.transDomain_subset_domain w w₂ hq.1)]

end MBVectorBundleCore

namespace BundleConnection

variable {V : MBVectorBundleCore 𝒱 F} (C : BundleConnection V) (r : 𝒲.Refines 𝒱)

open scoped Classical in
/-- The symbols of a connection in the trivializations of a refinement:
`Γ_{r(w)}(F y)(dF(y) a, ξ)` with `F = φ_{r(w)} ∘ φ_w⁻¹`, and `0` off the domain. -/
def refineSymbol (w : κ') (y a : E) (ξ : F) : F :=
  if y ∈ 𝒲.domain w then
    C.Γ (r.map w) (TrivializationCover.refineRep r w y)
      (dMB (TrivializationCover.refineRep r w) (y, a)) ξ
  else 0

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem refineSymbol_of_mem {w : κ'} {y : E} (hy : y ∈ 𝒲.domain w) (a : E) (ξ : F) :
    C.refineSymbol r w y a ξ = C.Γ (r.map w) (TrivializationCover.refineRep r w y)
      (dMB (TrivializationCover.refineRep r w) (y, a)) ξ := by
  simp [refineSymbol, hy]

theorem isLocalSymbol_refineSymbol (w : κ') :
    IsLocalSymbol (C.refineSymbol r w) (𝒲.domain w) := by
  set D := 𝒲.domain w
  have hD : IsOpen D := 𝒲.isOpen_domain w
  have hF := TrivializationCover.smoothMBOn_refineRep r w
  have hΓ := C.isLocalSymbol (r.map w)
  refine ⟨fun n ↦ ?_, fun y a a' ξ ↦ ?_, fun y c a ξ ↦ ?_, fun y a ξ ξ' ↦ ?_,
    fun y c a ξ ↦ ?_⟩
  · have hDU : IsOpen (D ×ˢ (univ : Set (E × F))) := hD.prod isOpen_univ
    have hfst := (ContinuousLinearMap.fst ℝ E (E × F)).contDiffMBOn n (D ×ˢ univ)
    have h₀ : ContDiffMBOn n (fun q : E × (E × F) ↦ TrivializationCover.refineRep r w q.1)
        (D ×ˢ univ) :=
      ContDiffMBOn.comp (g := TrivializationCover.refineRep r w)
        (f := ContinuousLinearMap.fst ℝ E (E × F)) hDU hD (hF n) hfst fun q hq ↦ hq.1
    have hpair : ContDiffMBOn n (fun q : E × (E × F) ↦ (q.1, q.2.1)) (D ×ˢ univ) :=
      ((ContinuousLinearMap.fst ℝ E (E × F)).prod ((ContinuousLinearMap.fst ℝ E F).comp
        (ContinuousLinearMap.snd ℝ E (E × F)))).contDiffMBOn n _
    have h₁ : ContDiffMBOn n
        (fun q : E × (E × F) ↦ dMB (TrivializationCover.refineRep r w) (q.1, q.2.1))
        (D ×ˢ univ) :=
      ContDiffMBOn.comp (g := dMB (TrivializationCover.refineRep r w)) hDU
        (hD.prod isOpen_univ) (hF (n + 1)).2.2 hpair fun q hq ↦ ⟨hq.1, mem_univ _⟩
    have h₂ : ContDiffMBOn n (fun q : E × (E × F) ↦ q.2.2) (D ×ˢ univ) :=
      ((ContinuousLinearMap.snd ℝ E F).comp
        (ContinuousLinearMap.snd ℝ E (E × F))).contDiffMBOn n _
    refine ContDiffMBOn.congr_of_isOpen hDU (fun q hq ↦ ?_)
      (hΓ.contDiffMBOn_comp hDU h₀ h₁ h₂ (𝒱.isOpen_domain _)
        fun q hq ↦ TrivializationCover.mapsTo_refineRep r w hq.1)
    exact (C.refineSymbol_of_mem r hq.1 _ _).symm
  · by_cases hy : y ∈ D
    · simp only [C.refineSymbol_of_mem r hy, (hF 1).dMB_add hD hy, hΓ.add_left]
    · simp [refineSymbol, D, hy]
  · by_cases hy : y ∈ D
    · simp only [C.refineSymbol_of_mem r hy, (hF 1).dMB_smul hy, hΓ.smul_left]
    · simp [refineSymbol, D, hy]
  · by_cases hy : y ∈ D
    · simp only [C.refineSymbol_of_mem r hy, hΓ.add_right]
    · simp [refineSymbol, D, hy]
  · by_cases hy : y ∈ D
    · simp only [C.refineSymbol_of_mem r hy, hΓ.smul_right]
    · simp [refineSymbol, D, hy]

/-- **A connection on a refinement**: the connection `∇` on `V`, written in the trivializations of
a refinement `𝒲` of the cover of `V`. -/
def refine : BundleConnection (V.refine r) where
  Γ := C.refineSymbol r
  isLocalSymbol := C.isLocalSymbol_refineSymbol r
  transition w w₂ y hy a ξ := by
    set i := r.map w
    set j := r.map w₂
    set Fp := TrivializationCover.refineRep r w
    set Fq := TrivializationCover.refineRep r w₂
    have hT : IsOpen (𝒲.transDomain w w₂) := 𝒲.isOpen_transDomain w w₂
    have hyp : y ∈ 𝒲.domain w := 𝒲.transDomain_subset_domain w w₂ hy
    have hyq : 𝒲.trans w w₂ y ∈ 𝒲.domain w₂ :=
      𝒲.transDomain_subset_domain w₂ w (𝒲.mapsTo_trans w w₂ hy)
    have hFp := TrivializationCover.smoothMBOn_refineRep r w
    have hFq := TrivializationCover.smoothMBOn_refineRep r w₂
    have hFpT : ContDiffMBOn 1 Fp (𝒲.transDomain w w₂) :=
      (hFp 1).mono (𝒲.transDomain_subset_domain w w₂)
    have hmapsT := TrivializationCover.mapsTo_refineRep_transDomain r w w₂
    have hw : Fp y ∈ 𝒱.transDomain i j := hmapsT hy
    have hsym : (𝒲.chart w).1.symm y = (𝒱.chart i).1.symm (Fp y) :=
      (TrivializationCover.symm_refineRep r hyp).symm
    have hd : dMB Fq (𝒲.trans w w₂ y, dMB (𝒲.trans w w₂) (y, a)) =
        dMB (𝒱.trans i j) (Fp y, dMB Fp (y, a)) := by
      have hev : Fq ∘ 𝒲.trans w w₂ =ᶠ[𝓝 y] 𝒱.trans i j ∘ Fp :=
        eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦
          TrivializationCover.refineRep_trans r hz
      rw [← ContDiffMBOn.dMB_comp (𝒲.isOpen_domain w₂) (hFq 1) (𝒲.smoothMBOn_trans w w₂ 1)
          (fun z hz ↦ 𝒲.transDomain_subset_domain w₂ w (𝒲.mapsTo_trans w w₂ hz)) hy a,
        dMB_congr_of_eventuallyEq hev,
        ContDiffMBOn.dMB_comp (𝒱.isOpen_transDomain i j) (𝒱.smoothMBOn_trans i j 1)
          hFpT hmapsT hy a]
    have hG : ContDiffMBOn 1 (fun z ↦ V.coordChange i j ((𝒱.chart i).1.symm z) ξ)
        (𝒱.transDomain i j) :=
      ContDiffMBOn.comp (g := fun q : E × F ↦ V.coordChange i j ((𝒱.chart i).1.symm q.1) q.2)
        (f := fun z ↦ (z, ξ)) (𝒱.isOpen_transDomain i j)
        ((𝒱.isOpen_transDomain i j).prod isOpen_univ) (V.smooth i j 1)
        (((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 _).prodMk (𝒱.isOpen_transDomain i j)
          (contDiffMBOn_const 1 ξ _)) fun z hz ↦ ⟨hz, mem_univ _⟩
    have hdg : dMB (fun z ↦ V.coordChange i j ((𝒲.chart w).1.symm z) ξ) (y, a) =
        dMB (fun z ↦ V.coordChange i j ((𝒱.chart i).1.symm z) ξ) (Fp y, dMB Fp (y, a)) := by
      have hev : (fun z ↦ V.coordChange i j ((𝒲.chart w).1.symm z) ξ) =ᶠ[𝓝 y]
          (fun z ↦ V.coordChange i j ((𝒱.chart i).1.symm z) ξ) ∘ Fp :=
        eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦ by
          change _ = V.coordChange i j ((𝒱.chart i).1.symm (Fp z)) ξ
          rw [TrivializationCover.symm_refineRep r (𝒲.transDomain_subset_domain w w₂ hz)]
      rw [dMB_congr_of_eventuallyEq hev,
        ContDiffMBOn.dMB_comp (𝒱.isOpen_transDomain i j) hG hFpT hmapsT hy a]
    have hTr := C.transition i j (Fp y) hw (dMB Fp (y, a)) ξ
    change C.refineSymbol r w₂ (𝒲.trans w w₂ y) (dMB (𝒲.trans w w₂) (y, a))
        (V.coordChange i j ((𝒲.chart w).1.symm y) ξ) =
      V.coordChange i j ((𝒲.chart w).1.symm y) (C.refineSymbol r w y a ξ) +
        dMB (fun z ↦ V.coordChange i j ((𝒲.chart w).1.symm z) ξ) (y, a)
    rw [C.refineSymbol_of_mem r hyq, C.refineSymbol_of_mem r hyp, hdg, hd,
      TrivializationCover.refineRep_trans r hy, hsym]
    exact hTr

end BundleConnection

/-! ### Hom bundles over different covers -/

section HomInf

variable {ι : Type*} {𝒰 : TrivializationCover E M ι}
  {F₁ F₂ : Type u} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- The bundle `Hom(V₁, V₂)` of bundles trivialized over different covers, trivialized over
their common refinement. -/
def homCoreInf (V₁ : MBVectorBundleCore 𝒰 F₁) (V₂ : MBVectorBundleCore 𝒱 F₂) :
    MBVectorBundleCore (𝒰.inf 𝒱) (F₁ →L[ℝ] F₂) :=
  homCore (V₁.refine (𝒰.infLeft 𝒱)) (V₂.refine (𝒰.infRight 𝒱))

/-- The connection on `Hom(V₁, V₂)` for bundles trivialized over different covers. -/
def BundleConnection.homInf {V₁ : MBVectorBundleCore 𝒰 F₁} {V₂ : MBVectorBundleCore 𝒱 F₂}
    (C₁ : BundleConnection V₁) (C₂ : BundleConnection V₂) :
    BundleConnection (homCoreInf V₁ V₂) :=
  (C₁.refine (𝒰.infLeft 𝒱)).hom (C₂.refine (𝒰.infRight 𝒱))

end HomInf

end LocallyConvex.Manifolds
