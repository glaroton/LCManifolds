/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Spray

/-!
# Covariant derivatives along curves and geodesics

References: S. Lang, *Fundamentals of Differential Geometry*, §VIII.3;
G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 6.

Let `α : ℝ → M` be a curve and `β : ℝ → TM` a lift of `α` (`β t ∈ T_{α t} M`). In a chart `i`,
write `α̃ = i ∘ α` and `μᵢ(t)` for the fiber coordinate of `β t`. The covariant derivative of `β`
along `α` is, in the chart,
`D_t β = μ̇ᵢ − Γᵢ(α̃)(α̃̇, μᵢ)`
(`covDerivAlong`, computed in the preferred chart at `α t`). It does not depend on the chart
(`covDerivAlong_chart`): differentiating `μⱼ = dτ(α̃) μᵢ` produces `d²τ(α̃̇, μᵢ)`, which cancels
with the term of the change of charts law of `Γ`.

A geodesic is a curve with `D_t α' = 0`, that is `α̃̈ = Γ(α̃̇, α̃̇)` in charts (`IsGeodesic`). Its
existence for given initial data is not claimed: it would need existence theorems for ODEs,
which fail in general locally convex spaces.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

section Calculus

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [LocallyConvexSpace ℝ E] in
/-- The derivative of a curve `t ↦ dτ(a t)(μ t)`:
`d²τ(a t)(ȧ t, μ t) + dτ(a t)(μ̇ t)`. -/
theorem dMB_dMB_curve {τ : E → F} {a μ : ℝ → E} {T : Set E} {O : Set ℝ} (hT : IsOpen T)
    (hO : IsOpen O) (hτ : ContDiffMBOn 2 τ T) (ha : ContDiffMBOn 1 a O)
    (hμ : ContDiffMBOn 1 μ O) (haT : MapsTo a O T) {t : ℝ} (ht : t ∈ O) :
    dMB (fun s ↦ dMB τ (a s, μ s)) (t, 1) =
      dMB (dMB τ) ((a t, μ t), (dMB a (t, 1), 0)) + dMB τ (a t, dMB μ (t, 1)) := by
  have hTU : IsOpen (T ×ˢ (univ : Set E)) := hT.prod isOpen_univ
  have hdτ : ContDiffMBOn 1 (dMB τ) (T ×ˢ univ) := hτ.2.2
  have hpair : ContDiffMBOn 1 (fun s ↦ (a s, μ s)) O := ha.prodMk hO hμ
  have hcomp := ContDiffMBOn.dMB_comp hTU hdτ hpair (fun s hs ↦ ⟨haT hs, mem_univ _⟩) ht 1
  have hdpair : dMB (fun s ↦ (a s, μ s)) (t, 1) = (dMB a (t, 1), dMB μ (t, 1)) :=
    ((ha.hasDirDerivAt ht 1).prodMk (hμ.hasDirDerivAt ht 1)).dMB_eq
  have hp : (a t, μ t) ∈ T ×ˢ (univ : Set E) := ⟨haT ht, mem_univ _⟩
  have hsplit : (dMB a (t, 1), dMB μ (t, 1)) = (dMB a (t, 1), (0 : E)) + (0, dMB μ (t, 1)) := by
    simp
  change dMB (dMB τ ∘ fun s ↦ (a s, μ s)) (t, 1) = _
  rw [hcomp, hdpair, hsplit, hdτ.dMB_add hTU hp, dMB_slice₂]
  obtain ⟨L, hL⟩ := (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).exists_clm hT (haT ht)
  have hfun : (fun w ↦ dMB τ (a t, w)) = ⇑L := funext fun w ↦ (hL w).symm
  rw [hfun, (L.hasDirDerivAt _ _).dMB_eq, hL]

end Calculus

section Manifold

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The fiber coordinates of a tangent vector in two charts are related by the derivative of the
transition map. -/
theorem tangentChart_snd_transition (i j : atlas E M) (p : TangentBundle E M)
    (hi : p.proj ∈ i.1.source) (hj : p.proj ∈ j.1.source) :
    (tangentChart j j.1 p).2 = dMB (j.1 ∘ i.1.symm) (i.1 p.proj, (tangentChart i i.1 p).2) := by
  obtain ⟨x, v⟩ := p
  change tangentCoordChange ⟨chartAt E x, chart_mem_atlas E x⟩ j x v =
    tangentCoordChange i j x (tangentCoordChange ⟨chartAt E x, chart_mem_atlas E x⟩ i x v)
  have key : ∀ w : E, tangentCoordChange ⟨chartAt E x, chart_mem_atlas E x⟩ j x w =
      tangentCoordChange i j x (tangentCoordChange ⟨chartAt E x, chart_mem_atlas E x⟩ i x w) :=
    fun w ↦ (tangentCoordChange_comp _ i j ⟨⟨mem_chart_source E x, hi⟩, hj⟩ w).symm
  exact key v

variable (E) in
/-- A `C^k` curve in `M`: continuous, with `C^k` local representatives `i ∘ α`. -/
def IsCkCurve (k : ℕ) (α : ℝ → M) : Prop :=
  Continuous α ∧ ∀ i : atlas E M, ContDiffMBOn k (i.1 ∘ α) (α ⁻¹' i.1.source)

/-- The fiber coordinate of a lift `β` of a curve, in the chart `i`. -/
def liftCoord (i : atlas E M) (β : ℝ → TangentBundle E M) (t : ℝ) : E :=
  (tangentChart i i.1 (β t)).2

/-- A `C^k` lift of the curve `α`: `β t ∈ T_{α t} M`, with `C^k` fiber coordinates. -/
def IsCkLift (k : ℕ) (α : ℝ → M) (β : ℝ → TangentBundle E M) : Prop :=
  (∀ t, (β t).proj = α t) ∧ ∀ i : atlas E M, ContDiffMBOn k (liftCoord i β) (α ⁻¹' i.1.source)

/-- The derivative of the local representative of a curve changes by the derivative of the
transition map: `d(j ∘ α)/dt = dτ (d(i ∘ α)/dt)`. -/
theorem dMB_chart_curve {α : ℝ → M} (hα : IsCkCurve E 1 α) (i j : atlas E M) {t : ℝ}
    (hti : α t ∈ i.1.source) (htj : α t ∈ j.1.source) :
    dMB (j.1 ∘ α) (t, 1) = dMB (j.1 ∘ i.1.symm) (i.1 (α t), dMB (i.1 ∘ α) (t, 1)) := by
  set O := α ⁻¹' (i.1.source ∩ j.1.source)
  have hO : IsOpen O := (i.1.open_source.inter j.1.open_source).preimage hα.1
  have hOt : t ∈ O := ⟨hti, htj⟩
  have hev : j.1 ∘ α =ᶠ[𝓝 t] (j.1 ∘ i.1.symm) ∘ (i.1 ∘ α) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hOt) fun s hs ↦ by simp [i.1.left_inv hs.1]
  rw [dMB_congr_of_eventuallyEq hev]
  exact ContDiffMBOn.dMB_comp (isOpen_transition_domain i j) (smoothMBOn_transition' i j 1)
    ((hα.2 i).mono (show O ⊆ α ⁻¹' i.1.source from fun s hs ↦ hs.1))
    (show MapsTo (i.1 ∘ α) O (i.1.target ∩ i.1.symm ⁻¹' j.1.source) from
      fun s hs ↦ ⟨i.1.map_source hs.1, by simp [i.1.left_inv hs.1, hs.2]⟩) hOt 1

variable (E) in
/-- The velocity `α'` of a curve, as a lift: the derivative of the local representative in the
preferred chart. -/
def velocity (α : ℝ → M) (t : ℝ) : TangentBundle E M :=
  ⟨α t, (dMB (chartAt E (α t) ∘ α) (t, 1) : E)⟩

/-- In any chart, the fiber coordinate of the velocity is the derivative of the local
representative. -/
theorem liftCoord_velocity {α : ℝ → M} (hα : IsCkCurve E 1 α) (j : atlas E M) {t : ℝ}
    (ht : α t ∈ j.1.source) : liftCoord j (velocity E α) t = dMB (j.1 ∘ α) (t, 1) := by
  rw [dMB_chart_curve hα ⟨chartAt E (α t), chart_mem_atlas E _⟩ j (mem_chart_source E _) ht]
  rfl

/-- The velocity of a `C^(k+1)` curve is a `C^k` lift. -/
theorem isCkLift_velocity {k : ℕ} {α : ℝ → M} (hα : IsCkCurve E (k + 1) α) :
    IsCkLift k α (velocity E α) := by
  have hα1 : IsCkCurve E 1 α := ⟨hα.1, fun i ↦ (hα.2 i).of_le (by omega)⟩
  refine ⟨fun _ ↦ rfl, fun j ↦ ?_⟩
  have hO : IsOpen (α ⁻¹' j.1.source) := j.1.open_source.preimage hα.1
  have hd : ContDiffMBOn k (dMB (j.1 ∘ α)) ((α ⁻¹' j.1.source) ×ˢ univ) := (hα.2 j).2.2
  have hpair : ContDiffMBOn k (fun s : ℝ ↦ (s, (1 : ℝ))) (α ⁻¹' j.1.source) :=
    ((ContinuousLinearMap.id ℝ ℝ).contDiffMBOn k _).prodMk hO (contDiffMBOn_const k 1 _)
  have hc := ContDiffMBOn.comp (g := dMB (j.1 ∘ α)) (f := fun s : ℝ ↦ (s, (1 : ℝ))) hO
    (hO.prod isOpen_univ) hd hpair fun s hs ↦ ⟨hs, mem_univ _⟩
  exact ContDiffMBOn.congr_of_isOpen hO (fun s hs ↦ (liftCoord_velocity hα1 j hs).symm) hc

namespace Connection

variable (C : Connection E M)

/-- The covariant derivative of a lift `β` along the curve `α`, computed in the preferred chart
at `α t`: `μ̇ − Γ(α̃)(α̃̇, μ)`. -/
def covDerivAlong (α : ℝ → M) (β : ℝ → TangentBundle E M) (t : ℝ) : E :=
  dMB (liftCoord ⟨chartAt E (α t), chart_mem_atlas E _⟩ β) (t, 1) -
    C.Γ ⟨chartAt E (α t), chart_mem_atlas E _⟩ (chartAt E (α t) (α t))
      (dMB (chartAt E (α t) ∘ α) (t, 1)) (liftCoord ⟨chartAt E (α t), chart_mem_atlas E _⟩ β t)

/-- **The covariant derivative along a curve does not depend on the chart**: read in any chart
`j` around `α t`, it is `μ̇ⱼ − Γⱼ(α̃ⱼ)(α̃̇ⱼ, μⱼ)`. -/
theorem covDerivAlong_chart {α : ℝ → M} {β : ℝ → TangentBundle E M} (hα : IsCkCurve E 1 α)
    (hβ : IsCkLift 1 α β) (j : atlas E M) {t : ℝ} (ht : α t ∈ j.1.source) :
    tangentCoordChange ⟨chartAt E (α t), chart_mem_atlas E _⟩ j (α t) (C.covDerivAlong α β t) =
      dMB (liftCoord j β) (t, 1) -
        C.Γ j (j.1 (α t)) (dMB (j.1 ∘ α) (t, 1)) (liftCoord j β t) := by
  set i : atlas E M := ⟨chartAt E (α t), chart_mem_atlas E _⟩
  have hti : α t ∈ i.1.source := mem_chart_source E _
  set τ := j.1 ∘ i.1.symm
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hτ : ContDiffMBOn 2 τ T := smoothMBOn_transition' i j 2
  have hτ1 : ContDiffMBOn 1 τ T := hτ.of_le (by norm_num)
  set O := α ⁻¹' (i.1.source ∩ j.1.source)
  have hO : IsOpen O := (i.1.open_source.inter j.1.open_source).preimage hα.1
  have hOt : t ∈ O := ⟨hti, ht⟩
  have ha : ContDiffMBOn 1 (i.1 ∘ α) O := (hα.2 i).mono fun s hs ↦ hs.1
  have hμ : ContDiffMBOn 1 (liftCoord i β) O := (hβ.2 i).mono fun s hs ↦ hs.1
  have haT : MapsTo (i.1 ∘ α) O T := fun s hs ↦
    ⟨i.1.map_source hs.1, by simp [i.1.left_inv hs.1, hs.2]⟩
  -- the local representatives in the chart `j`, near `t`
  have hev1 : j.1 ∘ α =ᶠ[𝓝 t] τ ∘ (i.1 ∘ α) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hOt) fun s hs ↦ by
      simp [τ, i.1.left_inv hs.1]
  have hev2 : liftCoord j β =ᶠ[𝓝 t] fun s ↦ dMB τ ((i.1 ∘ α) s, liftCoord i β s) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hOt) fun s hs ↦ by
      have h := tangentChart_snd_transition i j (β s) (by rw [hβ.1]; exact hs.1)
        (by rw [hβ.1]; exact hs.2)
      rw [hβ.1] at h
      exact h
  have hd1 : dMB (j.1 ∘ α) (t, 1) = dMB τ ((i.1 ∘ α) t, dMB (i.1 ∘ α) (t, 1)) := by
    rw [dMB_congr_of_eventuallyEq hev1]
    exact ContDiffMBOn.dMB_comp hT hτ1 ha haT hOt 1
  have hd2 : dMB (liftCoord j β) (t, 1) =
      dMB (dMB τ) (((i.1 ∘ α) t, liftCoord i β t), (dMB (i.1 ∘ α) (t, 1), 0)) +
        dMB τ ((i.1 ∘ α) t, dMB (liftCoord i β) (t, 1)) := by
    rw [dMB_congr_of_eventuallyEq hev2]
    exact dMB_dMB_curve hT hO hτ ha hμ haT hOt
  have hval : liftCoord j β t = dMB τ ((i.1 ∘ α) t, liftCoord i β t) := hev2.eq_of_nhds
  have hτt : τ ((i.1 ∘ α) t) = j.1 (α t) := by simp [τ, i.1.left_inv hti]
  have hΓ := C.transition i j ((i.1 ∘ α) t) (haT hOt) (dMB (i.1 ∘ α) (t, 1)) (liftCoord i β t)
  have hτdef : (j.1 ∘ i.1.symm) = τ := rfl
  rw [hτdef, hτt] at hΓ
  obtain ⟨L, hL⟩ := hτ1.exists_clm hT (haT hOt)
  rw [hd1, hd2, hval, hΓ]
  change dMB τ (i.1 (α t), _) = _
  simp only [Function.comp_apply] at hL ⊢
  rw [← hL, ← hL, ← hL]
  unfold covDerivAlong
  rw [map_sub]
  abel

/-- A geodesic: a curve whose velocity is parallel, `D_t α' = 0`. -/
def IsGeodesic (α : ℝ → M) : Prop := ∀ t, C.covDerivAlong α (velocity E α) t = 0

/-- **The geodesic equation**: a `C^2` curve is a geodesic if and only if, in every chart,
`α̃̈ = Γ(α̃)(α̃̇, α̃̇)`. -/
theorem isGeodesic_iff {α : ℝ → M} (hα : IsCkCurve E 2 α) :
    C.IsGeodesic α ↔ ∀ (j : atlas E M) (t : ℝ), α t ∈ j.1.source →
      dMB (fun s ↦ dMB (j.1 ∘ α) (s, 1)) (t, 1) =
        C.Γ j (j.1 (α t)) (dMB (j.1 ∘ α) (t, 1)) (dMB (j.1 ∘ α) (t, 1)) := by
  have hα1 : IsCkCurve E 1 α := ⟨hα.1, fun i ↦ (hα.2 i).of_le (by omega)⟩
  have hlift : IsCkLift 1 α (velocity E α) := isCkLift_velocity hα
  -- in a chart `j`, the covariant derivative of the velocity is `α̃̈ − Γ(α̃̇, α̃̇)`
  have hchart : ∀ (j : atlas E M) (t : ℝ), α t ∈ j.1.source →
      tangentCoordChange ⟨chartAt E (α t), chart_mem_atlas E _⟩ j (α t)
          (C.covDerivAlong α (velocity E α) t) =
        dMB (fun s ↦ dMB (j.1 ∘ α) (s, 1)) (t, 1) -
          C.Γ j (j.1 (α t)) (dMB (j.1 ∘ α) (t, 1)) (dMB (j.1 ∘ α) (t, 1)) := by
    intro j t ht
    have hO : IsOpen (α ⁻¹' j.1.source) := j.1.open_source.preimage hα.1
    have hev : liftCoord j (velocity E α) =ᶠ[𝓝 t] fun s ↦ dMB (j.1 ∘ α) (s, 1) :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds ht) fun s hs ↦ liftCoord_velocity hα1 j hs
    rw [C.covDerivAlong_chart hα1 hlift j ht, dMB_congr_of_eventuallyEq hev, hev.eq_of_nhds]
  constructor
  · intro hg j t ht
    have h := hchart j t ht
    rw [hg t, tangentCoordChange] at h
    obtain ⟨L, hL⟩ := (smoothMBOn_transition' ⟨chartAt E (α t), chart_mem_atlas E _⟩ j 1).exists_clm
      (isOpen_transition_domain _ j)
      (⟨(chartAt E (α t)).map_source (mem_chart_source E _), by
        simp [(chartAt E (α t)).left_inv (mem_chart_source E _), ht]⟩ :
        chartAt E (α t) (α t) ∈ (chartAt E (α t)).target ∩
          (chartAt E (α t)).symm ⁻¹' j.1.source)
    rw [← hL, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  · intro h t
    have hc := hchart ⟨chartAt E (α t), chart_mem_atlas E _⟩ t (mem_chart_source E _)
    rw [tangentCoordChange_self _ (mem_chart_source E _)] at hc
    rw [hc, h _ t (mem_chart_source E _), sub_self]

end Connection

end Manifold

end LCManifolds
