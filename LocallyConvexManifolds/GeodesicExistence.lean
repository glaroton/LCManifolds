/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.GeodesicBanach
import LocallyConvexAnalysis.QuadraticODE

/-!
# Local existence and uniqueness of geodesics on Banach manifolds

References: S. Lang, *Fundamentals of Differential Geometry*, Ch. IV §3 and VIII; G. Larotonda,
*Estructuras geométricas para las variedades de Banach*, §9.2.

Let `C` be a connection on a manifold modeled on a **Banach** space `E` (completeness is used by
Picard–Lindelöf). In a chart the geodesic equation is the quadratic second order equation
`c'' = Γ_c(c', c')`, so the results of `LocallyConvexAnalysis.QuadraticODE` give:

* `Connection.isSprayCurveOn_of_isGeodesicOn`: a geodesic read in any chart is a solution of the
  equation of the symbols of that chart, with velocity `deriv (φ ∘ α)`;
* `Connection.exists_isGeodesicOn_uniform` (**local existence with uniform time**): around a point
  of a chart there are `r > 0` and, for each bound `K` on the velocities, a time `ε > 0` such
  that every initial condition at distance `≤ r` (in the chart) with velocity `≤ K` has a geodesic
  defined on `(-ε, ε)`;
* `Connection.IsGeodesicOn.eqOn` (**uniqueness**): if `M` is Hausdorff, two geodesics on an
  interval `(a, b)` with the same position and velocity at one instant agree on `(a, b)`.

The Hausdorff hypothesis cannot be dropped: on the line with two origins, the two copies of a line
through the origins are geodesics of the flat connection with the same initial data.
-/

open Set Filter Metric
open scoped Topology ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  (C : Connection E M)

namespace Connection

omit [MBManifold E M] in
/-- The symbols of a chart are `C²` in the sense of Michal–Bastiani on `target × E × E`. -/
theorem contDiffMBOn_Γ (i : atlas E M) :
    ContDiffMBOn 2 (fun p : E × E × E ↦ C.Γ i p.1 p.2.1 p.2.2) (i.1.target ×ˢ univ) :=
  C.smooth i 2

/-- **A geodesic read in a chart is a solution of the equation of the symbols of the chart.** If
`α` is a geodesic on `I` and `J ⊆ I` is sent into the domain of the chart `i`, then `φᵢ ∘ α` solves
`c'' = Γᵢ(c)(c', c')` on `J`, with velocity `deriv (φᵢ ∘ α)`. -/
theorem isSprayCurveOn_of_isGeodesicOn {α : ℝ → M} {I J : Set ℝ} (h : C.IsGeodesicOn α I)
    (hJ : J ⊆ I) (i : atlas E M) (hJi : ∀ t ∈ J, α t ∈ i.1.source) :
    IsSprayCurveOn i.1.target (C.Γ i) J (i.1 ∘ α) (deriv (i.1 ∘ α)) := by
  intro t ht
  have htI : t ∈ I := hJ ht
  have hcont : ContinuousAt α t := (h.2.1 t htI).continuousAt (h.1.mem_nhds htI)
  obtain ⟨c₁, hc, hc₁⟩ := C.geodesicEqAt_of_chart hcont (mem_chart_source E (α t)) (hJi t ht)
    (h.2.2 t htI)
  have hev : c₁ =ᶠ[𝓝 t] deriv (i.1 ∘ α) := by
    filter_upwards [hc] with s hs using hs.deriv.symm
  have hd : deriv (i.1 ∘ α) t = c₁ t := hev.self_of_nhds.symm
  refine ⟨i.1.map_source (hJi t ht), ?_, ?_⟩
  · rw [hd]; exact hc.self_of_nhds
  · rw [hd]; exact hc₁.congr_of_eventuallyEq hev.symm

/-! ### Local existence -/

variable [CompleteSpace E]

/-- **Local existence of geodesics, with uniform time.** Let `y₀` be a point of the chart `i`.
There is `r > 0` such that for every `K ≥ 0` there is `ε > 0` with the following property: for
every `y` with `‖y - y₀‖ ≤ r` and every `w` with `‖w‖ ≤ K` there is a geodesic `α` on `(-ε, ε)`,
staying in the domain of `i`, with `φᵢ(α 0) = y` and `(φᵢ ∘ α)'(0) = w`. -/
theorem exists_isGeodesicOn_uniform (i : atlas E M) {y₀ : E} (hy₀ : y₀ ∈ i.1.target) :
    ∃ r > (0 : ℝ), ∀ K : ℝ, 0 ≤ K → ∃ ε > (0 : ℝ), ∀ y, ‖y - y₀‖ ≤ r → ∀ w, ‖w‖ ≤ K →
      ∃ α : ℝ → M, i.1 (α 0) = y ∧ HasDerivAt (i.1 ∘ α) w 0 ∧
        C.IsGeodesicOn α (Ioo (-ε) ε) ∧ ∀ t ∈ Ioo (-ε) ε, α t ∈ i.1.source := by
  obtain ⟨r, hr, H⟩ := exists_uniform_isSprayCurveOn_of_norm_le i.1.open_target
    (C.contDiffMBOn_Γ i) (fun x a b s ↦ C.smul_left i x s a b)
    (fun x a b s ↦ C.smul_right i x s a b) hy₀
  refine ⟨r, hr, fun K hK ↦ ?_⟩
  obtain ⟨ε, hε, H⟩ := H K hK
  refine ⟨ε, hε, fun y hy w hw ↦ ?_⟩
  obtain ⟨c, c', hc0, hc'0, hcs⟩ := H y hy w hw
  have hsub : Ioo (-ε) ε ⊆ Icc (-ε) ε := Ioo_subset_Icc_self
  set α : ℝ → M := fun t ↦ i.1.symm (c t)
  have hsrc : ∀ t ∈ Icc (-ε) ε, α t ∈ i.1.source := fun t ht ↦ i.1.map_target (hcs t ht).1
  -- near a point of `(-ε, ε)`, `φᵢ ∘ α = c`
  have hloc : ∀ t ∈ Ioo (-ε) ε, i.1 ∘ α =ᶠ[𝓝 t] c := fun t ht ↦ by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact i.1.right_inv (hcs s (hsub hs)).1
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
  have hcont : ContinuousOn α (Ioo (-ε) ε) := fun t ht ↦
    ((i.1.continuousOn_symm.continuousAt (i.1.open_target.mem_nhds (hcs t (hsub ht)).1)).comp
      (hcs t (hsub ht)).2.1.continuousAt).continuousWithinAt
  refine ⟨α, by simpa [α, hc0] using i.1.right_inv (hcs 0 (hsub h0)).1, ?_, ⟨isOpen_Ioo, hcont, ?_⟩,
    fun t ht ↦ hsrc t (hsub ht)⟩
  · rw [← hc'0]; exact (hcs 0 (hsub h0)).2.1.congr_of_eventuallyEq (hloc 0 h0)
  · intro t ht
    have hgi : C.GeodesicEqAt α i t := by
      refine ⟨c', ?_, ?_⟩
      · filter_upwards [Ioo_mem_nhds ht.1 ht.2, (hloc t ht).eventually_nhds] with s hs hs'
        exact (hcs s (hsub hs)).2.1.congr_of_eventuallyEq hs'
      · have hval : i.1 (α t) = c t := (hloc t ht).self_of_nhds
        rw [hval]; exact (hcs t (hsub ht)).2.2
    exact C.geodesicEqAt_of_chart ((hcont t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
      (hsrc t (hsub ht)) (mem_chart_source E _) hgi

/-- **Local existence of geodesics.** For every `x ∈ M` and every `v ∈ E` (a tangent vector read
in the chart `i` around `x`) there is a geodesic `α` on some `(-ε, ε)` with `α 0 = x` and
`(φᵢ ∘ α)'(0) = v`. -/
theorem exists_isGeodesicOn (i : atlas E M) {x : M} (hx : x ∈ i.1.source) (v : E) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → M, α 0 = x ∧ HasDerivAt (i.1 ∘ α) v 0 ∧
      C.IsGeodesicOn α (Ioo (-ε) ε) := by
  obtain ⟨r, hr, H⟩ := C.exists_isGeodesicOn_uniform i (i.1.map_source hx)
  obtain ⟨ε, hε, H⟩ := H ‖v‖ (norm_nonneg v)
  obtain ⟨α, h0, hv, hα, hsrc⟩ := H (i.1 x) (by simpa using hr.le) v le_rfl
  have h0' : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
  exact ⟨ε, hε, α, i.1.injOn (hsrc 0 h0') hx (by rw [h0]), hv, hα⟩

end Connection

/-! ### Uniqueness -/

namespace Connection

variable {C}

/-- Local step of uniqueness: near an instant `t` where two geodesics meet, there is an interval
`J ∋ t` such that the two geodesics agree on `J` as soon as their positions and velocities, read in
a chart `i` around the common point, agree at some instant of `J`. -/
theorem exists_Ioo_eqOn [CompleteSpace E] {α β : ℝ → M} {I : Set ℝ} (hα : C.IsGeodesicOn α I)
    (hβ : C.IsGeodesicOn β I) {t : ℝ} (ht : t ∈ I) (heq : α t = β t) (i : atlas E M)
    (hi : α t ∈ i.1.source) :
    ∃ δ > (0 : ℝ), Ioo (t - δ) (t + δ) ⊆ I ∧ ∀ τ ∈ Ioo (t - δ) (t + δ),
      (i.1 ∘ α) τ = (i.1 ∘ β) τ → deriv (i.1 ∘ α) τ = deriv (i.1 ∘ β) τ →
        EqOn α β (Ioo (t - δ) (t + δ)) := by
  have hαc : ContinuousAt α t := (hα.2.1 t ht).continuousAt (hα.1.mem_nhds ht)
  have hβc : ContinuousAt β t := (hβ.2.1 t ht).continuousAt (hβ.1.mem_nhds ht)
  have hN : I ∩ (α ⁻¹' i.1.source ∩ β ⁻¹' i.1.source) ∈ 𝓝 t :=
    inter_mem (hα.1.mem_nhds ht) (inter_mem (hαc.preimage_mem_nhds (i.1.open_source.mem_nhds hi))
      (hβc.preimage_mem_nhds (i.1.open_source.mem_nhds (heq ▸ hi))))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hN
  rw [Real.ball_eq_Ioo] at hball
  refine ⟨δ, hδ, fun s hs ↦ (hball hs).1, fun τ hτ hx hv ↦ ?_⟩
  have hsα := C.isSprayCurveOn_of_isGeodesicOn hα (fun s hs ↦ (hball hs).1) i
    (fun s hs ↦ (hball hs).2.1)
  have hsβ := C.isSprayCurveOn_of_isGeodesicOn hβ (fun s hs ↦ (hball hs).1) i
    (fun s hs ↦ (hball hs).2.2)
  have H := (hsα.eqOn_Ioo i.1.open_target (C.contDiffMBOn_Γ i) hsβ hτ hx hv).1
  exact fun s hs ↦ i.1.injOn (hball hs).2.1 (hball hs).2.2 (H hs)

/-- **Uniqueness of geodesics.** On a Hausdorff manifold modeled on a Banach space, two geodesics
on `(a, b)` with the same position at `t₀ ∈ (a, b)` and the same velocity there (read in a chart
`i` around that point) agree on `(a, b)`. -/
theorem IsGeodesicOn.eqOn [CompleteSpace E] [T2Space M] {α β : ℝ → M} {a b : ℝ}
    (hα : C.IsGeodesicOn α (Ioo a b)) (hβ : C.IsGeodesicOn β (Ioo a b)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (heq : α t₀ = β t₀) (i : atlas E M) (hi : α t₀ ∈ i.1.source)
    (hv : deriv (i.1 ∘ α) t₀ = deriv (i.1 ∘ β) t₀) : EqOn α β (Ioo a b) := by
  set u : Set ℝ := {t | α =ᶠ[𝓝 t] β}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  -- the set where the geodesics agree near `t` is all of `(a, b)`
  have hsub : Ioo a b ⊆ u := by
    refine isPreconnected_Ioo.subset_of_closure_inter_subset hu ⟨t₀, ht₀, ?_⟩ ?_
    · obtain ⟨δ, hδ, _, H⟩ := exists_Ioo_eqOn hα hβ ht₀ heq i hi
      have hmem : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs
      exact H t₀ hmem (by simp [heq]) hv hs
    · rintro t ⟨htc, ht⟩
      have hfreq : ∃ᶠ τ in 𝓝 t, τ ∈ u := mem_closure_iff_frequently.mp htc
      -- the geodesics meet at `t`, since `M` is Hausdorff
      have heqt : α t = β t :=
        tendsto_nhds_unique_of_frequently_eq
          ((hα.2.1 t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
          ((hβ.2.1 t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
          (hfreq.mono fun τ hτ ↦ hτ.self_of_nhds)
      set j : atlas E M := ⟨chartAt E (α t), chart_mem_atlas E _⟩
      obtain ⟨δ, hδ, _, H⟩ := exists_Ioo_eqOn hα hβ ht heqt j (mem_chart_source E _)
      have hmem : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
      obtain ⟨τ, hτu, hτ⟩ := (hfreq.and_eventually (Ioo_mem_nhds hmem.1 hmem.2)).exists
      have hτeq : j.1 ∘ α =ᶠ[𝓝 τ] j.1 ∘ β := hτu.fun_comp j.1
      have hEq := H τ hτ hτeq.self_of_nhds hτeq.deriv_eq
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs using hEq hs
  exact fun t ht ↦ (hsub ht).self_of_nhds

end Connection

/-! ### The geodesic equation is local; extension of geodesics -/

namespace Connection

variable {C}

omit [MBManifold E M] in
/-- The geodesic equation at `t` only depends on the germ of the curve at `t`. -/
theorem GeodesicEqAt.congr {α β : ℝ → M} {j : atlas E M} {t : ℝ} (h : C.GeodesicEqAt α j t)
    (hαβ : α =ᶠ[𝓝 t] β) : C.GeodesicEqAt β j t := by
  obtain ⟨c₁, hc, hc₁⟩ := h
  refine ⟨c₁, ?_, by rwa [← hαβ.self_of_nhds]⟩
  filter_upwards [hc, hαβ.eventually_nhds] with s hs hs'
  have hs'' : α =ᶠ[𝓝 s] β := hs'
  exact hs.congr_of_eventuallyEq (hs''.fun_comp j.1).symm

omit [MBManifold E M] in
theorem IsGeodesicOn.mono {α : ℝ → M} {I J : Set ℝ} (h : C.IsGeodesicOn α I) (hJ : IsOpen J)
    (hJI : J ⊆ I) : C.IsGeodesicOn α J :=
  ⟨hJ, h.2.1.mono hJI, fun t ht ↦ h.2.2 t (hJI ht)⟩

omit [MBManifold E M] in
/-- **Being a geodesic is a local property**: `β` is a geodesic on the open set `I` if near every
`t ∈ I` it agrees with some geodesic. -/
theorem isGeodesicOn_of_local {β : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (h : ∀ t ∈ I, ∃ γ : ℝ → M, ∃ J : Set ℝ, t ∈ J ∧ C.IsGeodesicOn γ J ∧ EqOn β γ J) :
    C.IsGeodesicOn β I := by
  have key : ∀ t ∈ I, ContinuousAt β t ∧
      C.GeodesicEqAt β ⟨chartAt E (β t), chart_mem_atlas E _⟩ t := by
    intro t ht
    obtain ⟨γ, J, htJ, hγ, hEq⟩ := h t ht
    have hev : γ =ᶠ[𝓝 t] β := by
      filter_upwards [hγ.1.mem_nhds htJ] with s hs using (hEq hs).symm
    refine ⟨((hγ.2.1 t htJ).continuousAt (hγ.1.mem_nhds htJ)).congr hev, ?_⟩
    rw [hEq htJ]
    exact (hγ.2.2 t htJ).congr hev
  exact ⟨hI, fun t ht ↦ (key t ht).1.continuousWithinAt, fun t ht ↦ (key t ht).2⟩

omit [MBManifold E M] in
/-- A translate of a geodesic is a geodesic. -/
theorem IsGeodesicOn.comp_sub {α : ℝ → M} {I : Set ℝ} (h : C.IsGeodesicOn α I) (t₁ : ℝ) :
    C.IsGeodesicOn (fun t ↦ α (t - t₁)) ((· - t₁) ⁻¹' I) := by
  have hcont : Continuous fun t : ℝ ↦ t - t₁ := continuous_sub_right t₁
  refine ⟨h.1.preimage hcont, h.2.1.comp hcont.continuousOn (mapsTo_preimage _ _), fun t ht ↦ ?_⟩
  obtain ⟨c₁, hc, hc₁⟩ := h.2.2 _ ht
  have htend : Tendsto (fun s : ℝ ↦ s - t₁) (𝓝 t) (𝓝 (t - t₁)) := hcont.continuousAt
  refine ⟨fun s ↦ c₁ (s - t₁), ?_, hc₁.comp_sub_const t t₁⟩
  filter_upwards [htend.eventually hc] with s hs
  exact hs.comp_sub_const s t₁

/-- **Extension of geodesics.** On a Hausdorff manifold modeled on a Banach space, let `α` be a
geodesic on `(a, b)` that converges to a point `q` as `t → b⁻`, and whose velocity, read in a chart
`i` around `q`, stays bounded as `t → b⁻`. Then `α` extends to a geodesic on some `(a, b')` with
`b' > b`. -/
theorem IsGeodesicOn.exists_extend [CompleteSpace E] [T2Space M] {α : ℝ → M} {a b : ℝ}
    (hα : C.IsGeodesicOn α (Ioo a b)) (hab : a < b) {q : M} (i : atlas E M)
    (hq : q ∈ i.1.source) (hlim : Tendsto α (𝓝[<] b) (𝓝 q)) {K : ℝ}
    (hK : ∀ᶠ t in 𝓝[<] b, ‖deriv (i.1 ∘ α) t‖ ≤ K) :
    ∃ b' > b, ∃ β : ℝ → M, C.IsGeodesicOn β (Ioo a b') ∧ EqOn β α (Ioo a b) := by
  obtain ⟨r, hr, H⟩ := C.exists_isGeodesicOn_uniform i (i.1.map_source hq)
  have hK0 : 0 ≤ K := by
    obtain ⟨t, ht⟩ := hK.exists
    exact (norm_nonneg _).trans ht
  obtain ⟨ε, hε, H⟩ := H K hK0
  -- an instant `t₁ ∈ (b - ε / 2, b)` where `α` is close to `q`, with velocity `≤ K`
  have hsrc : ∀ᶠ t in 𝓝[<] b, α t ∈ i.1.source := hlim (i.1.open_source.mem_nhds hq)
  have hclose : ∀ᶠ t in 𝓝[<] b, ‖i.1 (α t) - i.1 q‖ ≤ r := by
    have hc : Tendsto (fun t ↦ i.1 (α t)) (𝓝[<] b) (𝓝 (i.1 q)) :=
      ((i.1.continuousOn.continuousAt (i.1.open_source.mem_nhds hq)).tendsto).comp hlim
    filter_upwards [hc (closedBall_mem_nhds _ hr)] with t ht
    simpa [dist_eq_norm] using ht
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo (max a (b - ε / 2)) b :=
    Ioo_mem_nhdsLT (max_lt hab (by linarith))
  obtain ⟨t₁, ht₁, hsrc₁, hclose₁, hK₁⟩ := (hnear.and (hsrc.and (hclose.and hK))).exists
  have hb₁ : b - ε / 2 < t₁ := (le_max_right _ _).trans_lt ht₁.1
  -- the geodesic `μ` with the data of `α` at `t₁`, translated to `t₁`
  obtain ⟨μ, hμ0, hμv, hμ, hμsrc⟩ := H (i.1 (α t₁)) hclose₁ (deriv (i.1 ∘ α) t₁) hK₁
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
  set μ' : ℝ → M := fun t ↦ μ (t - t₁)
  have hμ' : C.IsGeodesicOn μ' (Ioo (t₁ - ε) (t₁ + ε)) := by
    have hpre : (fun t : ℝ ↦ t - t₁) ⁻¹' Ioo (-ε) ε = Ioo (t₁ - ε) (t₁ + ε) := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [← hpre]
    exact hμ.comp_sub t₁
  -- `α` and `μ'` agree where both are defined
  set J := Ioo (max a (t₁ - ε)) b
  have ht₁J : t₁ ∈ J := ⟨max_lt ((le_max_left _ _).trans_lt ht₁.1) (by linarith), ht₁.2⟩
  have hJα : C.IsGeodesicOn α J := hα.mono isOpen_Ioo (Ioo_subset_Ioo_left (le_max_left _ _))
  have hJμ : C.IsGeodesicOn μ' J :=
    hμ'.mono isOpen_Ioo (Ioo_subset_Ioo (le_max_right _ _) (by linarith))
  have heq : α t₁ = μ' t₁ := by
    show α t₁ = μ (t₁ - t₁)
    rw [sub_self]
    exact i.1.injOn hsrc₁ (hμsrc 0 h0) hμ0.symm
  have hv : deriv (i.1 ∘ α) t₁ = deriv (i.1 ∘ μ') t₁ := by
    have hd : HasDerivAt (i.1 ∘ μ') (deriv (i.1 ∘ α) t₁) t₁ :=
      HasDerivAt.comp_sub_const t₁ t₁ (by simpa using hμv)
    exact hd.deriv.symm
  have hagree : EqOn α μ' J := IsGeodesicOn.eqOn hJα hJμ ht₁J heq i hsrc₁ hv
  -- glue `α` (up to `t₁`) and `μ'` (after `t₁`)
  set β : ℝ → M := fun t ↦ if t ≤ t₁ then α t else μ' t
  have hβα : EqOn β α (Ioo a b) := fun t ht ↦ by
    by_cases htt : t ≤ t₁
    · simp [β, htt]
    · simp only [β, htt, ↓reduceIte]
      exact (hagree ⟨ht₁J.1.trans (lt_of_not_ge htt), ht.2⟩).symm
  set J' := Ioo (max a (t₁ - ε)) (t₁ + ε)
  have hβμ : EqOn β μ' J' := fun t ht ↦ by
    by_cases htt : t ≤ t₁
    · simp only [β, htt, ↓reduceIte]
      exact hagree ⟨ht.1, htt.trans_lt ht₁.2⟩
    · simp [β, htt]
  refine ⟨t₁ + ε, by linarith, β, isGeodesicOn_of_local isOpen_Ioo fun t ht ↦ ?_, hβα⟩
  by_cases htb : t < b
  · exact ⟨α, Ioo a b, ⟨ht.1, htb⟩, hα, hβα⟩
  · refine ⟨μ', J', ⟨max_lt ht.1 (by linarith [not_lt.mp htb, ht₁.2]), ht.2⟩,
      hμ'.mono isOpen_Ioo (Ioo_subset_Ioo_left (le_max_right _ _)), hβμ⟩

end Connection

end LocallyConvex.Manifolds
