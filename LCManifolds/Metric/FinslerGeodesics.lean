/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.GeodesicExistence
import LCManifolds.Metric.FinslerBounded

/-!
# Geodesics of complete Finsler manifolds

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach* (version of
29 November 2023), Cap. 9, §9.2 *Variedades de Finsler con spray*, Proposición 9.2.1.

Let `M` be a Hausdorff manifold modeled on a **Banach** space `E`, with a connection (a quadratic
spray) and a Finsler length structure `μ`. Proposición 9.2.1 states that, for a strong Finsler
manifold with spray, completeness of `(M, d_b)` implies that every geodesic is defined on all of
`ℝ`. Its proof: along a geodesic `α` on `(a, b)`, `b < ∞`, of constant speed `‖α̇‖ = ‖v‖`, one
has `d_b(α(tₙ), α(tₘ)) ≤ (tₘ - tₙ) ‖v‖`, so `α(tₙ)` is Cauchy and converges to some `q`; near `q`
geodesics with bounded initial velocity exist for a uniform time, and by uniqueness one of them
continues `α` past `b`. This file formalizes this implication (`1 ⇒ 2`).

## Main results

* `Connection.IsGeodesicOn.comp_neg`: the reversed curve `t ↦ α (-t)` of a geodesic is a
  geodesic (the symbols are bilinear).
* `Connection.IsGeodesicOn.isCkCurve_comp`, `Connection.IsGeodesicOn.velocity_comp`: a geodesic
  reparametrized by a `C¹` map `ρ : ℝ → I` is a `C¹` curve on all of `ℝ`, with velocity
  `ρ' · α̇ ∘ ρ`. This is how arcs of geodesics, which are only defined on an open interval,
  become competitors in the definition of `d_b` (which uses curves `ℝ → M`).
* `Connection.IsGeodesicOn.dist_le_of_speed_le`: `μ(α̇) ≤ L` on `[s, t]` gives
  `d_b(α s, α t) ≤ L (t - s)`; `dist_le_of_speed_le_rev` is the backward version.
* `Connection.IsGeodesicOn.exists_tendsto`: a geodesic of bounded speed converges at a finite end
  of its interval when `(M, d_b)` is complete and `μ` is bounded below.
* `Connection.IsGeodesicOn.exists_extend_of_complete` (**Proposición 9.2.1, `1 ⇒ 2`**): such a
  geodesic extends past both ends of its interval; `exists_extend_right_of_complete` and
  `exists_extend_left_of_complete` treat each end.

## Hypotheses, compared with *Estructuras*

* **Speed.** In *Estructuras* a Finsler manifold *with spray* has a metric invariant under the
  parallel transport of the spray along geodesics, so geodesics have constant speed. We only
  assume that the **speed `μ(α̇)` and the backward speed `μ(-α̇)` are bounded** on `(a, b)`. This
  is weaker; both bounds hold, with the same constant, under the invariance hypothesis, which
  applies to `-α̇` too. The backward speed is written as the speed of the reversed curve,
  `μ (velocity (fun σ ↦ α (-σ)) (-τ))`. It is needed because `μ` may be **non-reversible**: then
  `d_b` is asymmetric, and a Cauchy argument needs both `d_b(α s, α t)` and `d_b(α t, α s)`.
* **Completeness.** `(M, d_b)` is complete for the symmetrized distance
  `max (d_b(x, y), d_b(y, x))`, the uniform structure of `FinslerSpace μ`. For a reversible `μ`
  this is the completeness of `(M, d_b)` itself.
* **Boundedness.** The book assumes a *strong* Finsler manifold (`μ` bounded above and below).
  Only the **lower bound** (`FinslerSeminormField.IsBoundedBelow`) is used: it makes the identity
  `(M, d_b) → M` continuous (Lema 9.1.8), so the `d_b`-limit is a limit in `M`, and it turns the
  bound on `μ(α̇)` into a bound on the velocity read in a chart near the limit point.
* **Banach model, Hausdorff manifold.** Completeness of `E` is used by the Picard–Lindelöf theorem
  (local existence with uniform time, replacing the normal neighborhoods of Teorema 6.2.3) and by
  Lema 9.1.8; the Hausdorff property by uniqueness of geodesics and by Lema 9.1.8.

**Infinite-dimensional subtleties.** No local compactness is available, so the extension
argument cannot rely on compactness of closed balls: it rests on the existence time being
uniform for initial velocities bounded *in a chart*. That is why the bound on `μ(α̇)` must be
transferred to the chart, which needs the lower bound `‖φ_{*}v‖ ≤ C μ(v)`. In infinite dimension
a Finsler norm need not be equivalent to the norm of the model, and without the lower bound a
`μ`-bounded velocity may be unbounded in every chart. The speed hypotheses are stated for one
geodesic, so the statement "every maximal geodesic is defined on `ℝ`" is not formalized here:
maximal geodesics are not constructed in this library. Under the invariance hypothesis of the
book it follows from `exists_extend_of_complete` once they are.
-/

open Set Filter
open scoped Topology ENNReal ContDiff
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-! ### Velocities of curves that are differentiable in charts -/

/-- If the representative of `α` in the preferred chart at `α t` has derivative `v` at `t`, then
the velocity of `α` at `t` is `v`. -/
theorem velocity_eq_of_hasDerivAt {α : ℝ → M} {t : ℝ} {v : E}
    (h : HasDerivAt (chartAt E (α t) ∘ α) v t) : velocity E α t = ⟨α t, v⟩ := by
  have hd : dMB (chartAt E (α t) ∘ α) (t, 1) = v := by
    simpa using (h.hasFDerivAt.hasDirDerivAt (1 : ℝ)).dMB_eq
  unfold velocity
  rw [hd]

/-- **Change of chart for velocities.** If `α` is continuous at `t` and its representative in
the preferred chart at `α t` has derivative `v` at `t`, then its representative in any chart `i`
around `α t` has derivative `φ_{*}(v)`, the tangent coordinate change of `v`. -/
theorem hasDerivAt_chart_of_hasDerivAt {α : ℝ → M} {t : ℝ} {v : E} (hα : ContinuousAt α t)
    (h : HasDerivAt (chartAt E (α t) ∘ α) v t) (i : atlas E M) (hi : α t ∈ i.1.source) :
    HasDerivAt (i.1 ∘ α) (tangentCoordChange (prefAtlas E (α t)) i (α t) v) t := by
  set j : atlas E M := prefAtlas E (α t)
  have hj : α t ∈ j.1.source := mem_chart_source E (α t)
  set T := j.1.target ∩ j.1.symm ⁻¹' i.1.source
  have hT : IsOpen T := isOpen_transition_domain j i
  have hτ : ContDiffOn ℝ 1 (i.1 ∘ j.1.symm) T :=
    ((smoothMBOn_iff_contDiffOn hT).mp (smoothMBOn_transition' j i)).of_le (by simp)
  have hy : j.1 (α t) ∈ T := ⟨j.1.map_source hj, by simp [j.1.left_inv hj, hi]⟩
  have hD : HasFDerivAt (i.1 ∘ j.1.symm) (fderiv ℝ (i.1 ∘ j.1.symm) (j.1 (α t))) (j.1 (α t)) :=
    ((hτ.contDiffAt (hT.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
  have hcomp := hD.comp_hasDerivAt t h
  have hnear : ∀ᶠ s in 𝓝 t, α s ∈ j.1.source ∩ i.1.source :=
    hα.preimage_mem_nhds ((j.1.open_source.inter i.1.open_source).mem_nhds ⟨hj, hi⟩)
  have heq : (i.1 ∘ j.1.symm) ∘ (j.1 ∘ α) =ᶠ[𝓝 t] i.1 ∘ α := by
    filter_upwards [hnear] with s hs
    simp [j.1.left_inv hs.1]
  rw [show tangentCoordChange j i (α t) v = fderiv ℝ (i.1 ∘ j.1.symm) (j.1 (α t)) v from
    dMB_eq_fderiv hT hτ hy v]
  exact hcomp.congr_of_eventuallyEq heq.symm

/-! ### Geodesics in charts; reversed geodesics -/

namespace Connection

variable {C : Connection E M} {α : ℝ → M} {I : Set ℝ}

/-- A geodesic read in a chart `i` is differentiable, with derivative `deriv (φᵢ ∘ α)`. -/
theorem IsGeodesicOn.hasDerivAt_chart (hα : C.IsGeodesicOn α I) {t : ℝ} (ht : t ∈ I)
    (i : atlas E M) (hi : α t ∈ i.1.source) : HasDerivAt (i.1 ∘ α) (deriv (i.1 ∘ α) t) t :=
  (C.isSprayCurveOn_of_isGeodesicOn hα (singleton_subset_iff.2 ht) i
    (fun s hs ↦ by rw [mem_singleton_iff.1 hs]; exact hi) t rfl).2.1

/-- The velocity of a geodesic is the derivative of its representative in the preferred chart. -/
theorem IsGeodesicOn.velocity_eq (hα : C.IsGeodesicOn α I) {t : ℝ} (ht : t ∈ I) :
    velocity E α t = ⟨α t, deriv (chartAt E (α t) ∘ α) t⟩ :=
  velocity_eq_of_hasDerivAt (hα.hasDerivAt_chart ht ⟨_, chart_mem_atlas E _⟩
    (mem_chart_source E _))

/-- The derivative of a geodesic read in a chart `i` is the coordinate change of its velocity. -/
theorem IsGeodesicOn.deriv_chart_eq (hα : C.IsGeodesicOn α I) {t : ℝ} (ht : t ∈ I)
    (i : atlas E M) (hi : α t ∈ i.1.source) :
    deriv (i.1 ∘ α) t =
      tangentCoordChange (prefAtlas E (α t)) i (α t) (deriv (chartAt E (α t) ∘ α) t) :=
  (hasDerivAt_chart_of_hasDerivAt ((hα.2.1 t ht).continuousAt (hα.1.mem_nhds ht))
    (hα.hasDerivAt_chart ht ⟨_, chart_mem_atlas E _⟩ (mem_chart_source E _)) i hi).deriv

/-- A geodesic read in a chart is a Fréchet `C¹` curve where it is defined. -/
theorem IsGeodesicOn.contDiffOn_chart (hα : C.IsGeodesicOn α I) (i : atlas E M) :
    ContDiffOn ℝ 1 (i.1 ∘ α) (I ∩ α ⁻¹' i.1.source) := by
  have hJ : IsOpen (I ∩ α ⁻¹' i.1.source) := hα.2.1.isOpen_inter_preimage hα.1 i.1.open_source
  have hs := C.isSprayCurveOn_of_isGeodesicOn (J := I ∩ α ⁻¹' i.1.source) hα inter_subset_left i
    fun t ht ↦ ht.2
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hJ]
  refine ⟨fun t ht ↦ (hs t ht).2.1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact fun t ht ↦ (hs t ht).2.2.continuousAt.continuousWithinAt

/-- **A reparametrized geodesic is a `C¹` curve.** If `h : ℝ → ℝ` is `C¹` with values in `I`,
the curve `α ∘ h`, defined on all of `ℝ`, is `C¹`. -/
theorem IsGeodesicOn.isCkCurve_comp (hα : C.IsGeodesicOn α I) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hI : ∀ x, h x ∈ I) : IsCkCurve E 1 (α ∘ h) := by
  refine ⟨hα.2.1.comp_continuous hh.continuous hI, fun i ↦ ?_⟩
  have hO : IsOpen ((α ∘ h) ⁻¹' i.1.source) :=
    i.1.open_source.preimage (hα.2.1.comp_continuous hh.continuous hI)
  refine ContDiffOn.contDiffMBOn (k := 1) hO ?_
  have := (hα.contDiffOn_chart i).comp hh.contDiffOn (s := (α ∘ h) ⁻¹' i.1.source)
    fun x hx ↦ ⟨hI x, hx⟩
  exact this

/-- The velocity of a reparametrized geodesic: `(α ∘ h)'(x) = h'(x) α'(h x)`. -/
theorem IsGeodesicOn.velocity_comp (hα : C.IsGeodesicOn α I) {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hI : ∀ x, h x ∈ I) (x : ℝ) :
    velocity E (α ∘ h) x =
      ⟨α (h x), deriv h x • deriv (chartAt E (α (h x)) ∘ α) (h x)⟩ := by
  have hd := hα.hasDerivAt_chart (hI x) ⟨_, chart_mem_atlas E _⟩ (mem_chart_source E _)
  have hh' : HasDerivAt h (deriv h x) x :=
    ((hh.differentiable one_ne_zero) x).hasDerivAt
  exact velocity_eq_of_hasDerivAt (hd.scomp x hh')

omit [MBManifold E M] in
/-- **The reversed curve `t ↦ α (-t)` of a geodesic is a geodesic.** The symbols of a connection
are bilinear, so `Γ(-v, -v) = Γ(v, v)`. -/
theorem IsGeodesicOn.comp_neg (hα : C.IsGeodesicOn α I) :
    C.IsGeodesicOn (fun t ↦ α (-t)) (Neg.neg ⁻¹' I) := by
  refine ⟨hα.1.preimage continuous_neg,
    hα.2.1.comp continuous_neg.continuousOn (mapsTo_preimage _ _), fun t ht ↦ ?_⟩
  obtain ⟨c₁, hc, hc₁⟩ := hα.2.2 (-t) ht
  have htend : Tendsto (fun s : ℝ ↦ -s) (𝓝 t) (𝓝 (-t)) := continuous_neg.continuousAt
  refine ⟨fun s ↦ -c₁ (-s), ?_, ?_⟩
  · filter_upwards [htend.eventually hc] with s hs
    simpa [Function.comp_def] using hs.scomp s (hasDerivAt_neg s)
  · have h := (hc₁.scomp t (hasDerivAt_neg t)).neg
    have hΓ : ∀ (j : atlas E M) (y v : E), C.Γ j y (-v) (-v) = C.Γ j y v v := fun j y v ↦ by
      rw [← neg_one_smul ℝ v, C.smul_left, C.smul_right, smul_smul]
      norm_num
    simp only [neg_one_smul, neg_neg] at h
    simp only [hΓ]
    exact h

end Connection

/-! ### A smooth ramp -/

/-- A smooth nondecreasing map `ℝ → [s, t]` with `s ↦ s` and `t ↦ t`, built from
`Real.smoothTransition`. Composing a curve defined on an open interval containing `[s, t]` with it
gives a curve defined on all of `ℝ` with the same endpoints on `[s, t]`. -/
def smoothRamp (s t x : ℝ) : ℝ := s + (t - s) * Real.smoothTransition ((x - s) / (t - s))

theorem contDiff_smoothRamp (s t : ℝ) : ContDiff ℝ 1 (smoothRamp s t) := by
  have h1 : ContDiff ℝ 1 Real.smoothTransition := by
    simpa using Real.smoothTransition.contDiff (n := 1)
  exact contDiff_const.add (contDiff_const.mul (h1.comp ((contDiff_id.sub contDiff_const).div_const
    _)))

@[simp] theorem smoothRamp_left (s t : ℝ) : smoothRamp s t s = s := by simp [smoothRamp]

theorem smoothRamp_right {s t : ℝ} (hst : s < t) : smoothRamp s t t = t := by
  simp [smoothRamp, div_self (sub_ne_zero.2 hst.ne')]

theorem smoothRamp_mem {s t : ℝ} (hst : s ≤ t) (x : ℝ) : smoothRamp s t x ∈ Icc s t := by
  have h0 := Real.smoothTransition.nonneg ((x - s) / (t - s))
  have h1 := Real.smoothTransition.le_one ((x - s) / (t - s))
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  constructor <;> simp only [smoothRamp] <;> nlinarith

theorem monotone_smoothRamp {s t : ℝ} (hst : s ≤ t) : Monotone (smoothRamp s t) := by
  intro x y hxy
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have := Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hxy s) hts)
  simp only [smoothRamp]
  nlinarith

theorem integral_deriv_smoothRamp {s t : ℝ} (hst : s < t) :
    ∫ x in s..t, deriv (smoothRamp s t) x = t - s := by
  have hc := contDiff_smoothRamp s t
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ hc.differentiable one_ne_zero x)
    ((hc.continuous_deriv le_rfl).intervalIntegrable _ _), smoothRamp_left, smoothRamp_right hst]

/-! ### Distance travelled along a geodesic -/

namespace Connection

variable {C : Connection E M} {α : ℝ → M} {I : Set ℝ} (μ : FinslerLengthStructure E M)

/-- **The distance between two points of a geodesic is at most speed times time.** If `α` is a
geodesic on `I ⊇ [s, t]` with `μ(α̇) ≤ L` on `[s, t]`, then `d_b(α s, α t) ≤ L (t - s)`.

Since `α` is only defined on `I`, the competitor in the definition of `d_b` is the `C¹` curve
`α ∘ ρ : ℝ → M`, with `ρ` a smooth nondecreasing ramp of `ℝ` onto `[s, t]` (`smoothRamp`); its
length on `[s, t]` is `∫ ρ' μ(α̇ ∘ ρ) ≤ L (t - s)`. -/
theorem IsGeodesicOn.dist_le_of_speed_le (hα : C.IsGeodesicOn α I) {s t : ℝ} (hst : s ≤ t)
    (hI : Icc s t ⊆ I) {L : ℝ} (hL : ∀ τ ∈ Icc s t, μ.toFun (velocity E α τ) ≤ L) :
    μ.dist (α s) (α t) ≤ ENNReal.ofReal (L * (t - s)) := by
  rcases hst.eq_or_lt with rfl | hst'
  · simp
  set ρ := smoothRamp s t
  have hρ := contDiff_smoothRamp s t
  have hρI : ∀ x, ρ x ∈ I := fun x ↦ hI (smoothRamp_mem hst x)
  have hγ := hα.isCkCurve_comp hρ hρI
  have hbound : ∀ x ∈ Icc s t, μ.toFun (velocity E (α ∘ ρ) x) ≤ deriv ρ x * L := by
    intro x _
    have hρ' : 0 ≤ deriv ρ x := (monotone_smoothRamp hst).deriv_nonneg
    rw [hα.velocity_comp hρ hρI x, μ.smul_eq' _ _ hρ']
    refine mul_le_mul_of_nonneg_left ?_ hρ'
    have h := hL (ρ x) (smoothRamp_mem hst x)
    rwa [hα.velocity_eq (hρI x)] at h
  have hlen : μ.length (α ∘ ρ) s t ≤ L * (t - s) := by
    calc μ.length (α ∘ ρ) s t ≤ ∫ x in s..t, deriv ρ x * L :=
          intervalIntegral.integral_mono_on hst ((μ.continuous_velocity hγ).intervalIntegrable _ _)
            (((hρ.continuous_deriv le_rfl).mul continuous_const).intervalIntegrable _ _) hbound
      _ = L * (t - s) := by
          rw [intervalIntegral.integral_mul_const, integral_deriv_smoothRamp hst', mul_comm]
  have h := (μ.dist_le hγ hst).trans (ENNReal.ofReal_le_ofReal hlen)
  simpa [ρ, smoothRamp_right hst'] using h

/-- **The backward distance along a geodesic**: if the reversed curve `τ ↦ α (-τ)` has speed
`≤ L` on `[-t, -s]` (that is, `μ(-α̇) ≤ L` on `[s, t]`), then `d_b(α t, α s) ≤ L (t - s)`. -/
theorem IsGeodesicOn.dist_le_of_speed_le_rev (hα : C.IsGeodesicOn α I) {s t : ℝ} (hst : s ≤ t)
    (hI : Icc s t ⊆ I) {L : ℝ}
    (hL : ∀ τ ∈ Icc s t, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    μ.dist (α t) (α s) ≤ ENNReal.ofReal (L * (t - s)) := by
  have h := hα.comp_neg.dist_le_of_speed_le μ (neg_le_neg hst) (fun τ hτ ↦ by
      simpa using hI ⟨le_neg.1 hτ.2, neg_le.1 hτ.1⟩)
    (L := L) fun τ hτ ↦ by simpa using hL (-τ) ⟨le_neg.1 hτ.2, neg_le.1 hτ.1⟩
  simpa [sub_eq_add_neg, add_comm] using h

end Connection

/-! ### Geodesics of bounded speed have limits at finite ends -/

theorem preimage_neg_Ioo (a b : ℝ) : Neg.neg ⁻¹' Ioo a b = Ioo (-b) (-a) := by
  ext t
  simp only [mem_preimage, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

namespace Connection

variable {C : Connection E M} {α : ℝ → M} {a b L : ℝ} (μ : FinslerLengthStructure E M)

/-- Along a geodesic on `(a, b)` whose speed and backward speed are `≤ L`, the symmetrized
distance satisfies `max (d_b(α s, α t), d_b(α t, α s)) ≤ L |t - s|`. -/
theorem IsGeodesicOn.edist_toFinsler_le (hα : C.IsGeodesicOn α (Ioo a b))
    (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L)
    (hL' : ∀ τ ∈ Ioo a b, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    edist (μ.toFinsler (α s)) (μ.toFinsler (α t)) ≤ ENNReal.ofReal (L * |t - s|) := by
  have key : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      edist (μ.toFinsler (α s)) (μ.toFinsler (α t)) ≤ ENNReal.ofReal (L * (t - s)) := by
    intro s t hs ht hst
    have hI : Icc s t ⊆ Ioo a b := Icc_subset_Ioo hs.1 ht.2
    rw [edist_eq_max_bdist, μ.bdist_toFinsler, μ.bdist_toFinsler]
    exact max_le (hα.dist_le_of_speed_le μ hst hI fun τ hτ ↦ hL τ (hI hτ))
      (hα.dist_le_of_speed_le_rev μ hst hI fun τ hτ ↦ hL' τ (hI hτ))
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.2 hst)]
    exact key s t hs ht hst
  · rw [edist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hts)]
    exact key t s ht hs hts

/-- **A geodesic of bounded speed converges at a finite end** of its interval when `(M, d_b)`
is complete: the points `α t`, `t → b⁻`, form a Cauchy filter for the symmetrized distance, since
`max (d_b(α s, α t), d_b(α t, α s)) ≤ L |t - s|` (*Estructuras*, proof of Proposición 9.2.1). -/
theorem IsGeodesicOn.exists_tendsto_toFinsler [CompleteSpace μ.FinslerSpace]
    (hα : C.IsGeodesicOn α (Ioo a b)) (hab : a < b)
    (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L)
    (hL' : ∀ τ ∈ Ioo a b, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    ∃ p : μ.FinslerSpace, Tendsto (fun t ↦ μ.toFinsler (α t)) (𝓝[<] b) (𝓝 p) := by
  have hf : Cauchy (map (fun t ↦ μ.toFinsler (α t)) (𝓝[<] b)) := by
    rw [EMetric.cauchy_iff]
    refine ⟨NeBot.ne inferInstance, fun ε hε ↦ ?_⟩
    obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hr0 : 0 < r := ENNReal.ofReal_pos.1 hr
    set δ := r / (|L| + 1)
    have hδ : 0 < δ := by positivity
    have hLδ : |L| * δ ≤ r := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg L]
    refine ⟨(fun t ↦ μ.toFinsler (α t)) '' Ioo (max a (b - δ)) b,
      image_mem_map (Ioo_mem_nhdsLT (max_lt hab (by linarith))), ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxI : x ∈ Ioo a b := ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
    have hyI : y ∈ Ioo a b := ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
    have hbx := (le_max_right a (b - δ)).trans_lt hx.1
    have hby := (le_max_right a (b - δ)).trans_lt hy.1
    have hxy : |y - x| ≤ δ := abs_sub_le_iff.2 ⟨by linarith [hy.2], by linarith [hx.2]⟩
    refine ((hα.edist_toFinsler_le μ hL hL' hxI hyI).trans
      (ENNReal.ofReal_le_ofReal ?_)).trans_lt hrε
    calc L * |y - x| ≤ |L| * |y - x| := mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
      _ ≤ |L| * δ := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
      _ ≤ r := hLδ
  exact CompleteSpace.complete hf

variable [CompleteSpace E] [T2Space M]

/-- If `μ` is bounded below, the limit of `α` at `b⁻` for `d_b` is also a limit in `M`, since the
identity `(M, d_b) → M` is continuous (Lema 9.1.8). -/
theorem IsGeodesicOn.exists_tendsto [CompleteSpace μ.FinslerSpace]
    (hb : μ.toFinslerSeminormField.IsBoundedBelow) (hα : C.IsGeodesicOn α (Ioo a b))
    (hab : a < b) (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L)
    (hL' : ∀ τ ∈ Ioo a b, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    ∃ q : M, Tendsto α (𝓝[<] b) (𝓝 q) := by
  obtain ⟨p, hp⟩ := hα.exists_tendsto_toFinsler μ hab hL hL'
  exact ⟨μ.ofFinsler p, ((μ.continuous_ofFinsler hb).tendsto p).comp hp⟩

omit [CompleteSpace E] [T2Space M] in
/-- **A speed bound gives a bound in charts.** If `μ` is bounded below near `q` and `α → q` as
`t → b⁻` with `μ(α̇) ≤ L`, then the velocity of `α` read in a suitable chart around `q` stays
bounded as `t → b⁻`. -/
theorem IsGeodesicOn.exists_chart_norm_deriv_le (hb : μ.toFinslerSeminormField.IsBoundedBelow)
    (hα : C.IsGeodesicOn α (Ioo a b)) (hab : a < b)
    (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L) {q : M}
    (hlim : Tendsto α (𝓝[<] b) (𝓝 q)) :
    ∃ i : atlas E M, q ∈ i.1.source ∧ ∃ K, ∀ᶠ t in 𝓝[<] b, ‖deriv (i.1 ∘ α) t‖ ≤ K := by
  obtain ⟨i, U, hUo, hqU, hUs, c, hc, hbel⟩ := hb q
  refine ⟨i, hUs hqU, c * L, ?_⟩
  filter_upwards [hlim (hUo.mem_nhds hqU), Ioo_mem_nhdsLT hab] with t htU htI
  rw [hα.deriv_chart_eq htI i (hUs htU)]
  refine (hbel (α t) htU _).trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  have h := hL t htI
  rwa [hα.velocity_eq htI] at h

/-! ### Proposición 9.2.1, `1 ⇒ 2` -/

section Extension

variable [CompleteSpace μ.FinslerSpace]

/-- **Proposición 9.2.1 (`1 ⇒ 2`), right end.** Let `M` be a Hausdorff manifold modeled on a Banach
space, with a connection and a Finsler length structure `μ` bounded below, such that `(M, d_b)` is
complete (for the symmetrized distance). A geodesic on `(a, b)`, `b < ∞`, whose speed `μ(α̇)` and
backward speed `μ(-α̇)` are bounded by `L`, extends to a geodesic on some `(a, b')`, `b' > b`. -/
theorem IsGeodesicOn.exists_extend_right_of_complete
    (hb : μ.toFinslerSeminormField.IsBoundedBelow) (hα : C.IsGeodesicOn α (Ioo a b))
    (hab : a < b) (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L)
    (hL' : ∀ τ ∈ Ioo a b, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    ∃ b' > b, ∃ β : ℝ → M, C.IsGeodesicOn β (Ioo a b') ∧ EqOn β α (Ioo a b) := by
  obtain ⟨q, hlim⟩ := hα.exists_tendsto μ hb hab hL hL'
  obtain ⟨i, hq, K, hK⟩ := hα.exists_chart_norm_deriv_le μ hb hab hL hlim
  exact hα.exists_extend hab i hq hlim hK

/-- **Proposición 9.2.1 (`1 ⇒ 2`), left end**: under the same hypotheses, a geodesic on `(a, b)`,
`a > -∞`, extends to a geodesic on some `(a', b)`, `a' < a`. This is the right end for the
reversed geodesic `t ↦ α (-t)`, whose speed and backward speed are those of `α`, exchanged. -/
theorem IsGeodesicOn.exists_extend_left_of_complete
    (hb : μ.toFinslerSeminormField.IsBoundedBelow) (hα : C.IsGeodesicOn α (Ioo a b))
    (hab : a < b) (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L)
    (hL' : ∀ τ ∈ Ioo a b, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    ∃ a' < a, ∃ β : ℝ → M, C.IsGeodesicOn β (Ioo a' b) ∧ EqOn β α (Ioo a b) := by
  have hβ := hα.comp_neg
  rw [preimage_neg_Ioo] at hβ
  have hmem : ∀ τ ∈ Ioo (-b) (-a), -τ ∈ Ioo a b := fun τ hτ ↦
    ⟨lt_neg.1 hτ.2, neg_lt.1 hτ.1⟩
  obtain ⟨b', hb', β, hβ', hEq⟩ := hβ.exists_extend_right_of_complete μ hb (neg_lt_neg hab)
    (L := L) (fun τ hτ ↦ by simpa using hL' (-τ) (hmem τ hτ))
    (fun τ hτ ↦ by simpa using hL (-τ) (hmem τ hτ))
  have hγ := hβ'.comp_neg
  rw [preimage_neg_Ioo, neg_neg] at hγ
  refine ⟨-b', by linarith, fun t ↦ β (-t), hγ, fun t ht ↦ ?_⟩
  simpa using hEq (show -t ∈ Ioo (-b) (-a) from ⟨neg_lt_neg ht.2, neg_lt_neg ht.1⟩)

/-- **Proposición 9.2.1 (`1 ⇒ 2`)** (G. Larotonda, *Estructuras geométricas para las variedades
de Banach*, §9.2). Let `M` be a Hausdorff manifold modeled on a Banach space, with a connection
and a Finsler length structure `μ` bounded below, such that `(M, d_b)` is complete (for the
symmetrized distance). Then a geodesic on a bounded interval `(a, b)` whose speed `μ(α̇)` and
backward speed `μ(-α̇)` are bounded extends to a geodesic on a strictly larger open interval
`(a', b') ⊋ (a, b)`, at both ends. So a maximal geodesic of bounded speed is defined on `ℝ`. -/
theorem IsGeodesicOn.exists_extend_of_complete
    (hb : μ.toFinslerSeminormField.IsBoundedBelow) (hα : C.IsGeodesicOn α (Ioo a b))
    (hab : a < b) (hL : ∀ τ ∈ Ioo a b, μ.toFun (velocity E α τ) ≤ L)
    (hL' : ∀ τ ∈ Ioo a b, μ.toFun (velocity E (fun σ ↦ α (-σ)) (-τ)) ≤ L) :
    ∃ a' < a, ∃ b' > b, ∃ β : ℝ → M, C.IsGeodesicOn β (Ioo a' b') ∧ EqOn β α (Ioo a b) := by
  obtain ⟨a', ha', β₁, hβ₁, hEq₁⟩ := hα.exists_extend_left_of_complete μ hb hab hL hL'
  obtain ⟨b', hb', β₂, hβ₂, hEq₂⟩ := hα.exists_extend_right_of_complete μ hb hab hL hL'
  -- glue `β₁` (left of the midpoint `m`) and `β₂` (right of `m`); both agree with `α` on `(a, b)`
  set m := (a + b) / 2
  have hma : a < m := by simp only [m]; linarith
  have hmb : m < b := by simp only [m]; linarith
  set β : ℝ → M := fun t ↦ if t < m then β₁ t else β₂ t
  have hβ₁' : EqOn β β₁ (Ioo a' b) := fun t ht ↦ by
    by_cases htm : t < m
    · simp [β, htm]
    · have htI : t ∈ Ioo a b := ⟨by linarith [not_lt.1 htm], ht.2⟩
      simp only [β, htm, ↓reduceIte]
      rw [hEq₂ htI, hEq₁ htI]
  have hβ₂' : EqOn β β₂ (Ioo a b') := fun t ht ↦ by
    by_cases htm : t < m
    · have htI : t ∈ Ioo a b := ⟨ht.1, by linarith⟩
      simp only [β, htm, ↓reduceIte]
      rw [hEq₁ htI, hEq₂ htI]
    · simp [β, htm]
  refine ⟨a', ha', b', hb', β, isGeodesicOn_of_local isOpen_Ioo fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · by_cases htb : t < b
    · exact ⟨β₁, Ioo a' b, ⟨ht.1, htb⟩, hβ₁, hβ₁'⟩
    · exact ⟨β₂, Ioo a b', ⟨by linarith [not_lt.1 htb], ht.2⟩, hβ₂, hβ₂'⟩
  · rw [hβ₁' ⟨ha'.trans ht.1, ht.2⟩, hEq₁ ht]

end Extension

end Connection

end LCManifolds
