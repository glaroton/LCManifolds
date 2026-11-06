/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.MetricGeometry.LengthMetric
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The metric Hopf–Rinow theorem

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 8,
§8.2 (which follows M. Gromov, *Metric structures for Riemannian and non-Riemannian spaces*).

Let `(X, d)` be an interior metric space (`IsInterior X`, see `LengthMetric.lean`): the distance
between two points is the infimum of the lengths of the continuous curves joining them. The
**metric Hopf–Rinow theorem** (Teorema 8.2.3, due in this generality to Cohn-Vossen) says:

1. if `X` is complete and the closed balls `B̄_r(x)` are compact for all `0 < r < ρ`, then
   `B̄_ρ(x)` is compact (`IsInterior.isCompact_closedBall_of_lt`);
2. if moreover `X` is locally compact, then every closed ball is compact
   (`IsInterior.isCompact_closedBall`, `IsInterior.properSpace`), and `X` is **geodesic**: any
   two points are joined by a shortest curve, of length equal to their distance
   (`IsInterior.exists_rectPath_length_eq`).

Conversely, a space whose closed balls are all compact is complete (Observación 8.2.4,
`completeSpace_of_isCompact_closedBall`).

## Main results

* `IsInterior.exists_dist_le_add`, `IsInterior.exists_approx_intermediate`: approximate
  intermediate points, generalizing the approximate midpoints of
  `IsInterior.exists_approx_midpoint`;
* `RectPath.exists_lipschitz_reparam`: a curve of finite length `ℓ` can be reparametrized on
  `[0, 1]` as an `ℓ`-Lipschitz curve (Observación 8.1.5, Corolario 8.1.6);
* `IsInterior.isCompact_closedBall_of_lt`, `IsInterior.isCompact_closedBall`,
  `IsInterior.properSpace`: Teorema 8.2.3, item 1 and the first half of item 2;
* `IsInterior.exists_rectPath_length_eq_of_isCompact`, `IsInterior.exists_rectPath_length_eq`:
  existence of shortest curves, the second half of Teorema 8.2.3, item 2;
* `completeSpace_of_isCompact_closedBall`: Observación 8.2.4.

## Implementation notes

* Local compactness enters only through `WeaklyLocallyCompactSpace X` (every point has a compact
  neighborhood), which `LocallyCompactSpace X` implies.
* Item 1 is proved through total boundedness rather than with the diagonal argument of the book:
  every point of `B̄_ρ(x)` is `3δ`-close to the compact ball `B̄_{ρ-δ}(x)`, by the approximate
  intermediate points.
* The enlargement step of item 2 uses a Lebesgue number of a finite cover of the compact ball
  `B̄_ρ(x)` by balls with compact closure, instead of the boundary sphere `∂B_ρ(x)`.
* For the existence of shortest curves the book uses the Arzelà–Ascoli theorem and the lower
  semicontinuity of the length. We avoid both: the reparametrized almost minimizing curves
  `ηₙ : [0, 1] → B̄_{d+1}(x)` are `(d + 1/(n+1))`-Lipschitz, so a cluster point `γ` of `(ηₙ)` in
  the product (pointwise) topology, which exists by Tychonoff's theorem, is `d`-Lipschitz, hence
  continuous and of length `≤ d`. This part needs `MetricSpace X` (to identify `γ(0)` with `x`
  and `γ(1)` with `y`); the rest holds in pseudometric spaces.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

noncomputable section

namespace LocallyConvex.Manifolds

section Pseudo

variable {X : Type*} [PseudoMetricSpace X]

/-- **Approximate intermediate points at prescribed distances.** In an interior space, if
`a, b ≥ 0` and `a + b = d(x, y)`, then for every `ε > 0` there is `z` with `d(x, z) ≤ a + ε` and
`d(z, y) ≤ b + ε`. Take a curve of length `< d(x, y) + ε` and its point at arc length `a`, which
exists by the continuity of the arc length and the intermediate value theorem. -/
theorem IsInterior.exists_dist_le_add (h : IsInterior X) (x y : X) {a b ε : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = dist x y) (hε : 0 < ε) :
    ∃ z, dist x z ≤ a + ε ∧ dist z y ≤ b + ε := by
  have hlt : edist x y < ENNReal.ofReal (dist x y + ε) := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by positivity⟩
  obtain ⟨p, hp⟩ := h.exists_rectPath hlt
  set L := p.length
  have hLtop : L ≠ ⊤ := ne_top_of_lt hp
  set s := Icc p.a p.b
  have ha' : p.a ∈ s := left_mem_Icc.2 p.le
  have hb' : p.b ∈ s := right_mem_Icc.2 p.le
  have hbv : BoundedVariationOn p.toFun s := hLtop
  set F := variationOnFromTo p.toFun s p.a
  have hcont : ContinuousOn F s := fun t ht ↦
    (hbv.continuousWithinAt_variationOnFromTo_iff ha' ht).mpr (p.continuousOn t ht)
  have hFa : F p.a = 0 := variationOnFromTo.self _ _ _
  have hFb : F p.b = L.toReal := by
    simp only [F, variationOnFromTo.eq_of_le _ _ p.le, inter_self, L, RectPath.length, s]
  have hdL : dist x y ≤ L.toReal := by
    have := p.edist_le_length
    rw [edist_dist] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hLtop).mp this
  obtain ⟨t, ht, hFt⟩ : ∃ t ∈ s, F t = a := by
    have := intermediate_value_Icc p.le hcont
    rw [hFa, hFb] at this
    exact this ⟨ha, by linarith⟩
  have hLlt : L.toReal < dist x y + ε := ENNReal.toReal_lt_of_lt_ofReal hp
  have hsub : ∀ {u v : ℝ}, u ∈ s → v ∈ s → u ≤ v →
      dist (p.toFun u) (p.toFun v) ≤ variationOnFromTo p.toFun s u v := by
    intro u v hu hv huv
    rw [variationOnFromTo.eq_of_le _ _ huv, dist_edist]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top hLtop
      (eVariationOn.mono _ inter_subset_left)) ?_
    exact eVariationOn.edist_le _ ⟨hu, le_rfl, huv⟩ ⟨hv, huv, le_rfl⟩
  have hadd := variationOnFromTo.add hbv.locallyBoundedVariationOn ha' ht hb'
  refine ⟨p.toFun t, ?_, ?_⟩
  · have := hsub ha' ht ht.1
    rw [p.source] at this
    change dist x (p.toFun t) ≤ F t at this
    linarith
  · have := hsub ht hb' ht.2
    rw [p.target] at this
    have hFb' : variationOnFromTo p.toFun s p.a p.b = L.toReal := hFb
    change F t + variationOnFromTo p.toFun s t p.b = _ at hadd
    linarith

/-- **Approximate intermediate points** (generalizing *Estructuras*, Problema 8.III, that is
`IsInterior.exists_approx_midpoint`, which is the case `μ = 1/2`): in an interior space, for
`μ ∈ [0, 1]` and `ε > 0` there is `z` with `d(x, z) ≤ μ d(x, y) + ε` and
`d(z, y) ≤ (1 - μ) d(x, y) + ε`. -/
theorem IsInterior.exists_approx_intermediate (h : IsInterior X) (x y : X) {μ ε : ℝ}
    (hμ : μ ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ z, dist x z ≤ μ * dist x y + ε ∧ dist z y ≤ (1 - μ) * dist x y + ε :=
  h.exists_dist_le_add x y (mul_nonneg hμ.1 dist_nonneg)
    (mul_nonneg (sub_nonneg.2 hμ.2) dist_nonneg) (by ring) hε

/-- A point at distance `≤ r + η` from `x` is `3η`-close to the ball `B̄_r(x)`, if `η ≤ r`. -/
theorem IsInterior.exists_mem_closedBall_near (h : IsInterior X) {x z : X} {r η : ℝ}
    (hη : 0 < η) (hηr : η ≤ r) (hz : dist z x ≤ r + η) :
    ∃ w ∈ closedBall x r, dist w z ≤ 3 * η := by
  by_cases hzr : dist z x ≤ r
  · exact ⟨z, hzr, by simp; linarith⟩
  replace hzr := not_le.mp hzr
  obtain ⟨w, hw1, hw2⟩ := h.exists_dist_le_add x z (a := r - (dist z x - r))
    (b := 2 * (dist z x - r)) (ε := dist z x - r) (by linarith) (by linarith)
    (by rw [dist_comm]; ring) (by linarith)
  exact ⟨w, by rw [mem_closedBall, dist_comm]; linarith, by linarith⟩

/-- **Hopf–Rinow, item 1** (*Estructuras*, Teorema 8.2.3, 1): in a complete interior space, if
the closed balls `B̄_r(x)` are compact for all `0 < r < ρ`, then so is `B̄_ρ(x)`. It is totally
bounded: every point of `B̄_ρ(x)` is `3δ`-close to the compact ball `B̄_{ρ-δ}(x)`. -/
theorem IsInterior.isCompact_closedBall_of_lt [CompleteSpace X] (h : IsInterior X) (x : X)
    {ρ : ℝ} (hρ : 0 < ρ) (hK : ∀ r, 0 < r → r < ρ → IsCompact (closedBall x r)) :
    IsCompact (closedBall x ρ) := by
  refine isCompact_iff_totallyBounded_isComplete.mpr ⟨?_, isClosed_closedBall.isComplete⟩
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ := min (ε / 4) (ρ / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδρ : δ ≤ ρ / 2 := min_le_right _ _
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.mp
    (hK (ρ - δ) (by linarith) (by linarith)).totallyBounded δ hδ0
  refine ⟨t, ht, fun z hz ↦ ?_⟩
  obtain ⟨w, hw, hwz⟩ := h.exists_mem_closedBall_near hδ0 (by linarith)
    (show dist z x ≤ ρ - δ + δ by rw [sub_add_cancel]; exact hz)
  obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.mp (hcov hw)
  refine mem_iUnion₂.mpr ⟨y, hy, ?_⟩
  rw [mem_ball] at hwy ⊢
  calc dist z y ≤ dist z w + dist w y := dist_triangle _ _ _
    _ < 3 * δ + δ := add_lt_add_of_le_of_lt (by rwa [dist_comm]) hwy
    _ ≤ ε := by linarith

/-- In a (weakly) locally compact interior space, a compact closed ball `B̄_ρ(x)` with `ρ > 0`
is contained in a larger compact closed ball. Cover `B̄_ρ(x)` by finitely many balls with compact
closure and take a Lebesgue number `δ` of the cover; the points at distance `≤ ρ + η` from `x`,
with `3η < δ`, are close to `B̄_ρ(x)`, hence in the union of the closures. -/
theorem IsInterior.exists_isCompact_closedBall_gt [WeaklyLocallyCompactSpace X]
    (h : IsInterior X) (x : X) {ρ : ℝ} (hρ : 0 < ρ) (hK : IsCompact (closedBall x ρ)) :
    ∃ ρ' > ρ, IsCompact (closedBall x ρ') := by
  choose r hr0 hrc using fun y : X ↦ exists_isCompact_closedBall y
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y ↦ ball y (r y)) (fun _ ↦ isOpen_ball)
    (fun z _ ↦ mem_iUnion.mpr ⟨z, mem_ball_self (hr0 z)⟩)
  have ht' : closedBall x ρ ⊆ ⋃ i : (t : Set X), ball i.1 (r i.1) := fun z hz ↦ by
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun _ ↦ isOpen_ball) ht'
  set η := min (δ / 4) ρ
  have hη0 : 0 < η := lt_min (by positivity) hρ
  have hηρ : η ≤ ρ := min_le_right _ _
  have hηδ : η ≤ δ / 4 := min_le_left _ _
  refine ⟨ρ + η, by linarith, ?_⟩
  refine (t.isCompact_biUnion fun i _ ↦ hrc i).of_isClosed_subset isClosed_closedBall
    fun z hz ↦ ?_
  obtain ⟨w, hw, hwz⟩ := h.exists_mem_closedBall_near hη0 hηρ hz
  obtain ⟨⟨i, hi⟩, hsub⟩ := hleb w hw
  refine mem_iUnion₂.mpr ⟨i, hi, ball_subset_closedBall (hsub ?_)⟩
  rw [mem_ball, dist_comm]
  linarith

/-- **Hopf–Rinow, item 2, compactness of balls** (*Estructuras*, Teorema 8.2.3, 2): in a
complete, (weakly) locally compact interior space, every closed ball is compact. The supremum `ρ`
of the radii of the compact balls centered at `x` is positive by local compactness, `B̄_ρ(x)` is
compact by item 1, and can be enlarged, so `ρ = ∞`. -/
theorem IsInterior.isCompact_closedBall [CompleteSpace X] [WeaklyLocallyCompactSpace X]
    (h : IsInterior X) (x : X) (R : ℝ) : IsCompact (closedBall x R) := by
  by_contra hR
  set S := {r : ℝ | IsCompact (closedBall x r)}
  have hS : ∀ r ∈ S, r < R := fun r hr ↦ by
    by_contra hle
    exact hR (hr.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall
      (not_lt.mp hle)))
  have hbdd : BddAbove S := ⟨R, fun r hr ↦ (hS r hr).le⟩
  obtain ⟨r₀, hr₀, hr₀c⟩ := exists_isCompact_closedBall x
  set ρ := sSup S
  have hρ : r₀ ≤ ρ := le_csSup hbdd hr₀c
  have hρS : ρ ∈ S := by
    refine h.isCompact_closedBall_of_lt x (by linarith) fun r _ hr ↦ ?_
    obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup ⟨r₀, hr₀c⟩ hr
    exact hs.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hrs.le)
  obtain ⟨ρ', hρ', hρ'c⟩ := h.exists_isCompact_closedBall_gt x (by linarith) hρS
  exact absurd (le_csSup hbdd hρ'c) (not_le.mpr hρ')

/-- **Normal reparametrization** (*Estructuras*, Observación 8.1.5 and Corolario 8.1.6): a curve
of finite length `ℓ` from `x` to `y` can be reparametrized on `[0, 1]` (through its arc length,
by the intermediate value theorem) as a curve `η` with `η 0 = x`, `η 1 = y` and
`d(η u, η v) ≤ ℓ |u - v|`. Only the values on `[0, 1]` matter. -/
theorem RectPath.exists_lipschitz_reparam {x y : X} (p : RectPath x y) (hp : p.length ≠ ⊤) :
    ∃ η : ℝ → X, η 0 = x ∧ η 1 = y ∧
      ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, dist (η u) (η v) ≤ p.length.toReal * |u - v| := by
  set L := p.length
  set s := Icc p.a p.b
  have ha' : p.a ∈ s := left_mem_Icc.2 p.le
  have hb' : p.b ∈ s := right_mem_Icc.2 p.le
  have hbv : BoundedVariationOn p.toFun s := hp
  set F := variationOnFromTo p.toFun s p.a
  have hcont : ContinuousOn F s := fun t ht ↦
    (hbv.continuousWithinAt_variationOnFromTo_iff ha' ht).mpr (p.continuousOn t ht)
  have hFa : F p.a = 0 := variationOnFromTo.self _ _ _
  have hFb : F p.b = L.toReal := by
    simp only [F, variationOnFromTo.eq_of_le _ _ p.le, inter_self, L, RectPath.length, s]
  have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  have hsub : ∀ {u v : ℝ}, u ∈ s → v ∈ s → u ≤ v →
      dist (p.toFun u) (p.toFun v) ≤ F v - F u := by
    intro u v hu hv huv
    have hadd := variationOnFromTo.add hbv.locallyBoundedVariationOn ha' hu hv
    change F u + _ = F v at hadd
    rw [← hadd, add_sub_cancel_left, variationOnFromTo.eq_of_le _ _ huv, dist_edist]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top hp
      (eVariationOn.mono _ inter_subset_left)) ?_
    exact eVariationOn.edist_le _ ⟨hu, le_rfl, huv⟩ ⟨hv, huv, le_rfl⟩
  have hdist : ∀ {u v : ℝ}, u ∈ s → v ∈ s → dist (p.toFun u) (p.toFun v) ≤ |F u - F v| := by
    intro u v hu hv
    rcases le_total u v with huv | hvu
    · exact (hsub hu hv huv).trans (by rw [abs_sub_comm]; exact le_abs_self _)
    · rw [dist_comm]; exact (hsub hv hu hvu).trans (le_abs_self _)
  have hex : ∀ u ∈ Icc (0 : ℝ) 1, ∃ t ∈ s, F t = u * L.toReal := by
    intro u hu
    have := intermediate_value_Icc p.le hcont
    rw [hFa, hFb] at this
    exact this ⟨mul_nonneg hu.1 hL0, mul_le_of_le_one_left hL0 hu.2⟩
  choose! τ hτs hτF using hex
  set σ : ℝ → ℝ := fun u ↦ if u = 0 then p.a else if u = 1 then p.b else τ u
  have hσ : ∀ u ∈ Icc (0 : ℝ) 1, σ u ∈ s ∧ F (σ u) = u * L.toReal := by
    intro u hu
    by_cases h0 : u = 0
    · simp [σ, h0, ha', hFa]
    by_cases h1 : u = 1
    · simp [σ, h1, hb', hFb]
    simp only [σ, h0, h1, ite_false]
    exact ⟨hτs u hu, hτF u hu⟩
  refine ⟨fun u ↦ p.toFun (σ u), by simp [σ, p.source], by simp [σ, p.target], ?_⟩
  intro u hu v hv
  refine (hdist (hσ u hu).1 (hσ v hv).1).trans_eq ?_
  rw [(hσ u hu).2, (hσ v hv).2, ← sub_mul, abs_mul, abs_of_nonneg hL0, mul_comm]

/-- A complete, (weakly) locally compact interior space is proper (*Estructuras*,
Teorema 8.2.3, 2). -/
theorem IsInterior.properSpace [CompleteSpace X] [WeaklyLocallyCompactSpace X]
    (h : IsInterior X) : ProperSpace X :=
  ⟨h.isCompact_closedBall⟩

end Pseudo

/-- **Existence of shortest curves.** In an interior metric space, if the closed ball
`B̄_{d(x,y)+1}(x)` is compact, there is a continuous curve from `x` to `y` whose length is
`d(x, y)`. The `(d + 1/(n+1))`-Lipschitz normal reparametrizations of curves of length
`< d + 1/(n+1)` take values in that ball; a cluster point of them in the pointwise topology
(Tychonoff) is `d`-Lipschitz on `[0, 1]`, hence it is a curve of length `≤ d`. -/
theorem IsInterior.exists_rectPath_length_eq_of_isCompact {X : Type*} [MetricSpace X]
    (h : IsInterior X) (x y : X) (hK : IsCompact (closedBall x (dist x y + 1))) :
    ∃ p : RectPath x y, p.length = edist x y := by
  set d := dist x y with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hpath : ∀ n : ℕ, ∃ η : ℝ → X, η 0 = x ∧ η 1 = y ∧ ∀ u ∈ Icc (0 : ℝ) 1,
      ∀ v ∈ Icc (0 : ℝ) 1, dist (η u) (η v) ≤ (d + 1 / (n + 1)) * |u - v| := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨p, hp⟩ := h.exists_rectPath (x := x) (y := y)
      (ε := ENNReal.ofReal (d + 1 / (n + 1))) (by
        rw [edist_dist]
        exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by positivity⟩)
    obtain ⟨η, h0, h1, hη⟩ := p.exists_lipschitz_reparam (ne_top_of_lt hp)
    have hL : p.length.toReal ≤ d + 1 / (n + 1) := (ENNReal.toReal_lt_of_lt_ofReal hp).le
    exact ⟨η, h0, h1, fun u hu v hv ↦
      (hη u hu v hv).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))⟩
  choose η hη0 hη1 hηL using hpath
  have habs : ∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → |u - v| ≤ 1 :=
    fun hu hv ↦ abs_le.mpr ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  have hinv : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n ↦
    (div_le_one (by positivity)).mpr (by linarith [n.cast_nonneg (α := ℝ)])
  set I := Icc (0 : ℝ) 1
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  have hmem : ∀ n (t : I), η n t ∈ closedBall x (d + 1) := by
    intro n t
    rw [mem_closedBall, ← hη0 n]
    calc dist (η n t) (η n 0) ≤ (d + 1 / (n + 1)) * |(t : ℝ) - 0| := hηL n t t.2 0 h0I
      _ ≤ (d + 1 / (n + 1)) * 1 :=
        mul_le_mul_of_nonneg_left (habs t.2 h0I) (by positivity)
      _ ≤ d + 1 := by linarith [hinv n]
  set u : ℕ → (I → X) := fun n t ↦ η n t
  obtain ⟨γ, -, hγ⟩ := (isCompact_univ_pi fun _ : I ↦ hK).exists_mapClusterPt (f := atTop)
    (u := u) (le_principal_iff.mpr <| mem_map.mpr <| univ_mem' fun n ↦
      mem_univ_pi.mpr fun t ↦ hmem n t)
  rw [mapClusterPt_iff_frequently] at hγ
  have happrox : ∀ (s t : I) (ε : ℝ), 0 < ε → ∀ N : ℕ,
      ∃ n ≥ N, dist (η n s) (γ s) < ε ∧ dist (η n t) (γ t) < ε := by
    intro s t ε hε N
    have h1 : (fun f : I → X ↦ f s) ⁻¹' ball (γ s) ε ∈ 𝓝 γ :=
      (continuous_apply s).continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)
    have h2 : (fun f : I → X ↦ f t) ⁻¹' ball (γ t) ε ∈ 𝓝 γ :=
      (continuous_apply t).continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)
    have hnhds : {f : I → X | dist (f s) (γ s) < ε ∧ dist (f t) (γ t) < ε} ∈ 𝓝 γ :=
      inter_mem h1 h2
    obtain ⟨n, hn, hN⟩ := ((hγ _ hnhds).and_eventually (eventually_ge_atTop N)).exists
    exact ⟨n, hN, hn⟩
  have hlip : ∀ s t : I, dist (γ s) (γ t) ≤ d * |(s : ℝ) - t| := by
    intro s t
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨n, hnN, hs, ht⟩ := happrox s t (ε / 4) (by positivity) N
    have hnN' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnN 1)
    have hc : 1 / ((n : ℝ) + 1) * |(s : ℝ) - t| ≤ 1 / ((n : ℝ) + 1) :=
      mul_le_of_le_one_right (by positivity) (habs s.2 t.2)
    have hst := hηL n s s.2 t t.2
    rw [add_mul] at hst
    calc dist (γ s) (γ t) ≤ dist (γ s) (η n s) + dist (η n s) (η n t) + dist (η n t) (γ t) :=
          dist_triangle4 _ _ _ _
      _ < d * |(s : ℝ) - t| + ε := by rw [dist_comm] at hs; linarith
  have hend : ∀ (t : I) (z : X), (∀ n, η n t = z) → γ t = z := by
    intro t z hz
    refine (eq_of_forall_dist_le fun ε hε ↦ ?_).symm
    obtain ⟨n, -, hn, -⟩ := happrox t t ε hε 0
    rw [hz n] at hn
    exact hn.le
  set f : ℝ → X := fun t ↦ if ht : t ∈ I then γ ⟨t, ht⟩ else x
  have hf : LipschitzOnWith (Real.toNNReal d) f I := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
    simp only [f, hs, ht, ↓reduceDIte, Real.coe_toNNReal _ hd0, Real.dist_eq]
    exact hlip ⟨s, hs⟩ ⟨t, ht⟩
  let p : RectPath x y :=
    { toFun := f
      a := 0
      b := 1
      le := zero_le_one
      continuousOn := hf.continuousOn
      source := by simp only [f, h0I, ↓reduceDIte]; exact hend ⟨0, h0I⟩ x hη0
      target := by simp only [f, h1I, ↓reduceDIte]; exact hend ⟨1, h1I⟩ y hη1 }
  refine ⟨p, le_antisymm ?_ p.edist_le_length⟩
  have := hf.comp_eVariationOn_le (g := id) (s := I) (mapsTo_id _)
  change eVariationOn f I ≤ _
  rw [Function.comp_id, eVariationOn_id_Icc] at this
  refine this.trans_eq ?_
  rw [sub_zero, ENNReal.ofReal_one, mul_one, edist_dist]
  rfl

/-- **Metric Hopf–Rinow theorem** (*Estructuras*, Teorema 8.2.3, 2): a complete, (weakly)
locally compact interior metric space is geodesic: any two points `x, y` are joined by a
continuous curve of length `d(x, y)`. -/
theorem IsInterior.exists_rectPath_length_eq {X : Type*} [MetricSpace X] [CompleteSpace X]
    [WeaklyLocallyCompactSpace X] (h : IsInterior X) (x y : X) :
    ∃ p : RectPath x y, p.length = edist x y :=
  h.exists_rectPath_length_eq_of_isCompact x y (h.isCompact_closedBall x _)

/-- A metric space whose closed balls are all compact is complete (*Estructuras*,
Observación 8.2.4): it is a proper space, and Mathlib's `complete_of_proper` applies. -/
theorem completeSpace_of_isCompact_closedBall {X : Type*} [PseudoMetricSpace X]
    (h : ∀ (x : X) (r : ℝ), IsCompact (closedBall x r)) : CompleteSpace X :=
  haveI : ProperSpace X := ⟨h⟩
  inferInstance

end LocallyConvex.Manifolds
