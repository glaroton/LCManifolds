/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.MetricGeometry.HopfRinow

/-!
# Short geodesics and geodesic spaces

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, §8.1.2
(Definición 8.1.11, Observación 8.1.13) and Teorema 8.2.3.

* `IsShortGeodesic γ L` (Definición 8.1.11): `d(γ s, γ t) = L |s − t|` on `[0, 1]`; its length is
  `L` (`IsShortGeodesic.eVariationOn_eq`).
* `RectPath.edist_eq_of_length_eq` (Observación 8.1.13): if a curve realizes the distance between
  its end points, so does each of its sub-arcs.
* `IsGeodesicSpace`: an interior space in which any two points are joined by a short geodesic;
  `IsInterior.isGeodesicSpace` (Teorema 8.2.3): a complete, locally compact interior metric space
  is geodesic.
-/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace LocallyConvex.Manifolds

variable {X : Type*} [PseudoMetricSpace X]

/-- **Short geodesics** (Definición 8.1.11): `γ` is a short geodesic of length `L` on `[0, 1]` if
`d(γ s, γ t) = L |s − t|` for all `s, t ∈ [0, 1]`. -/
def IsShortGeodesic (γ : ℝ → X) (L : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) = L * |s - t|

/-- A short geodesic is continuous on `[0, 1]`. -/
theorem IsShortGeodesic.continuousOn {γ : ℝ → X} {L : ℝ} (h : IsShortGeodesic γ L) :
    ContinuousOn γ (Icc 0 1) := by
  have hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) ≤ |L| * dist s t := by
    intro s hs t ht
    rw [h s hs t ht, Real.dist_eq]
    exact mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
  exact (LipschitzOnWith.of_dist_le_mul (K := ⟨|L|, abs_nonneg L⟩)
    fun s hs t ht ↦ hL s hs t ht).continuousOn

/-- The length of a short geodesic of length `L` is `L`. -/
theorem IsShortGeodesic.eVariationOn_eq {γ : ℝ → X} {L : ℝ} (h : IsShortGeodesic γ L)
    (hL : 0 ≤ L) : eVariationOn γ (Icc 0 1) = ENNReal.ofReal L := by
  refine le_antisymm ?_ ?_
  · -- `γ` is `L`-Lipschitz, so its length is at most `L`
    have hlip : LipschitzOnWith ⟨L, hL⟩ γ (Icc 0 1) :=
      LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ by
        rw [h s hs t ht, Real.dist_eq]; rfl
    have := hlip.comp_eVariationOn_le (g := id) (s := Icc (0 : ℝ) 1) (mapsTo_id _)
    rw [Function.comp_id, eVariationOn_id_Icc] at this
    refine this.trans_eq ?_
    rw [sub_zero, ENNReal.ofReal_one, mul_one, ENNReal.ofReal, Real.toNNReal_of_nonneg hL]
    rfl
  · have := eVariationOn.edist_le γ (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    rw [edist_dist, h 0 (left_mem_Icc.2 zero_le_one) 1 (right_mem_Icc.2 zero_le_one)] at this
    simpa using this

/-- **Observación 8.1.13: sub-arcs of curves that realize the distance realize the distance.** -/
theorem RectPath.edist_eq_of_length_eq {x y : X} (p : RectPath x y) (hp : p.length = edist x y)
    {s t : ℝ} (has : p.a ≤ s) (hst : s ≤ t) (htb : t ≤ p.b) :
    eVariationOn p.toFun (Icc s t) = edist (p.toFun s) (p.toFun t) := by
  set f := p.toFun
  have hsplit1 := eVariationOn.Icc_add_Icc f (s := univ) has hst (mem_univ _)
  have hsplit2 := eVariationOn.Icc_add_Icc f (s := univ) (has.trans hst) htb (mem_univ _)
  simp only [univ_inter] at hsplit1 hsplit2
  have hL : eVariationOn f (Icc p.a p.b) = edist x y := hp
  have hfin : edist x y ≠ ⊤ := edist_ne_top x y
  set V1 := eVariationOn f (Icc p.a s)
  set V2 := eVariationOn f (Icc s t)
  set V3 := eVariationOn f (Icc t p.b)
  have hsum : V1 + V2 + V3 = edist x y := by rw [hsplit1, hsplit2, hL]
  have hV1 : V1 ≠ ⊤ := fun h ↦ hfin (by rw [← hsum, h]; simp)
  have hV2 : V2 ≠ ⊤ := fun h ↦ hfin (by rw [← hsum, h]; simp)
  have hV3 : V3 ≠ ⊤ := fun h ↦ hfin (by rw [← hsum, h]; simp)
  have e1 : edist x (f s) ≤ V1 := by
    rw [← p.source]; exact eVariationOn.edist_le f ⟨le_rfl, has⟩ ⟨has, le_rfl⟩
  have e2 : edist (f s) (f t) ≤ V2 := eVariationOn.edist_le f ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
  have e3 : edist (f t) y ≤ V3 := by
    rw [← p.target]; exact eVariationOn.edist_le f ⟨le_rfl, htb⟩ ⟨htb, le_rfl⟩
  have htri : edist x y ≤ edist x (f s) + edist (f s) (f t) + edist (f t) y :=
    edist_triangle4 _ _ _ _
  refine le_antisymm ?_ e2
  -- pass to real numbers
  have r1 := ENNReal.toReal_mono hV1 e1
  have r2 := ENNReal.toReal_mono hV2 e2
  have r3 := ENNReal.toReal_mono hV3 e3
  have rsum : V1.toReal + V2.toReal + V3.toReal = (edist x y).toReal := by
    rw [← hsum, ENNReal.toReal_add (by simpa using ⟨hV1, hV2⟩) hV3, ENNReal.toReal_add hV1 hV2]
  have rtri := ENNReal.toReal_mono (by simp [edist_ne_top]) htri
  rw [ENNReal.toReal_add (by simp [edist_ne_top]) (edist_ne_top _ _),
    ENNReal.toReal_add (edist_ne_top _ _) (edist_ne_top _ _)] at rtri
  rw [← ENNReal.ofReal_toReal hV2, ← ENNReal.ofReal_toReal (edist_ne_top (f s) (f t))]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- A **geodesic space** (*Estructuras*, Definición 8.1.11): an interior metric space in which any
two points are joined by a short geodesic. -/
def IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  IsInterior X ∧ ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧ IsShortGeodesic γ (dist x y)

/-- **A curve realizing the distance, normalized by arc length, is a short geodesic.** -/
theorem RectPath.exists_isShortGeodesic {x y : X} (p : RectPath x y)
    (hp : p.length = edist x y) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧ IsShortGeodesic γ (dist x y) := by
  have hfin : p.length ≠ ⊤ := by rw [hp]; exact edist_ne_top x y
  obtain ⟨η, h0, h1, hη⟩ := p.exists_lipschitz_reparam hfin
  have hL : p.length.toReal = dist x y := by rw [hp, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hL] at hη
  refine ⟨η, h0, h1, fun s hs t ht ↦ le_antisymm (hη s hs t ht) ?_⟩
  -- the reverse inequality, from the triangle inequality through `η s` and `η t`
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm (η s), abs_sub_comm]
    exact this t ht s hs (le_of_not_ge hst)
  have e1 := hη 0 (left_mem_Icc.2 zero_le_one) s hs
  have e3 := hη t ht 1 (right_mem_Icc.2 zero_le_one)
  rw [h0] at e1
  rw [h1] at e3
  have htri : dist x y ≤ dist x (η s) + dist (η s) (η t) + dist (η t) y :=
    dist_triangle4 _ _ _ _
  rw [abs_of_nonpos (by linarith [hs.1] : (0 : ℝ) - s ≤ 0)] at e1
  rw [abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0)] at e3
  rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- **Teorema 8.2.3: a complete, locally compact interior metric space is geodesic.** -/
theorem IsInterior.isGeodesicSpace {X : Type*} [MetricSpace X] [CompleteSpace X]
    [WeaklyLocallyCompactSpace X] (h : IsInterior X) : IsGeodesicSpace X :=
  ⟨h, fun x y ↦ by
    obtain ⟨p, hp⟩ := h.exists_rectPath_length_eq x y
    exact p.exists_isShortGeodesic hp⟩

end LocallyConvex.Manifolds
