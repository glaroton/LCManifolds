/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.IntermediateValue

/-!
# The rectifiable distance and interior metric spaces

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 8,
§8.1 (which follows M. Gromov, *Metric structures for Riemannian and non-Riemannian spaces*).

Let `(X, d)` be a pseudo-(extended) metric space. The **length** of a continuous curve
`γ : [a, b] → X` is the supremum over the partitions `a = t₀ ≤ ⋯ ≤ tₙ₊₁ = b` of
`Σ d(γ tᵢ, γ tᵢ₊₁)`; in Mathlib this is `eVariationOn γ (Icc a b)`, with values in `[0, ∞]`.
The basic properties listed in *Estructuras*, §8.1, are in Mathlib:

* refining a partition increases the sums, and `ℓ(γ) = 0` iff `γ` is constant
  (`eVariationOn.eq_zero_iff`);
* additivity under concatenation (`eVariationOn.Icc_add_Icc`);
* invariance under monotone reparametrizations (Observación 8.1.1,
  `eVariationOn.comp_eq_of_monotoneOn`);
* lower semicontinuity under uniform convergence (Proposición 8.1.3,
  `eVariationOn.lowerSemicontinuous_uniformOn`);
* continuity of the arc length `t ↦ ℓ(γ|[a, t])` (Lema 8.1.4,
  `variationOnFromTo.continuousAt_variationOnFromTo_iff`).

In this file:

* `RectPath x y`: continuous curves `γ : [a, b] → X` from `x` to `y`, with `RectPath.concat` and
  `RectPath.reverse`;
* `lengthDist`: the **rectifiable distance** `d_ℓ(x, y) = inf ℓ(γ)` over continuous curves from
  `x` to `y` (`∞` if there is none). It is a pseudo-(extended) metric: `lengthDist_self`,
  `lengthDist_comm`, `lengthDist_triangle`; and `d ≤ d_ℓ` (`edist_le_lengthDist`, Observación
  8.1.7);
* `LengthMetric X`: a copy of `X` with the distance `d_ℓ`. The identity `LengthMetric X → X` is
  `1`-Lipschitz, so the topology of `d_ℓ` is finer (`continuous_ofLength`); the two topologies
  agree iff every point can be joined to all nearby points by curves of small length
  (`continuous_toLength_iff`, Lema 8.1.8);
* `IsInterior`: `(X, d)` is an **interior metric space** (a length space) if `d = d_ℓ`, and it
  has approximate midpoints (`IsInterior.exists_approx_midpoint`, Problema 8.III).
-/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace LCManifolds

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Continuous curves between two points -/

/-- A continuous curve `γ : [a, b] → X` from `x` to `y`. Its length may be infinite. -/
structure RectPath (x y : X) where
  /-- The curve (only its values on `[a, b]` matter). -/
  toFun : ℝ → X
  /-- The initial time. -/
  a : ℝ
  /-- The final time. -/
  b : ℝ
  le : a ≤ b
  continuousOn : ContinuousOn toFun (Icc a b)
  source : toFun a = x
  target : toFun b = y

namespace RectPath

variable {x y z : X}

/-- The length of a curve: the supremum of the sums `Σ d(γ tᵢ, γ tᵢ₊₁)` over the partitions. -/
def length (p : RectPath x y) : ℝ≥0∞ := eVariationOn p.toFun (Icc p.a p.b)

/-- The constant curve. -/
def const (x : X) : RectPath x x where
  toFun _ := x
  a := 0
  b := 0
  le := le_rfl
  continuousOn := continuousOn_const
  source := rfl
  target := rfl

@[simp] theorem length_const (x : X) : (const x).length = 0 :=
  eVariationOn.subsingleton _ (by simp [const])

/-- The trivial partition: `d(x, y) ≤ ℓ(γ)` (Observación 8.1.7). -/
theorem edist_le_length (p : RectPath x y) : edist x y ≤ p.length := by
  have := eVariationOn.edist_le p.toFun (left_mem_Icc.2 p.le) (right_mem_Icc.2 p.le)
  rwa [p.source, p.target] at this

/-- The reversed curve `t ↦ γ (-t)` on `[-b, -a]`, from `y` to `x`. -/
def reverse (p : RectPath x y) : RectPath y x where
  toFun t := p.toFun (-t)
  a := -p.b
  b := -p.a
  le := neg_le_neg p.le
  continuousOn := p.continuousOn.comp continuous_neg.continuousOn fun t ht ↦
    ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  source := by simp [p.target]
  target := by simp [p.source]

@[simp] theorem length_reverse (p : RectPath x y) : p.reverse.length = p.length := by
  change eVariationOn (p.toFun ∘ Neg.neg) (Icc (-p.b) (-p.a)) = _
  rw [eVariationOn.comp_eq_of_antitoneOn _ _ (fun _ _ _ _ h ↦ neg_le_neg h), image_neg_Icc,
    neg_neg, neg_neg]
  rfl

/-- The concatenation of a curve from `x` to `y` and a curve from `y` to `z`: the second one is
translated so that it starts at the final time of the first. -/
def concat (p : RectPath x y) (q : RectPath y z) : RectPath x z where
  toFun t := if t ≤ p.b then p.toFun t else q.toFun (t + (q.a - p.b))
  a := p.a
  b := p.b + (q.b - q.a)
  le := p.le.trans (le_add_of_nonneg_right (sub_nonneg.mpr q.le))
  continuousOn := by
    have h1 : ContinuousOn (fun t ↦ if t ≤ p.b then p.toFun t else q.toFun (t + (q.a - p.b)))
        (Icc p.a p.b) :=
      p.continuousOn.congr fun t ht ↦ by simp [ht.2]
    have h2 : ContinuousOn (fun t ↦ if t ≤ p.b then p.toFun t else q.toFun (t + (q.a - p.b)))
        (Icc p.b (p.b + (q.b - q.a))) := by
      have hq : ContinuousOn (fun t ↦ q.toFun (t + (q.a - p.b))) (Icc p.b (p.b + (q.b - q.a))) :=
        q.continuousOn.comp (continuous_id.add continuous_const).continuousOn fun t ht ↦
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine hq.congr fun t ht ↦ ?_
      by_cases htb : t ≤ p.b
      · have : t = p.b := le_antisymm htb ht.1
        subst this
        simp [p.target, q.source]
      · simp [htb]
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc p.le (le_add_of_nonneg_right (sub_nonneg.mpr q.le))] at this
  source := by simp [p.le, p.source]
  target := by
    by_cases h : p.b + (q.b - q.a) ≤ p.b
    · have hqb : q.b = q.a := le_antisymm (by linarith) q.le
      simp only [h, ite_true]
      have : p.b + (q.b - q.a) = p.b := by rw [hqb, sub_self, add_zero]
      rw [this, p.target, ← q.source, ← hqb, q.target]
    · simp only [h, ite_false]
      rw [show p.b + (q.b - q.a) + (q.a - p.b) = q.b by ring, q.target]

/-- **Lengths add under concatenation** (*Estructuras*, §8.1, property 3). -/
theorem length_concat (p : RectPath x y) (q : RectPath y z) :
    (p.concat q).length = p.length + q.length := by
  set f := (p.concat q).toFun
  have hb : p.b ≤ p.b + (q.b - q.a) := le_add_of_nonneg_right (sub_nonneg.mpr q.le)
  have hsplit := eVariationOn.Icc_add_Icc f (s := Icc p.a (p.b + (q.b - q.a))) p.le hb
    ⟨p.le, hb⟩
  rw [inter_eq_right.mpr (Icc_subset_Icc le_rfl hb),
    inter_eq_right.mpr (Icc_subset_Icc p.le le_rfl), inter_self] at hsplit
  change eVariationOn f (Icc p.a (p.b + (q.b - q.a))) = _
  rw [← hsplit]
  congr 1
  · refine eVariationOn.eq_of_eqOn fun t ht ↦ ?_
    simp [f, concat, ht.2]
  · have heq : EqOn f (q.toFun ∘ fun t ↦ t + (q.a - p.b)) (Icc p.b (p.b + (q.b - q.a))) := by
      intro t ht
      by_cases htb : t ≤ p.b
      · have : t = p.b := le_antisymm htb ht.1
        subst this
        simp [f, concat, p.target, q.source]
      · simp [f, concat, htb]
    rw [eVariationOn.eq_of_eqOn heq, eVariationOn.comp_eq_of_monotoneOn q.toFun
      (fun t ↦ t + (q.a - p.b)) (fun _ _ _ _ h ↦ by simpa using h), image_add_const_Icc]
    congr 2 <;> ring

end RectPath

/-! ### The rectifiable distance -/

/-- The **rectifiable distance** `d_ℓ(x, y)`: the infimum of the lengths of the continuous curves
from `x` to `y`, and `∞` if there is none (*Estructuras*, §8.1). -/
def lengthDist (x y : X) : ℝ≥0∞ := ⨅ p : RectPath x y, p.length

theorem lengthDist_le {x y : X} (p : RectPath x y) : lengthDist x y ≤ p.length :=
  iInf_le _ p

/-- **`d ≤ d_ℓ`** (Observación 8.1.7). -/
theorem edist_le_lengthDist (x y : X) : edist x y ≤ lengthDist x y :=
  le_iInf fun p ↦ p.edist_le_length

@[simp] theorem lengthDist_self (x : X) : lengthDist x x = 0 :=
  le_antisymm ((lengthDist_le (RectPath.const x)).trans_eq (RectPath.length_const x)) bot_le

theorem lengthDist_comm (x y : X) : lengthDist x y = lengthDist y x :=
  le_antisymm (le_iInf fun p ↦ (lengthDist_le p.reverse).trans_eq p.length_reverse)
    (le_iInf fun p ↦ (lengthDist_le p.reverse).trans_eq p.length_reverse)

/-- The triangle inequality for `d_ℓ`, by concatenation of curves. -/
theorem lengthDist_triangle (x y z : X) : lengthDist x z ≤ lengthDist x y + lengthDist y z := by
  rcases isEmpty_or_nonempty (RectPath x y) with hxy | hxy
  · simp [lengthDist]
  rcases isEmpty_or_nonempty (RectPath y z) with hyz | hyz
  · simp [lengthDist]
  refine ENNReal.le_iInf_add_iInf fun p q ↦ ?_
  rw [← RectPath.length_concat]
  exact lengthDist_le _

/-! ### The space with the rectifiable distance -/

/-- A copy of `X` with the rectifiable distance `d_ℓ`. -/
def LengthMetric (X : Type*) := X

/-- The identity `X → LengthMetric X`. -/
def toLength : X → LengthMetric X := id

/-- The identity `LengthMetric X → X`. -/
def ofLength : LengthMetric X → X := id

instance : PseudoEMetricSpace (LengthMetric X) where
  edist x y := lengthDist (ofLength x) (ofLength y)
  edist_self x := lengthDist_self _
  edist_comm x y := lengthDist_comm _ _
  edist_triangle x y z := lengthDist_triangle _ _ _

theorem edist_toLength (x y : X) : edist (toLength x) (toLength y) = lengthDist x y := rfl

/-- The identity `(X, d_ℓ) → (X, d)` is `1`-Lipschitz: the topology of `d_ℓ` is finer than that
of `d` (it has more open sets; Observación 8.1.7). -/
theorem lipschitzWith_ofLength : LipschitzWith 1 (ofLength : LengthMetric X → X) :=
  LipschitzWith.of_edist_le fun x y ↦ edist_le_lengthDist (ofLength x) (ofLength y)

theorem continuous_ofLength : Continuous (ofLength : LengthMetric X → X) :=
  lipschitzWith_ofLength.continuous

/-- **When do the topologies of `d` and `d_ℓ` agree** (Lema 8.1.8): exactly when, for every `x`
and every `ε > 0`, all the points close enough to `x` (for `d`) can be joined to `x` by a curve of
length `< ε`. -/
theorem continuous_toLength_iff :
    Continuous (toLength : X → LengthMetric X) ↔
      ∀ x : X, ∀ ε > 0, ∀ᶠ y in 𝓝 x, lengthDist y x < ε := by
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun x ↦ ?_
  exact EMetric.tendsto_nhds

/-- A pseudo-(extended) metric space is an **interior metric space** (a length space) if the
distance between two points is the infimum of the lengths of the continuous curves joining them
(*Estructuras*, §8.1.1). -/
def IsInterior (X : Type*) [PseudoEMetricSpace X] : Prop := ∀ x y : X, lengthDist x y = edist x y

/-- In an interior metric space, curves of length arbitrarily close to the distance exist. -/
theorem IsInterior.exists_rectPath (h : IsInterior X) {x y : X} {ε : ℝ≥0∞}
    (hxy : edist x y < ε) : ∃ p : RectPath x y, p.length < ε := by
  rw [← h x y] at hxy
  exact iInf_lt_iff.mp hxy

/-! ### Approximate midpoints -/

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- **Interior metric spaces have approximate midpoints** (*Estructuras*, Problema 8.III, a
consequence of Lema 8.1.10): for every `x, y` and `ε > 0` there is `z` with
`max (d(x, z), d(z, y)) ≤ d(x, y) / 2 + ε`. Take a curve of length `< d(x, y) + 2ε` and its point
at half the length, which exists by the continuity of the arc length (Lema 8.1.4). -/
theorem IsInterior.exists_approx_midpoint (h : IsInterior X) (x y : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ z, dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε := by
  have hlt : edist x y < ENNReal.ofReal (dist x y + 2 * ε) := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by positivity⟩
  obtain ⟨p, hp⟩ := h.exists_rectPath hlt
  set L := p.length
  have hLtop : L ≠ ⊤ := ne_top_of_lt hp
  set s := Icc p.a p.b
  have ha : p.a ∈ s := left_mem_Icc.2 p.le
  have hb : p.b ∈ s := right_mem_Icc.2 p.le
  have hbv : BoundedVariationOn p.toFun s := hLtop
  set F := variationOnFromTo p.toFun s p.a
  have hcont : ContinuousOn F s := fun t ht ↦
    (hbv.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (p.continuousOn t ht)
  have hFa : F p.a = 0 := variationOnFromTo.self _ _ _
  have hFb : F p.b = L.toReal := by
    simp only [F, variationOnFromTo.eq_of_le _ _ p.le, inter_self, L, RectPath.length, s]
  have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  obtain ⟨t, ht, hFt⟩ : ∃ t ∈ s, F t = L.toReal / 2 := by
    have := intermediate_value_Icc p.le hcont
    rw [hFa, hFb] at this
    exact this ⟨by linarith, by linarith⟩
  have hLlt : L.toReal < dist x y + 2 * ε := ENNReal.toReal_lt_of_lt_ofReal hp
  have hsub : ∀ {u v : ℝ}, u ∈ s → v ∈ s → u ≤ v →
      dist (p.toFun u) (p.toFun v) ≤ variationOnFromTo p.toFun s u v := by
    intro u v hu hv huv
    rw [variationOnFromTo.eq_of_le _ _ huv, dist_edist]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top hLtop
      (eVariationOn.mono _ inter_subset_left)) ?_
    exact eVariationOn.edist_le _ ⟨hu, le_rfl, huv⟩ ⟨hv, huv, le_rfl⟩
  have hadd := variationOnFromTo.add hbv.locallyBoundedVariationOn ha ht hb
  refine ⟨p.toFun t, ?_, ?_⟩
  · have := hsub ha ht ht.1
    rw [p.source] at this
    change dist x (p.toFun t) ≤ F t at this
    linarith
  · have := hsub ht hb ht.2
    rw [p.target] at this
    have hFb' : variationOnFromTo p.toFun s p.a p.b = L.toReal := hFb
    change F t + variationOnFromTo p.toFun s t p.b = _ at hadd
    linarith

end Metric

end LCManifolds
