/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Metric.FinslerBounded
import LCManifolds.MetricGeometry.HopfRinow

/-!
# Hopf–Rinow for finite-dimensional Finsler manifolds

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Corolario
9.1.10.

Let `M` be a Hausdorff manifold modeled on a finite-dimensional normed space, with a reversible
Finsler metric `μ` whose seminorms are norms, and assume that `d_b` is finite (for instance, `M`
is connected by piecewise `C¹` paths). Then:

* `d_b` is a distance (`metricSpace`), since `μ` is bounded below (Teorema 9.1.5,
  Lema 9.1.8);
* `(M, d_b)` is locally compact, since it is homeomorphic to `M` (Corolario 9.1.9);
* `(M, d_b)` is an interior metric space (Proposición 9.1.2).

So if `(M, d_b)` is complete, the metric Hopf–Rinow theorem (Teorema 8.2.3) gives **shortest
curves**: any two points are joined by a continuous curve whose length is their distance
(`exists_rectPath_length_eq`, Corolario 9.1.10). These curves are continuous for `d_b`; whether
they can be taken piecewise `C¹` is a separate question (*Estructuras*, Observación 9.1.11).
-/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace LCManifolds

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M] [T2Space M]

namespace FinslerMetric

variable (μ : FinslerMetric E M) [Fact μ.toFinslerLengthStructure.IsReversible]
  (hnd : μ.toFinslerSeminormField.IsNondegenerate)
  (hfin : ∀ x y : M, μ.toFinslerLengthStructure.dist x y ≠ ⊤)

/-- The distance `d_b` as a metric space structure on `FinslerSpace`: it separates points
(Teorema 9.1.5 and Lema 9.1.8) and is finite by hypothesis. -/
@[instance_reducible]
def metricSpace : MetricSpace μ.toFinslerLengthStructure.FinslerSpace :=
  letI : EMetricSpace μ.toFinslerLengthStructure.FinslerSpace :=
    { (inferInstance : PseudoEMetricSpace μ.toFinslerLengthStructure.FinslerSpace) with
      eq_of_edist_eq_zero := fun {x y} h ↦
        μ.toFinslerLengthStructure.eq_of_dist_eq_zero
          (μ.isBounded_of_finiteDimensional hnd).isBoundedBelow
          (le_antisymm ((bdist_le_edist x y).trans h.le) bot_le) }
  EMetricSpace.toMetricSpace fun x y ↦ by
    rw [show edist x y = _ from μ.toFinslerLengthStructure.edist_toFinsler x y]
    exact hfin _ _

include hnd in
/-- `(M, d_b)` is locally compact: it is homeomorphic to `M` (Corolario 9.1.9). -/
theorem locallyCompactSpace : LocallyCompactSpace μ.toFinslerLengthStructure.FinslerSpace :=
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  (μ.toFinslerLengthStructure.homeomorphFinsler
    (μ.isBounded_of_finiteDimensional hnd)).symm.isOpenEmbedding.locallyCompactSpace

include hnd hfin in
/-- **Corolario 9.1.10 (Hopf–Rinow).** On a finite-dimensional Hausdorff manifold with a
reversible Finsler metric whose seminorms are norms, if `d_b` is finite and `(M, d_b)` is
complete, any two points are joined by a continuous curve of length `d_b(x, y)`. -/
theorem exists_rectPath_length_eq
    [hc : CompleteSpace μ.toFinslerLengthStructure.FinslerSpace] (x y : M) :
    ∃ p : RectPath (μ.toFinslerLengthStructure.toFinsler x)
        (μ.toFinslerLengthStructure.toFinsler y),
      p.length = μ.toFinslerLengthStructure.dist x y := by
  let := μ.metricSpace hnd hfin
  have : LocallyCompactSpace μ.toFinslerLengthStructure.FinslerSpace := μ.locallyCompactSpace hnd
  have : CompleteSpace μ.toFinslerLengthStructure.FinslerSpace := hc
  have hint : IsInterior μ.toFinslerLengthStructure.FinslerSpace :=
    μ.toFinslerLengthStructure.isInterior
  obtain ⟨p, hp⟩ := hint.exists_rectPath_length_eq (μ.toFinslerLengthStructure.toFinsler x)
    (μ.toFinslerLengthStructure.toFinsler y)
  refine ⟨p, hp.trans ?_⟩
  exact μ.toFinslerLengthStructure.edist_toFinsler x y

end FinslerMetric

end LCManifolds
