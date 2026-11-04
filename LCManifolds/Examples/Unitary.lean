/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Projector
import LCAnalysis.MBFrechet
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Example: the unitary group of a Banach `*`-algebra

Let `A` be a real Banach algebra with a continuous involution (for instance `B(H)`, for a
complex or real Hilbert space `H`, seen as a real algebra). The unitary group
`U(A) = {u | u* u = 1 = u u*}` is a split submanifold of `A`, modeled on the closed subspace
`𝔲(A) = {X | X* = -X}` of skew-adjoint elements, complemented by the self-adjoint ones.

**Completeness.** Here `A` is complete, so `A` is a Banach manifold and `U(A)` is a Banach
submanifold. Completeness is used twice: the invertible elements form an open set, and inversion
is smooth there.

The slice charts are explicit Cayley transforms, with no inverse function theorem. On the open
set `{a | a + 1 invertible}`,

  `φ(a) = 1 - 2 (a + 1)⁻¹`,   `φ⁻¹(X) = 2 (1 - X)⁻¹ - 1`,

(that is, `φ(a) = (a - 1)(a + 1)⁻¹` and `φ⁻¹(X) = (1 + X)(1 - X)⁻¹`), and `a` is unitary iff
`φ(a)` is skew-adjoint. This equivalence is pure algebra: no spectral theory is needed. Charts at
other points `p ∈ U(A)` are obtained by composing with the left translation `a ↦ p* a`.

Main results:

* `isSplitSubmanifold_unitary`: `U(A)` is a split submanifold of `A` modeled on `𝔲(A)`;
* `tangentSpace_unitary`: `T_p U(A) = {w | p* w ∈ 𝔲(A)} = p · 𝔲(A)`;
* `projectorField_unitary`: the projectors `E_p w = (w - p w* p) / 2` onto `T_p U(A)` form a
  field of projectors;
* `isGeodesic_unitary_iff`: for the connection they define, a curve is a geodesic iff
  `α̈ = α α̈* α`;
* `isGeodesic_expCurve`: the one-parameter subgroups `t ↦ p exp(t X)`, `X* = -X`, are geodesics;
* `isSplitSubmanifold_unitary_clm`: the case `A = B(H)`, `H` a complex Hilbert space.
-/

open Set Filter
open scoped Topology Manifold ContDiff
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [StarRing A]
  [StarModule ℝ A] [ContinuousStar A]

namespace Cayley

/-- The unit `1 + 1`, with inverse `2⁻¹ • 1`. -/
def twoUnit : Aˣ where
  val := 1 + 1
  inv := (2⁻¹ : ℝ) • 1
  val_inv := by
    rw [← two_smul ℝ (1 : A), smul_mul_smul_comm, one_mul]
    norm_num
  inv_val := by
    rw [← two_smul ℝ (1 : A), smul_mul_smul_comm, one_mul]
    norm_num

/-- `2 • u⁻¹`, a unit with inverse `2⁻¹ • u`. -/
def twoInvUnit (u : Aˣ) : Aˣ where
  val := (2 : ℝ) • (↑u⁻¹ : A)
  inv := (2⁻¹ : ℝ) • (u : A)
  val_inv := by
    rw [smul_mul_smul_comm, Units.inv_mul]
    norm_num
  inv_val := by
    rw [smul_mul_smul_comm, Units.mul_inv]
    norm_num

omit [CompleteSpace A] [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem inverse_twoInvUnit (u : Aˣ) :
    Ring.inverse ((2 : ℝ) • (↑u⁻¹ : A)) = (2⁻¹ : ℝ) • (u : A) :=
  Ring.inverse_unit (twoInvUnit u)

/-- The Cayley chart near `1`: `φ(a) = 1 - 2 (a + 1)⁻¹ = (a - 1)(a + 1)⁻¹`. -/
def cay (a : A) : A := 1 - (2 : ℝ) • Ring.inverse (a + 1)

/-- Its inverse: `φ⁻¹(X) = 2 (1 - X)⁻¹ - 1 = (1 + X)(1 - X)⁻¹`. -/
def cayInv (X : A) : A := (2 : ℝ) • Ring.inverse (1 - X) - 1

omit [CompleteSpace A] [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem one_sub_cay {a : A} (u : Aˣ) (hu : (u : A) = a + 1) :
    1 - cay a = (2 : ℝ) • (↑u⁻¹ : A) := by
  rw [cay, ← hu, Ring.inverse_unit, sub_sub_cancel]

omit [CompleteSpace A] [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem cayInv_add_one {X : A} (v : Aˣ) (hv : (v : A) = 1 - X) :
    cayInv X + 1 = (2 : ℝ) • (↑v⁻¹ : A) := by
  rw [cayInv, ← hv, Ring.inverse_unit, sub_add_cancel]

omit [CompleteSpace A] [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem cayInv_cay {a : A} (ha : IsUnit (a + 1)) : cayInv (cay a) = a := by
  obtain ⟨u, hu⟩ := ha
  rw [cayInv, one_sub_cay u hu, inverse_twoInvUnit, smul_smul]
  norm_num
  rw [hu, add_sub_cancel_right]

omit [CompleteSpace A] [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem cay_cayInv {X : A} (hX : IsUnit (1 - X)) : cay (cayInv X) = X := by
  obtain ⟨v, hv⟩ := hX
  rw [cay, cayInv_add_one v hv, inverse_twoInvUnit, smul_smul]
  norm_num
  rw [hv, sub_sub_cancel]

omit [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem contDiffOn_cay : ContDiffOn ℝ ∞ (cay : A → A) {a | IsUnit (a + 1)} := by
  rintro a ⟨u, hu⟩
  refine ContDiffAt.contDiffWithinAt ?_
  have hi : ContDiffAt ℝ ∞ (fun b : A ↦ Ring.inverse (b + 1)) a := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at h
    exact h.comp a (contDiffAt_id.add contDiffAt_const)
  exact contDiffAt_const.sub (hi.const_smul (2 : ℝ))

omit [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem contDiffOn_cayInv : ContDiffOn ℝ ∞ (cayInv : A → A) {X | IsUnit (1 - X)} := by
  rintro X ⟨v, hv⟩
  refine ContDiffAt.contDiffWithinAt ?_
  have hi : ContDiffAt ℝ ∞ (fun Y : A ↦ Ring.inverse (1 - Y)) X := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) v
    rw [hv] at h
    exact h.comp X (contDiffAt_const.sub contDiffAt_id)
  exact (hi.const_smul (2 : ℝ)).sub contDiffAt_const

variable (A) in
/-- The Cayley slice chart around `1`, defined on `{a | a + 1 invertible}`. -/
def chart : OpenPartialHomeomorph A A where
  toFun := cay
  invFun := cayInv
  source := {a | IsUnit (a + 1)}
  target := {X | IsUnit (1 - X)}
  map_source' a ha := by
    obtain ⟨u, hu⟩ := ha
    change IsUnit (1 - cay a)
    rw [one_sub_cay u hu]
    exact (twoInvUnit u).isUnit
  map_target' X hX := by
    obtain ⟨v, hv⟩ := hX
    change IsUnit (cayInv X + 1)
    rw [cayInv_add_one v hv]
    exact (twoInvUnit v).isUnit
  left_inv' _ ha := cayInv_cay ha
  right_inv' _ hX := cay_cayInv hX
  open_source := Units.isOpen.preimage (continuous_id.add continuous_const)
  open_target := Units.isOpen.preimage (continuous_const.sub continuous_id)
  continuousOn_toFun := contDiffOn_cay.continuousOn
  continuousOn_invFun := contDiffOn_cayInv.continuousOn

omit [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
theorem chart_mem : chart A ∈ mbGroupoid A := by
  have hs : IsOpen (chart A).source := (chart A).open_source
  have ht : IsOpen (chart A).target := (chart A).open_target
  exact ⟨(smoothMBOn_iff_contDiffOn hs).mpr contDiffOn_cay,
    (smoothMBOn_iff_contDiffOn ht).mpr contDiffOn_cayInv⟩

omit [CompleteSpace A] [ContinuousStar A] in
/-- **The Cayley transform detects unitarity**: if `a + 1` is invertible, then `a` is unitary iff
`φ(a)` is skew-adjoint. Pure algebra. -/
theorem mem_unitary_iff {a : A} (ha : IsUnit (a + 1)) :
    a ∈ unitary A ↔ cay a ∈ skewAdjoint.submodule ℝ A := by
  obtain ⟨u, hu⟩ := ha
  -- `s = a + 1`, `t = a* + 1`, `i = s⁻¹`, `j = t⁻¹ = i*`
  set i : A := ↑u⁻¹ with hi
  have hs1 : (a + 1) * i = 1 := by rw [← hu]; exact u.mul_inv
  have hs2 : i * (a + 1) = 1 := by rw [← hu]; exact u.inv_mul
  have ht1 : (star a + 1) * star i = 1 := by
    simpa [star_mul, star_add] using congrArg star hs2
  have ht2 : star i * (star a + 1) = 1 := by
    simpa [star_mul, star_add] using congrArg star hs1
  have hcay : cay a = 1 - (2 : ℝ) • i := by rw [cay, ← hu, Ring.inverse_unit]
  -- `φ(a)* = -φ(a)` iff `i + i* = 1`
  have hskew : cay a ∈ skewAdjoint.submodule ℝ A ↔ i + star i = 1 := by
    change star (cay a) = -cay a ↔ _
    rw [hcay, star_sub, star_one, star_smul, star_trivial]
    constructor
    · intro h
      have h2 : (2 : ℝ) • (i + star i) = (2 : ℝ) • 1 := by
        rw [smul_add, two_smul ℝ (1 : A), ← sub_eq_zero]
        calc (2 : ℝ) • i + (2 : ℝ) • star i - (1 + 1) =
            -((1 - (2 : ℝ) • star i) - -(1 - (2 : ℝ) • i)) := by abel
          _ = 0 := by rw [h, sub_self, neg_zero]
      exact smul_right_injective A (two_ne_zero : (2 : ℝ) ≠ 0) h2
    · intro h
      have : star i = 1 - i := by rw [← h, add_sub_cancel_left]
      rw [this, smul_sub, two_smul ℝ (1 : A)]
      abel
  rw [hskew, Unitary.mem_iff]
  constructor
  · rintro ⟨h1, -⟩
    -- `i + j = j (t + s) i = j t s i = 1`, using `t s = t + s` (from `a* a = 1`)
    have hts : (star a + 1) * (a + 1) = (star a + 1) + (a + 1) := by
      rw [add_mul, mul_add, mul_add, h1]; noncomm_ring
    calc i + star i = star i * (star a + 1) * i + star i * ((a + 1) * i) := by
            rw [ht2, hs1, one_mul, mul_one]
      _ = star i * ((star a + 1) + (a + 1)) * i := by noncomm_ring
      _ = 1 := by rw [← hts, ← mul_assoc, ht2, one_mul, hs1]
  · intro h
    -- `t s = t (i + j) s = t + s`, and `s t = s (i + j) t = s + t`
    have e1 : (star a + 1) * (a + 1) = (star a + 1) + (a + 1) := by
      calc (star a + 1) * (a + 1) = (star a + 1) * (i + star i) * (a + 1) := by
              rw [h, mul_one]
        _ = (star a + 1) * (i * (a + 1)) + (star a + 1) * star i * (a + 1) := by noncomm_ring
        _ = (star a + 1) + (a + 1) := by rw [hs2, ht1, mul_one, one_mul]
    have e2 : (a + 1) * (star a + 1) = (a + 1) + (star a + 1) := by
      calc (a + 1) * (star a + 1) = (a + 1) * (i + star i) * (star a + 1) := by
              rw [h, mul_one]
        _ = (a + 1) * i * (star a + 1) + (a + 1) * (star i * (star a + 1)) := by noncomm_ring
        _ = (a + 1) + (star a + 1) := by rw [hs1, ht2, mul_one, one_mul, add_comm]
    constructor
    · calc star a * a = (star a + 1) * (a + 1) - (star a + 1) - (a + 1) + 1 := by noncomm_ring
        _ = 1 := by rw [e1]; abel
    · calc a * star a = (a + 1) * (star a + 1) - (a + 1) - (star a + 1) + 1 := by noncomm_ring
        _ = 1 := by rw [e2]; abel

/-- The left translation `a ↦ p* a` by a unitary `p`, with inverse `a ↦ p a`. -/
def leftMul (p : unitary A) : A ≃L[ℝ] A where
  toFun a := star (p : A) * a
  invFun a := (p : A) * a
  map_add' := mul_add _
  map_smul' c a := mul_smul_comm c _ a
  left_inv a := by
    simp only [← mul_assoc, Unitary.mul_star_self_of_mem p.2, one_mul]
  right_inv a := by
    simp only [← mul_assoc, Unitary.star_mul_self_of_mem p.2, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

omit [CompleteSpace A] [StarModule ℝ A] [ContinuousStar A] in
theorem leftMul_apply (p : unitary A) (a : A) : leftMul p a = star (p : A) * a := rfl

omit [CompleteSpace A] [StarModule ℝ A] [ContinuousStar A] in
theorem leftMul_mem (p : unitary A) :
    (leftMul p).toHomeomorph.toOpenPartialHomeomorph ∈ mbGroupoid A := by
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · exact (leftMul p).toContinuousLinearMap.contDiffMBOn k _
  · exact (leftMul p).symm.toContinuousLinearMap.contDiffMBOn k _

/-- The slice chart around `p ∈ U(A)`: translate by `p*`, then the Cayley chart. -/
def chartAt' (p : unitary A) : OpenPartialHomeomorph A A :=
  (leftMul p).toHomeomorph.toOpenPartialHomeomorph.trans (chart A)

omit [StarModule ℝ A] [ContinuousStar A] in
theorem chartAt'_mem (p : unitary A) : chartAt' p ∈ mbGroupoid A :=
  (mbGroupoid A).trans (leftMul_mem p) chart_mem

omit [StarModule ℝ A] [ContinuousStar A] in
theorem mem_chartAt'_source (p : unitary A) : (p : A) ∈ (chartAt' p).source := by
  refine ⟨mem_univ _, ?_⟩
  change IsUnit (star (p : A) * p + 1)
  rw [Unitary.star_mul_self_of_mem p.2]
  exact (twoUnit : Aˣ).isUnit

omit [ContinuousStar A] in
theorem isSliceChart (p : unitary A) :
    IsSliceChart (unitary A : Set A) (skewAdjoint.submodule ℝ A) (chartAt' p) := by
  refine ⟨StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ (chartAt'_mem p), fun q hq ↦ ?_⟩
  change q ∈ unitary A ↔ cay (star (p : A) * q) ∈ _
  have hq' : IsUnit (star (p : A) * q + 1) := hq.2
  rw [← mem_unitary_iff hq']
  constructor
  · exact fun h ↦ mul_mem (Unitary.star_mem p.2) h
  · intro h
    have : q = (p : A) * (star (p : A) * q) := by
      rw [← mul_assoc, Unitary.mul_star_self_of_mem p.2, one_mul]
    rw [this]
    exact mul_mem p.2 h

end Cayley

omit [CompleteSpace A] in
variable (A) in
/-- The skew-adjoint elements are complemented: `X ↦ (X - X*)/2` is a continuous projection. -/
theorem closedComplemented_skewAdjoint : (skewAdjoint.submodule ℝ A).ClosedComplemented := by
  let P : A →L[ℝ] A :=
    { toFun := fun x ↦ (2⁻¹ : ℝ) • (x - star x)
      map_add' := fun x y ↦ by simp only [star_add, smul_sub, smul_add]; abel
      map_smul' := fun c x ↦ by
        simp only [star_smul, star_trivial, RingHom.id_apply, smul_sub, smul_comm c]
      cont := continuous_const.smul (continuous_id.sub continuous_star) }
  have hP : ∀ x, P x ∈ skewAdjoint.submodule ℝ A := fun x ↦ by
    change star ((2⁻¹ : ℝ) • (x - star x)) = -((2⁻¹ : ℝ) • (x - star x))
    rw [star_smul, star_trivial, star_sub, star_star, ← smul_neg, neg_sub]
  refine ⟨P.codRestrict _ hP, fun x ↦ Subtype.ext ?_⟩
  change (2⁻¹ : ℝ) • ((x : A) - star (x : A)) = x
  have hx : star (x : A) = -(x : A) := x.2
  rw [hx, sub_neg_eq_add, ← two_smul ℝ (x : A), smul_smul]
  norm_num

omit [CompleteSpace A] in
theorem isClosed_skewAdjoint : IsClosed (skewAdjoint.submodule ℝ A : Set A) :=
  isClosed_eq continuous_star continuous_neg

open Cayley in
/-- **The unitary group of a Banach `*`-algebra is a split submanifold**, modeled on the
skew-adjoint elements. -/
theorem isSplitSubmanifold_unitary :
    IsSplitSubmanifold (unitary A : Set A) (skewAdjoint.submodule ℝ A) where
  isClosed := isClosed_skewAdjoint
  exists_sliceChart p hp :=
    ⟨chartAt' ⟨p, hp⟩, isSliceChart ⟨p, hp⟩, mem_chartAt'_source ⟨p, hp⟩⟩
  closedComplemented := closedComplemented_skewAdjoint A

namespace Cayley

omit [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
/-- The derivative of the Cayley chart at `1` is `w ↦ w / 2`. -/
theorem hasFDerivAt_cay_one :
    HasFDerivAt (cay : A → A) ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ A) 1 := by
  have hf : HasFDerivAt (fun b : A ↦ b + 1) (ContinuousLinearMap.id ℝ A) 1 :=
    (hasFDerivAt_id (1 : A)).add_const (1 : A)
  have hi : HasFDerivAt (fun b : A ↦ Ring.inverse (b + 1))
      ((-ContinuousLinearMap.mulLeftRight ℝ A ↑(twoUnit : Aˣ)⁻¹ ↑(twoUnit : Aˣ)⁻¹).comp
        (ContinuousLinearMap.id ℝ A)) 1 :=
    HasFDerivAt.comp (g := Ring.inverse) (1 : A) (hasFDerivAt_ringInverse (twoUnit : Aˣ)) hf
  have h := (hi.const_smul (2 : ℝ)).const_sub 1
  convert h using 1
  · funext b; rfl
  ext w
  change (2⁻¹ : ℝ) • w = -((2 : ℝ) • -(((2⁻¹ : ℝ) • (1 : A)) * w * ((2⁻¹ : ℝ) • (1 : A))))
  simp only [smul_neg, neg_neg, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul]
  norm_num

omit [StarModule ℝ A] [ContinuousStar A] in
/-- The derivative of the chart around `p`, at `p`, is `w ↦ p* w / 2`. -/
theorem dMB_chartAt'_at (p : unitary A) (w : A) :
    dMB (chartAt' p) (p, w) = (2⁻¹ : ℝ) • (star (p : A) * w) := by
  have hc : HasFDerivAt (cay : A → A) ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ A)
      (leftMul p p) := by
    rw [leftMul_apply, Unitary.star_mul_self_of_mem p.2]
    exact hasFDerivAt_cay_one
  have hL := (leftMul p).hasFDerivAt (x := (p : A))
  have hcomp := hc.comp (p : A) hL
  change dMB (cay ∘ leftMul p) (p, w) = _
  rw [(hcomp.hasDirDerivAt w).dMB_eq]
  rfl

end Cayley

open Cayley in
/-- **The tangent space of `U(A)` at `p` is `p · 𝔲(A)`**: `w` is tangent iff `p* w` is
skew-adjoint. -/
theorem tangentSpace_unitary (p : unitary A) :
    isSplitSubmanifold_unitary.tangentSpace p =
      {w | star (p : A) * w ∈ skewAdjoint.submodule ℝ A} := by
  ext w
  rw [isSplitSubmanifold_unitary.mem_tangentSpace_iff p (isSliceChart p) (mem_chartAt'_source p),
    dMB_chartAt'_at]
  exact Submodule.smul_mem_iff _ (by norm_num)

/-! ### The field of projectors and its geodesics -/

/-- The projector onto `T_p U(A) = p · 𝔲(A)`: `E_p w = (w - p w* p) / 2`, that is,
`E_p w = p · (X - X*) / 2` with `X = p* w`. -/
def unitaryProj (p w : A) : A := (2⁻¹ : ℝ) • (w - p * star w * p)

omit [CompleteSpace A] [ContinuousStar A] in
theorem mul_star_unitaryProj_mul {p : A} (hp : p ∈ unitary A) (w : A) :
    p * star (unitaryProj p w) * p = (2⁻¹ : ℝ) • (p * star w * p - w) := by
  have h1 := Unitary.star_mul_self_of_mem hp
  have h2 := Unitary.mul_star_self_of_mem hp
  simp only [unitaryProj, star_smul, star_trivial, star_sub, star_mul, star_star, mul_smul_comm,
    smul_mul_assoc, mul_sub, sub_mul]
  congr 2
  simp only [← mul_assoc, h2, one_mul]
  rw [mul_assoc, h1, mul_one]

omit [CompleteSpace A] [ContinuousStar A] in
theorem unitaryProj_idem {p : A} (hp : p ∈ unitary A) (w : A) :
    unitaryProj p (unitaryProj p w) = unitaryProj p w := by
  conv_lhs => rw [unitaryProj, mul_star_unitaryProj_mul hp]
  simp only [unitaryProj]
  module

omit [CompleteSpace A] [ContinuousStar A] in
omit [StarModule ℝ A] in
theorem star_mul_unitaryProj {p : A} (hp : p ∈ unitary A) (w : A) :
    star p * unitaryProj p w = (2⁻¹ : ℝ) • (star p * w - star w * p) := by
  have h1 := Unitary.star_mul_self_of_mem hp
  simp only [unitaryProj, mul_smul_comm, mul_sub]
  simp only [← mul_assoc, h1, one_mul]

/-- **The projectors `E_p w = (w - p w* p) / 2` form a field of projectors** onto the tangent
spaces of `U(A)`. -/
def projectorField_unitary : ProjectorField (isSplitSubmanifold_unitary (A := A)).1 where
  E p w := unitaryProj p w
  map_add p w w' := by
    simp only [unitaryProj, star_add, mul_add, add_mul, smul_sub, smul_add]; abel
  map_smul p c w := by
    simp only [unitaryProj, star_smul, star_trivial, mul_smul_comm, smul_mul_assoc, smul_sub,
      smul_comm c]
  idem p w := unitaryProj_idem p.2 w
  range_eq p := by
    have h2 := Unitary.mul_star_self_of_mem p.2
    rw [show (isSplitSubmanifold_unitary (A := A)).1 =
      isSplitSubmanifold_unitary.toIsEmbeddedSubmanifold from rfl, tangentSpace_unitary p]
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      change star (star (p : A) * unitaryProj (p : A) v) =
        -(star (p : A) * unitaryProj (p : A) v)
      rw [star_mul_unitaryProj p.2, star_smul, star_trivial, star_sub, star_mul, star_mul,
        star_star, star_star, ← smul_neg, neg_sub]
    · intro hw
      have hw' : star (star (p : A) * w) = -(star (p : A) * w) := hw
      rw [star_mul, star_star] at hw'
      refine ⟨w, ?_⟩
      change (2⁻¹ : ℝ) • (w - (p : A) * star w * p) = w
      rw [mul_assoc, hw', mul_neg, ← mul_assoc, h2, one_mul, sub_neg_eq_add, ← two_smul ℝ w,
        smul_smul]
      norm_num
  smooth {φ} hφ p₀ := by
    set D : Set (skewAdjoint.submodule ℝ A) := Subtype.val ⁻¹' φ.target
    have hD : IsOpen D := ProjectorField.isOpen_dom φ
    have hDD : IsOpen (D ×ˢ (univ : Set A)) := hD.prod isOpen_univ
    have hψ : ContDiffOn ℝ ∞ (ProjectorField.param φ) D :=
      (smoothMBOn_iff_contDiffOn hD).mp (ProjectorField.smoothMBOn_param hφ)
    have hψ1 : ContDiffOn ℝ ∞ (fun q : skewAdjoint.submodule ℝ A × A ↦
        ProjectorField.param φ q.1) (D ×ˢ univ) := hψ.comp contDiffOn_fst fun q hq ↦ hq.1
    have hstar : ContDiffOn ℝ ∞ (fun q : skewAdjoint.submodule ℝ A × A ↦ star q.2)
        (D ×ˢ univ) :=
      ((starL' ℝ : A ≃L[ℝ] A).contDiff.comp contDiff_snd).contDiffOn
    have hG : ContDiffOn ℝ ∞ (fun q : skewAdjoint.submodule ℝ A × A ↦
        unitaryProj (ProjectorField.param φ q.1) q.2) (D ×ˢ univ) :=
      (contDiffOn_snd.sub ((hψ1.mul hstar).mul hψ1)).const_smul _
    refine (smoothMBOn_iff_contDiffOn hDD).mpr (hG.congr fun q hq ↦ ?_)
    have hx : (((sliceChart hφ p₀).symm q.1 : unitary A) : A) = φ.symm q.1 :=
      sliceChart_symm_apply_coe hφ p₀ hq.1
    change unitaryProj (((sliceChart hφ p₀).symm q.1 : unitary A) : A) q.2 = _
    rw [hx]
    rfl

/-- **Geodesics of `U(A)`**: a curve with smooth ambient curve is a geodesic of the connection
of the projector field iff `α̈ = α α̈* α`. -/
theorem isGeodesic_unitary_iff {α : ℝ → unitary A} (hα : SmoothMBOn (Subtype.val ∘ α) univ) :
    letI := (isSplitSubmanifold_unitary (A := A)).1.chartedSpace
    haveI := (isSplitSubmanifold_unitary (A := A)).1.mbManifold
    (projectorField_unitary (A := A)).connection.IsGeodesic α ↔
      ∀ t, dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1) =
        (α t : A) * star (dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1)) * α t := by
  let := (isSplitSubmanifold_unitary (A := A)).1.chartedSpace
  have := (isSplitSubmanifold_unitary (A := A)).1.mbManifold
  rw [ProjectorField.connection_isGeodesic_iff _
    ((isSplitSubmanifold_unitary (A := A)).1.isCkCurve_of_smooth hα 2)]
  refine forall_congr' fun t ↦ ?_
  change unitaryProj _ _ = 0 ↔ _
  rw [unitaryProj, smul_eq_zero, sub_eq_zero, or_iff_right (by norm_num)]
  exact Iff.rfl

omit [CompleteSpace A] [StarRing A] [StarModule ℝ A] [ContinuousStar A] in
/-- The derivative of a Fréchet differentiable curve. -/
theorem dMB_eq_of_hasDerivAt' {f : ℝ → A} {f' : A} {t : ℝ} (hf : HasDerivAt f f' t) :
    dMB f (t, 1) = f' := by
  rw [(hf.hasFDerivAt.hasDirDerivAt 1).dMB_eq]
  simp

/-- The one-parameter subgroup through `p` in the direction `p X`, `X ∈ 𝔲(A)`:
`t ↦ p exp(t X)`. -/
def expCurve (p : unitary A) {X : A} (hX : X ∈ skewAdjoint A) : ℝ → unitary A :=
  let +nondep : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  fun t ↦ ⟨(p : A) * NormedSpace.exp (t • X), mul_mem p.2
    (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hX))⟩

/-- **One-parameter subgroups `t ↦ p exp(t X)`, `X* = -X`, are geodesics of `U(A)`.** -/
theorem isGeodesic_expCurve (p : unitary A) {X : A} (hX : X ∈ skewAdjoint A) :
    letI := (isSplitSubmanifold_unitary (A := A)).1.chartedSpace
    haveI := (isSplitSubmanifold_unitary (A := A)).1.mbManifold
    (projectorField_unitary (A := A)).connection.IsGeodesic (expCurve p hX) := by
  let +nondep : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hval : Subtype.val ∘ expCurve p hX = fun t : ℝ ↦ (p : A) * NormedSpace.exp (t • X) := rfl
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ (p : A) * NormedSpace.exp (t • X))
      ((p : A) * (NormedSpace.exp (t • X) * X)) t := fun t ↦
    (hasDerivAt_exp_smul_const X t).const_mul _
  have hsmooth : SmoothMBOn (Subtype.val ∘ expCurve p hX) univ := by
    rw [hval, smoothMBOn_iff_contDiffOn isOpen_univ]
    have : ContDiff ℝ ∞ fun t : ℝ ↦ NormedSpace.exp (t • X) :=
      (contDiff_iff_contDiffAt.mpr fun x ↦
        (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt).comp (contDiff_id.smul contDiff_const)
    exact (contDiff_const.mul this).contDiffOn
  rw [isGeodesic_unitary_iff hsmooth]
  intro t
  have h1 : (fun s ↦ dMB (Subtype.val ∘ expCurve p hX) (s, 1)) =
      fun s : ℝ ↦ (p : A) * NormedSpace.exp (s • X) * X := by
    funext s
    rw [hval, dMB_eq_of_hasDerivAt' (hd s), mul_assoc]
  have h2 : dMB (fun s : ℝ ↦ (p : A) * NormedSpace.exp (s • X) * X) (t, 1) =
      (p : A) * NormedSpace.exp (t • X) * X * X := by
    refine dMB_eq_of_hasDerivAt' ?_
    have := (hd t).mul_const X
    simpa only [mul_assoc] using this
  rw [h1, h2]
  change _ = (p : A) * NormedSpace.exp (t • X) * star _ * ((p : A) * NormedSpace.exp (t • X))
  have hXs : star X = -X := hX
  have hE : star (NormedSpace.exp (t • X)) * NormedSpace.exp (t • X) = 1 :=
    Unitary.star_mul_self_of_mem
      (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hX))
  have hc : Commute X (NormedSpace.exp (t • X)) :=
    ((Commute.refl X).smul_right t).exp_right
  have hp := Unitary.star_mul_self_of_mem p.2
  -- `α α̈* α = p e X X e* p* p e = p e X X e* e = p e X X`
  simp only [star_mul, hXs]
  calc (p : A) * NormedSpace.exp (t • X) * X * X
      = (p : A) * NormedSpace.exp (t • X) * (X * X) *
          (star (NormedSpace.exp (t • X)) * NormedSpace.exp (t • X)) := by
        rw [hE, mul_one, mul_assoc _ X X]
    _ = (p : A) * NormedSpace.exp (t • X) * (X * X * star (NormedSpace.exp (t • X)) *
          (star (p : A) * (p : A)) * NormedSpace.exp (t • X)) := by
        rw [hp, mul_one]; noncomm_ring
    _ = _ := by noncomm_ring

/-- **The unitary group of a complex Hilbert space is a split submanifold of `B(H)`**, modeled
on the skew-adjoint operators. -/
theorem isSplitSubmanifold_unitary_clm {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsSplitSubmanifold (unitary (H →L[ℂ] H) : Set (H →L[ℂ] H))
      (skewAdjoint.submodule ℝ (H →L[ℂ] H)) :=
  isSplitSubmanifold_unitary

end LCManifolds
