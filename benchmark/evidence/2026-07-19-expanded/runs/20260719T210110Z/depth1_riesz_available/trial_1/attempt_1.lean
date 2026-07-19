import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 1. -/
axiom provided_riesz_extension (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  have hN0 : N (0 : E) = 0 := by
    have h := N_hom (2 : ℝ) (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith

  let D : Submodule ℝ (E × ℝ) :=
    { carrier := {p | p.1 ∈ f.domain}
      zero_mem' := by
        change (0 : E) ∈ f.domain
        exact f.domain.zero_mem
      add_mem' := by
        intro a b ha hb
        change a.1 + b.1 ∈ f.domain
        exact f.domain.add_mem ha hb
      smul_mem' := by
        intro c a ha
        change c • a.1 ∈ f.domain
        exact f.domain.smul_mem c ha }

  let first : D →ₗ[ℝ] f.domain :=
    { toFun := fun p => ⟨p.1.1, p.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c a
        apply Subtype.ext
        rfl }

  let second : D →ₗ[ℝ] ℝ :=
    { toFun := fun p => p.1.2
      map_add' := by
        intro a b
        rfl
      map_smul' := by
        intro c a
        rfl }

  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := D
      toLinearMap := second - f.toLinearMap.comp first }

  let S : PointedCone ℝ (E × ℝ) :=
    { carrier := {p | N p.1 ≤ p.2}
      zero_mem' := by
        change N (0 : E) ≤ (0 : ℝ)
        simp [hN0]
      add_mem' := by
        intro a b ha hb
        change N (a.1 + b.1) ≤ a.2 + b.2
        exact (N_add a.1 b.1).trans (add_le_add ha hb)
      smul_mem' := by
        intro c hc p hp
        change N (c • p.1) ≤ c * p.2
        rcases hc.eq_or_lt with (rfl | hcpos)
        · simp [hN0]
        · rw [N_hom c hcpos p.1]
          exact mul_le_mul_of_nonneg_left hp hc }

  obtain ⟨G, hG, hGpos⟩ :=
    provided_riesz_extension (E := E × ℝ) S F
      (by
        intro z hz
        change 0 ≤ z.1.2 - f ⟨z.1.1, z.2⟩
        change N z.1.1 ≤ z.1.2 at hz
        exact sub_nonneg.mpr ((hf ⟨z.1.1, z.2⟩).trans hz))
      (by
        intro y
        refine ⟨⟨((0 : E), N y.1 - y.2), ?_⟩, ?_⟩
        · change (0 : E) ∈ f.domain
          exact f.domain.zero_mem
        · change N ((0 : E) + y.1) ≤ (N y.1 - y.2) + y.2
          simp)

  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -G (x, 0)
      map_add' := by
        intro x y
        rw [show (x + y, (0 : ℝ)) = (x, 0) + (y, 0) by ext <;> simp]
        rw [map_add, neg_add]
      map_smul' := by
        intro c x
        rw [show (c • x, (0 : ℝ)) = c • (x, 0) by ext <;> simp]
        rw [map_smul]
        simp }

  refine ⟨g, ?_, ?_⟩
  · intro x
    have h :=
      hG (⟨((x : E), (0 : ℝ)), x.2⟩ : F.domain)
    change G ((x : E), 0) = (0 : ℝ) - f x at h
    change -G ((x : E), 0) = f x
    linarith
  · intro x
    have hzero : G ((0 : E), N x) = N x := by
      have h :=
        hG (⟨((0 : E), N x), f.domain.zero_mem⟩ : F.domain)
      change G ((0 : E), N x) = N x - f (0 : f.domain) at h
      simpa using h
    have hp : 0 ≤ G (x, N x) :=
      hGpos (x, N x) (by
        change N x ≤ N x
        exact le_rfl)
    have hsum :
        G (x, N x) = G (x, 0) + G ((0 : E), N x) := by
      rw [show (x, N x) = (x, 0) + ((0 : E), N x) by ext <;> simp]
      rw [map_add]
    rw [hsum, hzero] at hp
    change -G (x, 0) ≤ N x
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth1
