import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth2

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 2. -/
axiom provided_exists_top (s : PointedCone ℝ E) (p : E →ₗ.[ℝ] ℝ)
    (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
    (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
    ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x

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
  let C : PointedCone ℝ (E × ℝ) :=
    { carrier := {z | N z.1 ≤ z.2}
      zero_mem' := by
        change N (0 : E) ≤ 0
        rw [hN0]
      add_mem' := by
        intro x y hx hy
        change N (x.1 + y.1) ≤ x.2 + y.2
        exact (N_add x.1 y.1).trans (add_le_add hx hy)
      smul_mem' := by
        intro c hc x hx
        change N (c • x.1) ≤ c * x.2
        rw [N_hom c hc]
        exact mul_le_mul_of_nonneg_left hx (le_of_lt hc) }
  let D : Submodule ℝ (E × ℝ) :=
    { carrier := {z | z.1 ∈ f.domain}
      zero_mem' := f.domain.zero_mem
      add_mem' := by
        intro x y hx hy
        exact f.domain.add_mem hx hy
      smul_mem' := by
        intro c x hx
        exact f.domain.smul_mem c hx }
  let p₀ : D →ₗ[ℝ] ℝ :=
    { toFun := fun z => z.1.2 - f ⟨z.1.1, z.2⟩
      map_add' := by
        intro x y
        change
          (x.1.2 + y.1.2) -
              f (⟨x.1.1 + y.1.1, _⟩ : f.domain) =
            (x.1.2 - f ⟨x.1.1, x.2⟩) +
              (y.1.2 - f ⟨y.1.1, y.2⟩)
        rw [map_add]
        ring
      map_smul' := by
        intro c x
        change
          c * x.1.2 - f (⟨c • x.1.1, _⟩ : f.domain) =
            c * (x.1.2 - f ⟨x.1.1, x.2⟩)
        rw [map_smul]
        ring }
  let p : (E × ℝ) →ₗ.[ℝ] ℝ := ⟨D, p₀⟩
  have hp_nonneg :
      ∀ x : p.domain, (x : E × ℝ) ∈ C → 0 ≤ p x := by
    intro x hx
    have hxD : x.1.1 ∈ f.domain := by
      simpa [p, D] using x.2
    let xf : f.domain := ⟨x.1.1, hxD⟩
    change N x.1.1 ≤ x.1.2 at hx
    change 0 ≤ x.1.2 - f xf
    exact sub_nonneg.mpr ((hf xf).trans hx)
  have hp_dense :
      ∀ y : E × ℝ, ∃ x : p.domain, (x : E × ℝ) + y ∈ C := by
    intro y
    refine ⟨⟨(0, N y.1 - y.2), ?_⟩, ?_⟩
    · change (0 : E) ∈ f.domain
      exact f.domain.zero_mem
    · change N ((0 : E) + y.1) ≤ (N y.1 - y.2) + y.2
      simp
  obtain ⟨q, hqp, hqdom, hqpos⟩ :=
    provided_exists_top C p hp_nonneg hp_dense
  rcases hqp with ⟨hdom, hagree⟩
  have htop : ∀ z : E × ℝ, z ∈ q.domain := by
    intro z
    rw [hqdom]
    exact Submodule.mem_top
  let Q : (E × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => q ⟨z, htop z⟩
      map_add' := by
        intro x y
        simpa only using
          q.toLinearMap.map_add
            (⟨x, htop x⟩ : q.domain)
            (⟨y, htop y⟩ : q.domain)
      map_smul' := by
        intro c x
        simpa only using
          q.toLinearMap.map_smul c (⟨x, htop x⟩ : q.domain) }
  have hQ_on (z : p.domain) : Q z.1 = p z := by
    have hz := DFunLike.congr_fun hagree z
    change p z = q ⟨z.1, hdom z.2⟩ at hz
    change q ⟨z.1, htop z.1⟩ = p z
    simpa only using hz.symm
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -Q (x, 0)
      map_add' := by
        intro x y
        change -Q ((x, 0) + (y, 0)) = -Q (x, 0) + -Q (y, 0)
        rw [map_add, neg_add_rev]
        rw [add_comm]
      map_smul' := by
        intro c x
        change -Q (c • (x, 0)) = c • (-Q (x, 0))
        rw [map_smul]
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    let z : p.domain := ⟨(x.1, 0), by
      change x.1 ∈ f.domain
      exact x.2⟩
    have hz := hQ_on z
    change Q (x.1, 0) = 0 - f x at hz
    change -Q (x.1, 0) = f x
    linarith
  · intro x
    have hpos : 0 ≤ Q (x, N x) := by
      apply hqpos (x := ⟨(x, N x), htop (x, N x)⟩)
      change N x ≤ N x
      exact le_rfl
    have hQt : Q (0, N x) = N x := by
      let z : p.domain := ⟨(0, N x), by
        change (0 : E) ∈ f.domain
        exact f.domain.zero_mem⟩
      have hz := hQ_on z
      change Q (0, N x) = N x - f (0 : f.domain) at hz
      simpa using hz
    have hsplit :
        Q (x, N x) = Q (x, 0) + Q (0, N x) := by
      simpa using Q.map_add (x, 0) (0, N x)
    change -Q (x, 0) ≤ N x
    rw [hsplit, hQt] at hpos
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth2
