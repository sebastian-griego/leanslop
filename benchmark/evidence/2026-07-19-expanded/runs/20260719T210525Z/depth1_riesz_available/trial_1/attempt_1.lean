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
  classical
  have hN_zero : N (0 : E) = 0 := by
    have h : N (0 : E) = (2 : ℝ) * N (0 : E) := by
      simpa using N_hom (2 : ℝ) (by norm_num) (0 : E)
    nlinarith
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {z | N z.1 ≤ z.2}
      zero_mem' := by
        change N (0 : E) ≤ (0 : ℝ)
        exact le_of_eq hN_zero
      add_mem' := by
        intro x hx y hy
        change N (x.1 + y.1) ≤ x.2 + y.2
        exact le_trans (N_add x.1 y.1) (add_le_add hx hy)
      smul_mem' := by
        intro c hc z hz
        change N (c • z.1) ≤ c * z.2
        by_cases hcz : c = 0
        · subst c
          simp [hN_zero]
        · have hcge : 0 ≤ c := by positivity
          have hcpos : 0 < c := lt_of_le_of_ne hcge (Ne.symm hcz)
          rw [N_hom c hcpos z.1]
          exact mul_le_mul_of_nonneg_left hz hcge }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod (⊤ : Submodule ℝ ℝ)
      toFun := fun x => x.1.2 - f ⟨x.1.1, x.2.1⟩
      map_add' := by
        intro x y
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      map_smul' := by
        intro c x
        simp [mul_sub] }
  have hnonneg : ∀ x : F.domain, (x : E × ℝ) ∈ s → 0 ≤ F x := by
    intro x hx
    have hxN : N x.1.1 ≤ x.1.2 := hx
    have hfx : f ⟨x.1.1, x.2.1⟩ ≤ N x.1.1 := hf _
    change 0 ≤ x.1.2 - f ⟨x.1.1, x.2.1⟩
    nlinarith
  have hdense : ∀ y, ∃ x : F.domain, (x : E × ℝ) + y ∈ s := by
    intro y
    refine ⟨⟨((0 : E), N y.1 - y.2), ?_⟩, ?_⟩
    · exact ⟨zero_mem f.domain, trivial⟩
    · change N y.1 ≤ (N y.1 - y.2) + y.2
      ring_nf
  obtain ⟨G, hGext, hGpos⟩ := provided_riesz_extension s F hnonneg hdense
  have hG01 : G ((0 : E), (1 : ℝ)) = 1 := by
    have h := hGext ⟨((0 : E), (1 : ℝ)), by exact ⟨zero_mem f.domain, trivial⟩⟩
    simpa [F] using h
  refine
    ⟨{ toFun := fun x => -G (x, (0 : ℝ))
       map_add' := by
        intro x y
        change -G ((x + y), (0 : ℝ)) = -G (x, (0 : ℝ)) + -G (y, (0 : ℝ))
        calc
          -G ((x + y), (0 : ℝ)) = -G (((x, (0 : ℝ)) + (y, (0 : ℝ)))) := by simp
          _ = -(G (x, (0 : ℝ)) + G (y, (0 : ℝ))) := by rw [map_add]
          _ = -G (x, (0 : ℝ)) + -G (y, (0 : ℝ)) := by ring
       map_smul' := by
        intro c x
        change -G ((c • x), (0 : ℝ)) = c • (-G (x, (0 : ℝ)))
        calc
          -G ((c • x), (0 : ℝ)) = -G (c • (x, (0 : ℝ))) := by simp
          _ = -(c • G (x, (0 : ℝ))) := by rw [map_smul]
          _ = c • (-G (x, (0 : ℝ))) := by simp },
      ?_,
      ?_⟩
  · intro x
    have h := hGext ⟨((x : E), (0 : ℝ)), by exact ⟨x.2, trivial⟩⟩
    have h' : G ((x : E), (0 : ℝ)) = -f x := by
      simpa [F] using h
    simp [h']
  · intro x
    change -G (x, (0 : ℝ)) ≤ N x
    have hpos : 0 ≤ G (x, N x) := by
      exact hGpos (x, N x) (by change N x ≤ N x; rfl)
    have hsmul : G ((0 : E), N x) = N x := by
      calc
        G ((0 : E), N x) = G ((N x) • ((0 : E), (1 : ℝ))) := by simp
        _ = (N x) • G ((0 : E), (1 : ℝ)) := by rw [map_smul]
        _ = N x := by simp [hG01]
    have hdecomp : G (x, N x) = G (x, (0 : ℝ)) + N x := by
      calc
        G (x, N x) = G ((x, (0 : ℝ)) + ((0 : E), N x)) := by simp
        _ = G (x, (0 : ℝ)) + G ((0 : E), N x) := by rw [map_add]
        _ = G (x, (0 : ℝ)) + N x := by rw [hsmul]
    nlinarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth1
