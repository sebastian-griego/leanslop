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

lemma sublinear_zero (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x) :
    N (0 : E) = 0 := by
  have h : N (0 : E) = (2 : ℝ) * N (0 : E) := by
    simpa using N_hom 2 (by positivity) (0 : E)
  linarith

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  have hN0 : N (0 : E) = 0 := sublinear_zero N N_hom
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {p : E × ℝ | N p.1 ≤ p.2}
      zero_mem' := by
        simpa [hN0]
      add_mem' := by
        intro a b ha hb
        change N (a.1 + b.1) ≤ a.2 + b.2
        exact le_trans (N_add a.1 b.1) (add_le_add ha hb)
      smul_mem' := by
        intro c hc a ha
        change N (c • a.1) ≤ c * a.2
        rw [N_hom c hc a.1]
        nlinarith [ha, hc] }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toFun :=
        { toFun := fun u => u.1.2 - f ⟨u.1.1, u.2.1⟩
          map_add' := by
            intro a b
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          map_smul' := by
            intro c u
            simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] } }
  obtain ⟨G, hGext, hGnonneg⟩ :=
    provided_riesz_extension s F
      (by
        intro u hu
        have hfu : f ⟨u.1.1, u.2.1⟩ ≤ N u.1.1 := hf ⟨u.1.1, u.2.1⟩
        have hnon : 0 ≤ u.1.2 - f ⟨u.1.1, u.2.1⟩ := by
          linarith [hfu, hu]
        simpa [F] using hnon)
      (by
        intro y
        refine ⟨⟨((0 : E), N y.1 - y.2), by simp⟩, ?_⟩
        change N y.1 ≤ (N y.1 - y.2) + y.2
        linarith)
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -G ((x : E), (0 : ℝ))
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp [mul_comm, mul_left_comm, mul_assoc] }
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hx0 : G ((x : E), (0 : ℝ)) = -f x := by
      have h := hGext ⟨((x : E), (0 : ℝ)), by simp [x.property]⟩
      simpa [F] using h
    simpa [g, hx0]
  · intro x
    have h01 : G ((0 : E), (1 : ℝ)) = 1 := by
      have h := hGext ⟨((0 : E), (1 : ℝ)), by simp⟩
      simpa [F] using h
    have hpos : 0 ≤ G (x, N x) := by
      apply hGnonneg
      change N x ≤ N x
      exact le_rfl
    have hsmul : G ((0 : E), N x) = N x * G ((0 : E), (1 : ℝ)) := by
      have hs : ((0 : E), N x) = N x • ((0 : E), (1 : ℝ)) := by
        ext <;> simp
      rw [hs]
      simp
    have hdecomp : G (x, N x) = G ((x : E), (0 : ℝ)) + N x := by
      have hpair : (x, N x) = ((x : E), (0 : ℝ)) + ((0 : E), N x) := by
        ext <;> simp
      rw [hpair, map_add, hsmul, h01]
      simp
    have hle : -G ((x : E), (0 : ℝ)) ≤ N x := by
      have : 0 ≤ G ((x : E), (0 : ℝ)) + N x := by
        simpa [hdecomp] using hpos
      linarith
    simpa [g] using hle


#print axioms tested_hahn_banach

end Depth1
