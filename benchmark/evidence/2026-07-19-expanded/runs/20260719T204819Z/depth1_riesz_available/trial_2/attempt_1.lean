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
  have N_zero : N (0 : E) = 0 := by
    have h := N_hom (2 : ℝ) (by norm_num) (0 : E)
    have h' : N (0 : E) = 2 * N (0 : E) := by
      simpa using h
    linarith
  let C : ConvexCone ℝ (E × ℝ) where
    carrier := {z | z = 0 ∨ N z.1 < z.2}
    zero_mem' := Or.inl rfl
    add_mem' := by
      intro z w hz hw
      change z = 0 ∨ N z.1 < z.2 at hz
      change w = 0 ∨ N w.1 < w.2 at hw
      rcases hz with rfl | hz
      · simpa using hw
      rcases hw with rfl | hw
      · simpa using hz
      right
      change N (z.1 + w.1) < z.2 + w.2
      exact lt_of_le_of_lt (N_add _ _) (add_lt_add hz hw)
    smul_mem' := by
      intro c hc z hz
      change z = 0 ∨ N z.1 < z.2 at hz
      by_cases hcz : c = 0
      · subst c
        left
        simp
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
      rcases hz with rfl | hz
      · left
        simp
      right
      simpa [N_hom c hcpos, smul_eq_mul] using
        (mul_lt_mul_of_pos_left hz hcpos)
  let s : PointedCone ℝ (E × ℝ) :=
    ⟨C, by
      intro z hz hnz
      change z = 0 ∨ N z.1 < z.2 at hz
      change -z = 0 ∨ N (-z).1 < (-z).2 at hnz
      rcases hz with hz | hz
      · exact hz
      rcases hnz with hnz | hnz
      · simpa using hnz
      have hnz' : N (-z.1) < -z.2 := by
        simpa using hnz
      have hsum : 0 ≤ N z.1 + N (-z.1) := by
        simpa [N_zero] using N_add z.1 (-z.1)
      exfalso
      linarith⟩
  let d : Submodule ℝ (E × ℝ) := f.domain.prod ⊤
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    ⟨d,
      { toFun := fun z => z.1.2 - f ⟨z.1.1, z.2.1⟩
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro c x
          simp [smul_eq_mul] }⟩
  obtain ⟨G, hGF, hGpos⟩ :=
    provided_riesz_extension s F
      (by
        intro x hx
        change x.1 = 0 ∨ N x.1.1 < x.1.2 at hx
        rcases hx with hx | hx
        · have hx0 : x = 0 := by
            apply Subtype.ext
            exact hx
          rw [hx0]
          simp
        · have xmem : x.1.1 ∈ f.domain := x.2.1
          have hfx := hf ⟨x.1.1, xmem⟩
          change 0 ≤ x.1.2 - f ⟨x.1.1, xmem⟩
          linarith)
      (by
        intro y
        let z : E × ℝ := (0, N y.1 - y.2 + 1)
        have hzdom : z ∈ d := by
          simp [z, d]
        refine ⟨(⟨z, hzdom⟩ : F.domain), ?_⟩
        change z + y = 0 ∨ N (z + y).1 < (z + y).2
        right
        dsimp [z]
        linarith)
  have hvert (r : ℝ) : G ((0 : E), r) = r := by
    let z : E × ℝ := (0, r)
    have hzdom : z ∈ d := by
      simp [z, d]
    have h := hGF (⟨z, hzdom⟩ : F.domain)
    simpa [F, z] using h
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -G (x, 0)
      map_add' := by
        intro x y
        change -G (x + y, 0) = -G (x, 0) + -G (y, 0)
        rw [show (x + y, (0 : ℝ)) = (x, 0) + (y, 0) by simp, G.map_add]
        simp
      map_smul' := by
        intro c x
        change -G (c • x, 0) = c • (-G (x, 0))
        rw [show (c • x, (0 : ℝ)) = c • (x, 0) by simp, G.map_smul]
        simp [smul_eq_mul] }
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hzdom : ((x : E), (0 : ℝ)) ∈ d := by
      simp [d, x.property]
    have h := hGF
      (⟨((x : E), (0 : ℝ)), hzdom⟩ : F.domain)
    dsimp [g]
    simpa [F] using congrArg Neg.neg h
  · intro x
    by_contra hle
    have hlt : N x < g x := lt_of_not_ge hle
    let ε : ℝ := (g x - N x) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hpair : (x, N x + ε) ∈ s := by
      change (x, N x + ε) = 0 ∨ N x < N x + ε
      right
      linarith
    have hp := hGpos (x, N x + ε) hpair
    have hcalc :
        G (x, N x + ε) = G (x, 0) + (N x + ε) := by
      calc
        G (x, N x + ε) =
            G ((x, 0) + ((0 : E), N x + ε)) := by simp
        _ = G (x, 0) + G ((0 : E), N x + ε) := G.map_add _ _
        _ = G (x, 0) + (N x + ε) := by rw [hvert]
    have hbound : g x ≤ N x + ε := by
      dsimp [g]
      rw [hcalc] at hp
      linarith
    dsimp [ε] at hbound
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth1
