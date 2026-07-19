import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth3

open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 3. -/
axiom provided_step (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

lemma exists_maximal_positive (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (hf : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) :
    ∃ g, f ≤ g ∧
      (∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x) ∧
      ∀ h, g < h → ¬∀ x : h.domain, (x : E) ∈ s → 0 ≤ h x :=
  LinearPMap.exists_maximal f
    (fun x y => x ∈ s → 0 ≤ y) hf

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  classical
  have N_zero : N (0 : E) = 0 := by
    have h := N_hom 2 (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {z | N z.1 ≤ z.2}
      zero_mem' := by
        simpa [N_zero]
      add_mem' := by
        rintro ⟨x, a⟩ ⟨y, b⟩ hx hy
        exact (N_add x y).trans (add_le_add hx hy)
      smul_mem' := by
        intro c hc
        rintro ⟨x, a⟩ hx
        rcases hc.eq_or_lt with rfl | hc
        · simpa [N_zero]
        · simpa [N_hom c hc x] using mul_le_mul_of_nonneg_left hx hc.le }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toLinearMap :=
        { toFun := fun z => z.1.2 - f ⟨z.1.1, z.2.1⟩
          map_add' := by
            intro x y
            simp
            ring
          map_smul' := by
            intro c x
            simp
            ring } }
  have hF : ∀ z : F.domain, (z : E × ℝ) ∈ s → 0 ≤ F z := by
    intro z hz
    rcases z with ⟨⟨x, a⟩, hx⟩
    change N x ≤ a at hz
    change 0 ≤ a - f ⟨x, hx.1⟩
    exact sub_nonneg.mpr ((hf ⟨x, hx.1⟩).trans hz)
  obtain ⟨G, hFG, hG, hmax⟩ := exists_maximal_positive s F hF
  have hGtop : G.domain = ⊤ := by
    by_contra hne
    have hdense : ∀ y, ∃ x : G.domain, (x : E × ℝ) + y ∈ s := by
      rintro ⟨y, b⟩
      let z : F.domain :=
        ⟨(0, N y - b), by
          constructor
          · exact zero_mem f.domain
          · exact Submodule.mem_top⟩
      let x : G.domain := ⟨(z : E × ℝ), hFG.1 z.2⟩
      refine ⟨x, ?_⟩
      change N (0 + y) ≤ (N y - b) + b
      linarith
    obtain ⟨H, hGH, hH⟩ := provided_step s G hG hdense hne
    exact (hmax H hGH) hH
  let inc : (E × ℝ) →ₗ[ℝ] G.domain :=
    { toFun := fun z => ⟨z, by rw [hGtop]; exact Submodule.mem_top⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  let L : (E × ℝ) →ₗ[ℝ] ℝ := G.toLinearMap.comp inc
  have hLF (z : F.domain) : L (z : E × ℝ) = F z := by
    exact (hFG.2 z).symm
  have hLone : L (0, 1) = 1 := by
    let z : F.domain :=
      ⟨(0, 1), by
        constructor
        · exact zero_mem f.domain
        · exact Submodule.mem_top⟩
    simpa [F] using hLF z
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -L (x, 0)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    let z : F.domain :=
      ⟨((x : E), 0), by
        constructor
        · exact x.2
        · exact Submodule.mem_top⟩
    have hz := hLF z
    change -L ((x : E), 0) = f x
    simpa [F] using congrArg Neg.neg hz
  · intro x
    have hs : ((x, N x) : E × ℝ) ∈ s := le_rfl
    have hp : 0 ≤ L (x, N x) := hG (inc (x, N x)) hs
    have hsplit : L (x, N x) = L (x, 0) + N x := by
      rw [show (x, N x) = (x, 0) + N x • (0, 1) by ext <;> simp]
      simp [hLone]
    change -L (x, 0) ≤ N x
    rw [hsplit] at hp
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth3
