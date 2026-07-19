import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth4

open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

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
  let S : Set (Submodule ℝ (E × ℝ)) :=
    {G |
      (∀ b : ℝ, (0, b) ∈ G → b = 0) ∧
      (∀ x : f.domain, ((x : E), f x) ∈ G) ∧
      (∀ p : E × ℝ, p ∈ G → p.2 ≤ N p.1)}
  let q : f.domain →ₗ[ℝ] E × ℝ :=
    { toFun := fun x => ((x : E), f x)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro c x
        ext <;> simp }
  let G₀ : Submodule ℝ (E × ℝ) := LinearMap.range q
  have hG₀ : G₀ ∈ S := by
    simp only [S, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      rcases hb with ⟨x, hx⟩
      change ((x : E), f x) = (0, b) at hx
      have hx₀ : (x : E) = 0 := congrArg Prod.fst hx
      have : x = 0 := Subtype.ext hx₀
      subst x
      simpa using congrArg Prod.snd hx
    · intro x
      exact ⟨x, rfl⟩
    · intro p hp
      rcases hp with ⟨x, rfl⟩
      exact hf x
  have hSne : S.Nonempty := ⟨G₀, hG₀⟩
  have hchain :
      ∀ c : Set (Submodule ℝ (E × ℝ)), c ⊆ S →
        IsChain (· ≤ ·) c → c.Nonempty →
        ∃ H ∈ S, ∀ G ∈ c, G ≤ H := by
    intro c hcS hcc hcne
    let H : Submodule ℝ (E × ℝ) :=
      { carrier := {p | ∃ G ∈ c, p ∈ G}
        zero_mem' := by
          rcases hcne with ⟨G, hGc⟩
          exact ⟨G, hGc, G.zero_mem⟩
        add_mem' := by
          rintro p r ⟨G, hGc, hp⟩ ⟨K, hKc, hr⟩
          rcases hcc.total hGc hKc with hGK | hKG
          · exact ⟨K, hKc, K.add_mem (hGK hp) hr⟩
          · exact ⟨G, hGc, G.add_mem hp (hKG hr)⟩
        smul_mem' := by
          rintro a p ⟨G, hGc, hp⟩
          exact ⟨G, hGc, G.smul_mem a hp⟩ }
    have hHS : H ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        rcases hb with ⟨G, hGc, hb⟩
        have hGS := hcS hGc
        simp only [S, Set.mem_setOf_eq] at hGS
        exact hGS.1 b hb
      · intro x
        rcases hcne with ⟨G, hGc⟩
        have hGS := hcS hGc
        simp only [S, Set.mem_setOf_eq] at hGS
        exact ⟨G, hGc, hGS.2.1 x⟩
      · intro p hp
        rcases hp with ⟨G, hGc, hp⟩
        have hGS := hcS hGc
        simp only [S, Set.mem_setOf_eq] at hGS
        exact hGS.2.2 p hp
    refine ⟨H, hHS, ?_⟩
    intro G hGc p hp
    exact ⟨G, hGc, hp⟩
  obtain ⟨G, hGS, hGmax⟩ :=
    zorn_le_nonempty hchain hSne
  simp only [S, Set.mem_setOf_eq] at hGS
  rcases hGS with ⟨hfun, hinc, hdom⟩
  have hproj : ∀ x : E, ∃ b : ℝ, (x, b) ∈ G := by
    intro x
    by_contra hx
    have hx' : ∀ b : ℝ, (x, b) ∉ G := by
      simpa only [not_exists] using hx
    let L : Set ℝ := {r | ∃ y b, (y, b) ∈ G ∧ r = b - N (y - x)}
    have hLne : L.Nonempty := by
      refine ⟨-N (-x), ?_⟩
      refine ⟨0, 0, G.zero_mem, ?_⟩
      simp
    have hLbdd : BddAbove L := by
      refine ⟨N x, ?_⟩
      intro r hr
      rcases hr with ⟨y, b, hyb, rfl⟩
      have hb : b ≤ N y := hdom (y, b) hyb
      have hn := N_add (y - x) x
      have heq : y - x + x = y := by abel
      rw [heq] at hn
      linarith
    let a : ℝ := sSup L
    have hlower (y : E) (b : ℝ) (hyb : (y, b) ∈ G) :
        b - N (y - x) ≤ a := by
      apply le_csSup hLbdd
      exact ⟨y, b, hyb, rfl⟩
    have haupper (y : E) (b : ℝ) (hyb : (y, b) ∈ G) :
        a ≤ N (y + x) - b := by
      apply csSup_le hLne
      intro r hr
      rcases hr with ⟨z, d, hzd, rfl⟩
      have hsum : d + b ≤ N (z + y) :=
        hdom (z + y, d + b) (by
          simpa using G.add_mem hzd hyb)
      have hn := N_add (z - x) (y + x)
      have heq : z - x + (y + x) = z + y := by abel
      rw [heq] at hn
      linarith
    have hu (y : E) (b : ℝ) (hyb : (y, b) ∈ G) :
        b + a ≤ N (y + x) := by
      linarith [haupper y b hyb]
    have hl (y : E) (b : ℝ) (hyb : (y, b) ∈ G) :
        b - a ≤ N (y - x) := by
      linarith [hlower y b hyb]
    let φ : (G × ℝ) →ₗ[ℝ] E × ℝ :=
      { toFun := fun u =>
          (u.1.1.1 + u.2 • x, u.1.1.2 + u.2 * a)
        map_add' := by
          intro u v
          ext <;> simp [add_smul, add_mul]
        map_smul' := by
          intro c u
          ext <;> simp [smul_add, mul_smul, mul_assoc, mul_add] }
    let H : Submodule ℝ (E × ℝ) := LinearMap.range φ
    have hGH : G ≤ H := by
      intro p hp
      refine ⟨(⟨p, hp⟩, 0), ?_⟩
      simp [φ]
    have hxa : (x, a) ∈ H := by
      refine ⟨(⟨0, G.zero_mem⟩, 1), ?_⟩
      simp [φ]
    have hHfun : ∀ b : ℝ, (0, b) ∈ H → b = 0 := by
      intro b hb
      rcases hb with ⟨u, hu⟩
      rcases u with ⟨v, c⟩
      change (v.1.1 + c • x, v.1.2 + c * a) = (0, b) at hu
      have hfirst : v.1.1 + c • x = 0 := congrArg Prod.fst hu
      have hc : c = 0 := by
        by_contra hc
        have hvx : v.1.1 = (-c) • x := by
          apply add_right_cancel (b := c • x)
          simpa [← add_smul] using hfirst
        apply hx' ((-c)⁻¹ * v.1.2)
        have hw := G.smul_mem ((-c)⁻¹) v.2
        convert hw using 1
        ext
        · rw [hvx, smul_smul]
          simp [hc]
        · simp
      subst c
      have hvzero : v.1.1 = 0 := by simpa using hfirst
      have hv₂ : v.1.2 = 0 := by
        apply hfun v.1.2
        convert v.2 using 1
        ext
        · exact hvzero.symm
        · rfl
      simpa [hv₂] using congrArg Prod.snd hu
    have hHdom : ∀ p : E × ℝ, p ∈ H → p.2 ≤ N p.1 := by
      intro p hp
      rcases hp with ⟨u, rfl⟩
      rcases u with ⟨v, c⟩
      change v.1.2 + c * a ≤ N (v.1.1 + c • x)
      rcases lt_trichotomy c 0 with hc | hc | hc
      · let d : ℝ := -c
        have hd : 0 < d := by dsimp [d]; linarith
        let w : G := ⟨d⁻¹ • v.1, G.smul_mem d⁻¹ v.2⟩
        have hw := hl w.1.1 w.1.2 w.2
        have heq : d • (d⁻¹ • v.1.1 - x) = v.1.1 + c • x := by
          simp [d, smul_sub, smul_smul, hd.ne', sub_eq_add_neg]
        have hn := N_hom d hd (d⁻¹ • v.1.1 - x)
        rw [heq] at hn
        have hdi : d * (d⁻¹ * v.1.2) = v.1.2 := by
          field_simp
        change d⁻¹ * v.1.2 - a ≤ N (d⁻¹ • v.1.1 - x) at hw
        dsimp [d] at hd hn hdi ⊢
        nlinarith
      · subst c
        simpa using hdom v.1 v.2
      · let w : G := ⟨c⁻¹ • v.1, G.smul_mem c⁻¹ v.2⟩
        have hw := hu w.1.1 w.1.2 w.2
        have heq : c • (c⁻¹ • v.1.1 + x) = v.1.1 + c • x := by
          simp [smul_add, smul_smul, hc.ne']
        have hn := N_hom c hc (c⁻¹ • v.1.1 + x)
        rw [heq] at hn
        have hci : c * (c⁻¹ * v.1.2) = v.1.2 := by
          field_simp
        change c⁻¹ * v.1.2 + a ≤ N (c⁻¹ • v.1.1 + x) at hw
        nlinarith
    have hHS : H ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      refine ⟨hHfun, ?_, hHdom⟩
      intro y
      exact hGH (hinc y)
    have hHG : H ≤ G := hGmax H hHS hGH
    exact hx' a (hHG hxa)
  let val : E → ℝ := fun x => Classical.choose (hproj x)
  have hval (x : E) : (x, val x) ∈ G :=
    Classical.choose_spec (hproj x)
  have huniq (x : E) (b c : ℝ)
      (hb : (x, b) ∈ G) (hc : (x, c) ∈ G) : b = c := by
    have hsub : (0, b - c) ∈ G := by
      have := G.sub_mem hb hc
      simpa using this
    have := hfun (b - c) hsub
    linarith
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := val
      map_add' := by
        intro x y
        apply huniq (x + y)
        · exact hval (x + y)
        · simpa using G.add_mem (hval x) (hval y)
      map_smul' := by
        intro c x
        apply huniq (c • x)
        · exact hval (c • x)
        · simpa using G.smul_mem c (hval x) }
  refine ⟨g, ?_, ?_⟩
  · intro x
    change val x = f x
    exact huniq x (val x) (f x) (hval x) (hinc x)
  · intro x
    change val x ≤ N x
    exact hdom (x, val x) (hval x)


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth4
