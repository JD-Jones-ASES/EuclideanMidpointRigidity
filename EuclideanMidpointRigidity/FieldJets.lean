module

public import EuclideanMidpointRigidity.AxialSixth
public import EuclideanMidpointRigidity.MultilinearExpansion
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Spatial Hessians and diagonal third derivatives in the tree evaluation -/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace EuclideanMidpointRigidity.Jet

variable {d : ℕ}
local notation "E" => Space d
local notation "Coeff" => Cubic d

theorem field_pair (C : E → Coeff) (p : E) (hC : ContDiffAt ℝ ∞ C p) (u v : E) :
    listForm (fieldDerivatives C p) [u,v] = fderiv ℝ (fderiv ℝ C) p u v := by
  let D := fieldDerivatives C p
  let H := fderiv ℝ (fderiv ℝ C) p
  have hd (x : E) : listForm D [x,x] = H x x := by
    change listForm D (List.replicate 2 x) = _
    rw [listForm_replicate]
    exact iteratedFDeriv_two_apply C p (fun _ ↦ x)
  have h₁ : listForm D [u+v,u+v] = listForm D [u,u+v]+listForm D [v,u+v] :=
    listForm_middle_add D [] [u+v] u v
  have h₂ (x : E) : listForm D [x,u+v] = listForm D [x,u]+listForm D [x,v] :=
    listForm_middle_add D [x] [] u v
  have hswap : listForm D [v,u] = listForm D [u,v] := listForm_perm D (List.Perm.swap u v [])
  have hsym : H v u=H u v := (hC.isSymmSndFDerivAt (by simp)) v u
  have h := hd (u+v)
  rw [h₁,h₂,h₂,hswap,hd u,hd v] at h
  simp only [map_add,ContinuousLinearMap.add_apply,hsym] at h
  change listForm D [u,v] = H u v
  linear_combination (norm := module) (1/2:ℝ) • h

theorem field_triple_diagonal (C : E → Coeff) (p e : E) :
    listForm (fieldDerivatives C p) [e,e,e] = fderiv ℝ (fderiv ℝ (fderiv ℝ C)) p e e e := by
  change listForm (fieldDerivatives C p) (List.replicate 3 e) = _
  rw [listForm_replicate]
  change iteratedFDeriv ℝ (2+1) C p (fun _ ↦ e) = _
  rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_two_apply]
  rfl

end EuclideanMidpointRigidity.Jet
