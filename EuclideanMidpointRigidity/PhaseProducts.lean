module

public import EuclideanMidpointRigidity.LeadingComposition
public import EuclideanMidpointRigidity.GeodesicForceJets

/-! # Spatial and velocity derivatives of the geodesic acceleration -/

@[expose] public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d
local notation "H" => E × E

structure PhaseProduct (d : ℕ) where
  spatial : List (Space d)
  left : Option (Space d)
  right : Option (Space d)

namespace PhaseProduct

def value (s : PhaseProduct d) (D : E → T) (q : H) :=
  K (directions D s.spatial q.1) (s.left.getD q.2) (s.right.getD q.2)

def derivative (s : PhaseProduct d) (w : H) : List (PhaseProduct d) :=
  [{s with spatial := w.1::s.spatial}]++
  (if s.left.isNone then [{s with left := some w.2}] else [])++
  (if s.right.isNone then [{s with right := some w.2}] else [])

def sumValue (ss : List (PhaseProduct d)) (D : E → T) (q : H) := (ss.map (fun s ↦ s.value D q)).sum

def terms : List H → List (PhaseProduct d)
  | [] => [⟨[],none,none⟩]
  | w::ws => (terms ws).flatMap (fun s ↦ s.derivative w)

private theorem slot_smooth (o : Option E) : ContDiff ℝ ∞ (fun q : H ↦ o.getD q.2) := by
  cases o with
  | none => exact contDiff_snd
  | some z => exact contDiff_const

theorem smooth {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W) (s : PhaseProduct d) :
    ContDiffOn ℝ ∞ (s.value D) (Prod.fst ⁻¹' W : Set H) := by
  let L : T →L[ℝ] E →L[ℝ] E →L[ℝ] E := (cubicSubspace d).subtypeL
  have hc := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) («E» := T) (F := E →L[ℝ] E →L[ℝ] E) L
  have h := ContDiff.comp_contDiffOn («E» := E) (F := T) (G := E →L[ℝ] E →L[ℝ] E) hc (directions.smooth hW hD s.spatial)
  have hh := h.comp (contDiffOn_fst (s := (Prod.fst ⁻¹' W : Set H))) (fun _ hv ↦ hv)
  exact (hh.clm_apply (slot_smooth s.left).contDiffOn).clm_apply (slot_smooth s.right).contDiffOn

private theorem slot_rate (o : Option E) (v w : E) :
    HasDerivAt (fun t : ℝ ↦ o.getD (v+t • w)) (if o.isNone then w else 0) 0 := by
  cases o with
  | some z => exact hasDerivAt_const 0 z
  | none => simpa only [Option.getD,Option.isNone,ite_true,one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add v

theorem rate {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W)
    (s : PhaseProduct d) {q : H} (hq : q.1 ∈ W) (w : H) :
    directional (s.value D) w q=sumValue (s.derivative w) D q := by
  let line := fun t : ℝ ↦ q+t • w
  have hl : HasDerivAt line w 0 := by simpa only [line,one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add q
  have h₀ : line 0=q := by simp [line]
  have hg := ((smooth hW hD s).contDiffAt ((hW.preimage continuous_fst).mem_nhds hq)).differentiableAt (by simp)
  have whole := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl h₀.symm
  have dx : HasDerivAt (fun t : ℝ ↦ q.1+t • w.1) w.1 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const w.1).const_add q.1
  have hd := (((directions.smooth hW hD s.spatial).contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 dx (by simp)
  have h := hasDerivAt_K hd (slot_rate s.left q.2 w.2) (slot_rate s.right q.2 w.2)
  have he := whole.unique h
  rcases s with ⟨xs,left,right⟩
  cases left <;> cases right <;>
    simpa [directional,sumValue,derivative,value,directions,Function.comp_def,K,add_assoc] using he

theorem sum_smooth {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W) (ss : List (PhaseProduct d)) :
    ContDiffOn ℝ ∞ (sumValue ss D) (Prod.fst ⁻¹' W : Set H) := by
  induction ss with
  | nil => exact contDiffOn_const
  | cons s ss ih => exact (smooth hW hD s).add ih

theorem sum_rate {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W)
    (ss : List (PhaseProduct d)) {q : H} (hq : q.1 ∈ W) (w : H) :
    directional (sumValue ss D) w q=sumValue (ss.flatMap (fun s ↦ s.derivative w)) D q := by
  induction ss with
  | nil => change fderiv ℝ (fun _ : H ↦ (0:E)) q w=0; rw [(hasFDerivAt_const (0:E) q).fderiv,zero_apply]
  | cons s ss ih =>
    have hv := directions.add (hW.preimage continuous_fst) (smooth hW hD s) (sum_smooth hW hD ss) [w] hq
    change directional (fun q ↦ s.value D q+sumValue ss D q) w q=directional (s.value D) w q+directional (sumValue ss D) w q at hv
    rw [rate hW hD s hq w,ih] at hv
    change directional (fun x ↦ s.value D x+sumValue ss D x) w q=sumValue ((s::ss).flatMap (fun s ↦ s.derivative w)) D q
    simpa only [sumValue,List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons] using hv

theorem jet_formula {W : Set E} {D : E → T} (hW : IsOpen W) (hD : ContDiffOn ℝ ∞ D W) (xs : List H) :
    EqOn (directions (fun q : H ↦ K (D q.1) q.2 q.2) xs) (sumValue (terms xs) D) (Prod.fst ⁻¹' W) := by
  induction xs with
  | nil => intro q _; simp [terms,sumValue,value,directions]
  | cons w xs ih =>
    intro q hq
    have he : directions (fun q : H ↦ K (D q.1) q.2 q.2) xs =ᶠ[𝓝 q] sumValue (terms xs) D :=
      (show ∀ᶠ x in 𝓝 q, x ∈ (Prod.fst ⁻¹' W : Set H) from (hW.preimage continuous_fst).mem_nhds hq).mono fun _ hx ↦ ih hx
    exact (DFunLike.congr_fun he.fderiv_eq w).trans (sum_rate hW hD _ hq w)

end PhaseProduct
end EuclideanMidpointRigidity

