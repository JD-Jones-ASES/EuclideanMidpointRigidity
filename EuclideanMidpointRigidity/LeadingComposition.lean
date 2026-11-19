module

public import EuclideanMidpointRigidity.FlatProduct

/-! # The leading derivative after a smooth change of variables -/

public section
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace EuclideanMidpointRigidity.directions
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem leading_comp {U : Set E} {V : Set F} {f : E → F} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f U) (hm : MapsTo f U V) {p : E} (hp : p ∈ U)
    (xs : List E) {g : F → G} (hg : ContDiffOn ℝ ∞ g V)
    (hz : ∀ ys : List F, ys.length<xs.length → directions g ys (f p)=0) :
    directions (g ∘ f) xs p=directions g (xs.map (fderiv ℝ f p)) (f p) := by
  let L := fderiv ℝ f p
  have h (n : ℕ) : ∀ (xs : List E), xs.length=n → ∀ (g : F → G), ContDiffOn ℝ ∞ g V →
      (∀ ys : List F, ys.length<n → directions g ys (f p)=0) →
      directions (g ∘ f) xs p=directions g (xs.map L) (f p) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro xs hlen g hg hz
      cases xs using List.reverseRecOn with
      | nil => rfl
      | append_singleton xs w =>
        have hlen' : xs.length+1=n := by simpa using hlen
        let A := fderiv ℝ g ∘ f
        let v := directional f w
        have hA : ContDiffOn ℝ ∞ A U := (hg.fderiv_of_isOpen hV (by simp)).comp hf hm
        have hv : ContDiffOn ℝ ∞ v U := smooth hU hf [w]
        have he : directional (g ∘ f) w =ᶠ[𝓝 p] (fun x ↦ A x (v x)) :=
          (show ∀ᶠ x in 𝓝 p, x ∈ U from hU.mem_nhds hp).mono fun x hx ↦
            DFunLike.congr_fun (((hg.contDiffAt (hV.mem_nhds (hm hx))).differentiableAt (by simp)).hasFDerivAt.comp x
              ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv w
        have coeff (ys : List E) (hy : ys.length<n) (z : F) :
            directions A ys p z=directions g (ys.map L++[z]) (f p) := by
          let M := ContinuousLinearMap.apply ℝ G z
          have heval := linear_map hU hA M ys hp
          have hi := ih ys.length hy ys rfl (directional g z) (smooth hV hg [z]) (fun ts ht ↦ by
            change directions (directions g [z]) ts (f p)=0
            rw [← append]
            exact hz _ (by simp only [List.length_append,List.length_singleton]; omega))
          rw [append]
          exact heval.symm.trans hi
        have hl (ys : List E) (hy : ys.length<xs.length) : directions A ys p=0 := by
          ext z : 1
          rw [coeff ys (by omega)]
          exact hz _ (by simp only [List.length_append,List.length_map,List.length_singleton]; omega)
        rw [append,List.map_append]
        change directions (directional (g ∘ f) w) xs p=directions g (xs.map L++[L w]) (f p)
        rw [(congr_germ he xs).eq_of_nhds,leading_apply hU hp xs hA hv hl]
        exact coeff xs (by omega) (L w)
  exact h _ xs rfl g hg hz

end EuclideanMidpointRigidity.directions

