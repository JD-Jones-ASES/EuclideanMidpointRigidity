module

public import EuclideanMidpointRigidity.CoupledWeights
public import EuclideanMidpointRigidity.FixedFactorRows
public import EuclideanMidpointRigidity.SymmetricJet

/-! # The cubic Killing equation when the derivative vanishes on the kernel of the axis slice -/

public section
noncomputable section
open scoped InnerProductSpace
namespace EuclideanMidpointRigidity.FixedAxis
open Quartic
variable {d : ℕ}
local notation "E" => Space d
local notation "T" => Cubic d

theorem eigen_mixed {c : T} {J : E →L[ℝ] T} {u x y z w : E} {a b s t : ℝ}
    (hQ : ∀ v, obstruction c J v=0) (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0)
    (hx : K c u x=a • x) (hy : K c u y=b • y) (hz : K c u z=s • z) (hw : K c u w=t • w) :
    mixedWeight a b s t (jetEntry J x y z w) (jetEntry J y x z w) (jetEntry J z x y w)=0 := by
  have h := polar_weight (entryForm J w) (c.val u).toLinearMap t (entry_swap J w)
    (weighted_row hQ hu hJ hw) hx hy hz
  change mixedWeight a b s t (jetEntry J x w y z) (jetEntry J y w x z) (jetEntry J z w x y)=0 at h
  simpa only [jetEntry_swap₁,jetEntry_swap₂] using h

theorem killing_of_slice_kernel {c : T} {J : E →L[ℝ] T} {u : E} (F : SliceFrame c u)
    (hQ : ∀ v, obstruction c J v=0) (hu : J u=0) (hJ : ∀ l v, K (J l) u v=0)
    (hk : ∀ l, K c u l=0 → J l=0) (v : E) : directionProfile v (J v)=0 := by
  apply killing_of_symJet_basis F.basis.toBasis _ v
  intro i j k l
  let x := F.basis i
  let y := F.basis j
  let z := F.basis k
  let w := F.basis l
  let a := F.eigenvalue i
  let b := F.eigenvalue j
  let s := F.eigenvalue k
  let t := F.eigenvalue l
  have hx : K c u x=a • x := F.eigen i
  have hy : K c u y=b • y := F.eigen j
  have hz : K c u z=s • z := F.eigen k
  have hw : K c u w=t • w := F.eigen l
  have he := symJet_of_killing (J := J.comp (c.val u)) (weighted_killing hQ hu hJ) x y z w
  have eigen_zero {q : ℝ} {n : E} (hn : K c u n=q • n) (hq : q=0) (i j k : E) :
      jetEntry J n i j k=0 := by
    have h₀ := hk n (by simpa only [hq,zero_smul] using hn)
    simp [jetEntry,cubicEntry,h₀,K]
  change jetEntry J x y z w+jetEntry J y x z w+jetEntry J z x y w+jetEntry J w x y z=0
  apply four_weights (a := a) (b := b) (c := s) (d := t)
  · exact eigen_mixed hQ hu hJ hx hy hz hw
  · simpa only [jetEntry_swap₁,jetEntry_swap₂] using eigen_mixed hQ hu hJ hy hz hw hx
  · simpa only [jetEntry_swap₁,jetEntry_swap₂] using eigen_mixed hQ hu hJ hz hw hx hy
  · simpa only [jetEntry_swap₁,jetEntry_swap₂] using eigen_mixed hQ hu hJ hw hx hy hz
  · change jetEntry J (K c u x) y z w+jetEntry J (K c u y) x z w+
      jetEntry J (K c u z) x y w+jetEntry J (K c u w) x y z=0 at he
    rw [hx,hy,hz,hw] at he
    simpa only [jetEntry,cubicEntry,map_smul,K_smul_coeff,real_inner_smul_left] using he
  · exact fun h ↦ eigen_zero hx h _ _ _
  · exact fun h ↦ eigen_zero hy h _ _ _
  · exact fun h ↦ eigen_zero hz h _ _ _
  · exact fun h ↦ eigen_zero hw h _ _ _

end EuclideanMidpointRigidity.FixedAxis

