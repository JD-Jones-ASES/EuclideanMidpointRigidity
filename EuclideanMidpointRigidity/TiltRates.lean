module

public import EuclideanMidpointRigidity.TiltBoundaryJets

/-! # The two spectra allowed by the frozen curvature equations -/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.Endpoint
open BoundaryTest

def boundaryDet {η : ℚ} (P Q : BoundaryTest η) : ℚ :=
  P.jet.coeff 5*Q.jet.coeff 7-P.jet.coeff 7*Q.jet.coeff 5

structure TiltRates (η ν : ℚ) : Prop where
  eta_ne : η≠0
  lambda_ne : ν≠0
  rate₁ : η-2*η-2≠0
  rate₂ : η-2*ν-2≠0
  single₁ : boundaryDet (tilted η 0 η eta_ne) (linear η η eta_ne)≠0
  single₂ : boundaryDet (tilted η 0 ν eta_ne) (linear η ν eta_ne)≠0
  double : boundaryDet (tilted η η ν eta_ne) (tilted η ν η eta_ne)≠0
  triple : (tilted η (η+ν) η eta_ne).jet.coeff 7≠0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1200000 in
theorem rates_two_three : TiltRates 2 3 := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_,?_,?_,?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1200000 in
theorem rates_three_one_fifths : TiltRates (3/5) (1/5) := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_,?_,?_,?_⟩ <;> decide +kernel

end EuclideanMidpointRigidity.Endpoint

