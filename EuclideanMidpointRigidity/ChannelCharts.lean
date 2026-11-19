module

public import EuclideanMidpointRigidity.MixedChannel

/-! # Polynomial coordinates of the external channel equations

The regular chart uses the two cubic components as free coordinates.
The angular chart uses the two frame derivatives. Each displayed identity is a
polynomial linear combination of the same nine raw equations.
-/

@[expose] public section
noncomputable section
namespace EuclideanMidpointRigidity.MixedChannel
set_option maxHeartbeats 1500000

def regularDenominator (s : ℝ) : ℝ := (s - 1)*(2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(170*s^2 + 16*s + 93)

def regular_q (s l h : ℝ) : ℝ :=
  (- 25*(2*s - 1)^2*(348000*s^5 - 349980*s^4 - 11446*s^3 + 307417*s^2 - 225665*s + 26930)/72)*l + (- 1625*(s - 1)*(2*s - 1)*(2*s + 1)*(25*s^2 - 45*s + 11)*(30*s^2 + 18*s - 41)/18)*h

def regular_r1w (s l h : ℝ) : ℝ :=
  (5*(2*s - 1)*(4225000*s^5 - 1759000*s^4 + 6231710*s^3 - 4747193*s^2 - 1018131*s + 401574)/468)*l + (125*(s - 1)*(2*s + 1)*(25*s^2 - 45*s + 11)*(130*s^2 - 174*s + 93)/9)*h

def regular_rw1 (s l h : ℝ) : ℝ :=
  (25*(2*s - 1)*(1541500*s^5 + 687210*s^4 + 217762*s^3 - 1268325*s^2 - 19949*s + 80130)/468)*l + (- 125*(s - 1)*(2*s + 1)*(10*s^2 + 76*s - 177)*(25*s^2 - 45*s + 11)/9)*h

def regular_z1w (s l h : ℝ) : ℝ :=
  (25*(2*s - 1)*(447250*s^5 + 172715*s^4 + 1577958*s^3 - 1724778*s^2 + 140381*s + 53266)/468)*l + (125*(s - 1)*(2*s + 1)*(25*s^2 - 45*s + 11)*(110*s^2 - 249*s + 188)/9)*h

def regular_r2w (s l h : ℝ) : ℝ :=
  (- 5*(s - 1)*(2*s - 1)*(5*s - 1)*(325*s - 241)*(170*s^2 + 16*s + 93)/39)*l + (- 25*(s - 1)^2*(5*s - 1)*(20*s - 17)*(170*s^2 + 16*s + 93)/6)*h

def regular_rw2 (s l h : ℝ) : ℝ :=
  (5*(s - 1)*(2*s - 1)*(5*s - 1)*(25*s + 171)*(170*s^2 + 16*s + 93)/39)*l + (5*(s - 1)*(5*s - 1)*(10*s + 11)*(25*s - 9)*(170*s^2 + 16*s + 93)/6)*h

def regular_z2w (s l h : ℝ) : ℝ :=
  (- 5*(s - 1)*(2*s - 1)*(5*s - 1)*(275*s - 219)*(170*s^2 + 16*s + 93)/39)*l + (- 25*(s - 1)^2*(5*s - 1)*(25*s - 9)*(170*s^2 + 16*s + 93)/6)*h

def regular_rot1 (s l h : ℝ) : ℝ :=
  (25*(2*s - 1)*(2436000*s^5 - 5780360*s^4 + 3689558*s^3 - 2808715*s^2 + 2198299*s - 401574)/936)*l + (125*(s - 1)*(25*s^2 - 45*s + 11)*(420*s^3 - 398*s^2 + 296*s - 465)/18)*h

def regular_rot2 (s l h : ℝ) : ℝ :=
  (- 5*(s - 1)*(2*s - 1)*(170*s^2 + 16*s + 93)*(2625*s^2 - 2645*s + 636)/78)*l + (125*(s - 1)^2*(25*s - 9)*(170*s^2 + 16*s + 93)/6)*h

theorem regular_coordinates {v : MixedChannel} {s : ℝ} (he : v.Equations s) :
    regularDenominator s*v.q=regular_q s v.l v.h ∧
    regularDenominator s*v.r1w=regular_r1w s v.l v.h ∧
    regularDenominator s*v.rw1=regular_rw1 s v.l v.h ∧
    regularDenominator s*v.z1w=regular_z1w s v.l v.h ∧
    regularDenominator s*v.r2w=regular_r2w s v.l v.h ∧
    regularDenominator s*v.rw2=regular_rw2 s v.l v.h ∧
    regularDenominator s*v.z2w=regular_z2w s v.l v.h ∧
    regularDenominator s*v.rot1=regular_rot1 s v.l v.h ∧
    regularDenominator s*v.rot2=regular_rot2 s v.l v.h := by
  obtain ⟨⟨a,b,c,d,e,f⟩,g,i,j⟩ := he
  repeat' apply And.intro
  · dsimp only [regularDenominator,regular_q]
    linear_combination (13*(s - 2)*(2*s - 9)*(2*s - 1)^2*(5*s - 1)*(125*s^2 + 5*s - 74)/8)*a +
      (13*(2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(4*s^3 + 64*s^2 - 77*s - 19)/8)*b +
      (13*(s - 2)*(2*s - 1)^2*(3*s + 5)*(5*s - 1)*(125*s^2 + 5*s - 74)/4)*c +
      (325*(s - 1)*(2*s - 1)*(2*s + 1)*(25*s^2 - 45*s + 11)*(30*s^2 + 18*s - 41)/36)*d +
      (325*(2*s - 1)*(2*s + 1)*(30*s^2 + 18*s - 41)*(50*s^3 + 205*s^2 - 245*s + 32)/72)*e +
      (325*(2*s - 1)*(2*s + 1)*(3*s - 2)*(25*s^2 - 45*s + 11)*(30*s^2 + 18*s - 41)/36)*f +
      (- 13*(2*s - 1)^2*(5*s - 1)*(30*s^2 + 18*s - 41)*(125*s^2 + 5*s - 74)/2)*g +
      (- 65*(2*s - 1)^2*(2*s + 1)*(30*s^2 + 18*s - 41)*(125*s^2 + 5*s - 74)/4)*i +
      (- 13*(2*s - 1)^2*(2*s + 1)*(5*s - 1)*(30*s^2 + 18*s - 41)*(125*s^2 + 5*s - 74)/4)*j
  · dsimp only [regularDenominator,regular_r1w]
    linear_combination (7*s*(2*s - 9)*(2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)/4)*a +
      ((2*s - 1)*(5*s - 1)*(14*s^2 + 89*s + 93)*(125*s^2 + 5*s - 74)/4)*b +
      (7*s*(2*s - 1)*(3*s + 5)*(5*s - 1)*(125*s^2 + 5*s - 74)/2)*c +
      (- 25*(s - 1)*(2*s + 1)*(25*s^2 - 45*s + 11)*(130*s^2 - 174*s + 93)/18)*d +
      (- 25*(2*s + 1)*(130*s^2 - 174*s + 93)*(50*s^3 + 205*s^2 - 245*s + 32)/36)*e +
      (- 25*(2*s + 1)*(3*s - 2)*(25*s^2 - 45*s + 11)*(130*s^2 - 174*s + 93)/18)*f +
      ((2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(130*s^2 - 174*s + 93))*g +
      (5*(2*s - 1)*(2*s + 1)*(125*s^2 + 5*s - 74)*(130*s^2 - 174*s + 93)/2)*i +
      ((2*s - 1)*(2*s + 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(130*s^2 - 174*s + 93)/2)*j
  · dsimp only [regularDenominator,regular_rw1]
    linear_combination (- 7*(2*s - 1)*(5*s - 1)*(8*s^2 + 8*s - 3)*(125*s^2 + 5*s - 74)/4)*a +
      ((2*s - 1)*(5*s - 1)*(57*s^2 + 101*s + 24)*(125*s^2 + 5*s - 74)/2)*b +
      ((2*s - 1)*(5*s - 1)*(86*s^2 + 9*s + 9)*(125*s^2 + 5*s - 74)/2)*c +
      (25*(s - 1)*(2*s + 1)*(10*s^2 + 76*s - 177)*(25*s^2 - 45*s + 11)/18)*d +
      (25*(2*s + 1)*(10*s^2 + 76*s - 177)*(50*s^3 + 205*s^2 - 245*s + 32)/36)*e +
      (25*(2*s + 1)*(3*s - 2)*(10*s^2 + 76*s - 177)*(25*s^2 - 45*s + 11)/18)*f +
      (- (2*s - 1)*(5*s - 1)*(10*s^2 + 76*s - 177)*(125*s^2 + 5*s - 74))*g +
      (- 5*(2*s - 1)*(2*s + 1)*(10*s^2 + 76*s - 177)*(125*s^2 + 5*s - 74)/2)*i +
      (- (2*s - 1)*(2*s + 1)*(5*s - 1)*(10*s^2 + 76*s - 177)*(125*s^2 + 5*s - 74)/2)*j
  · dsimp only [regularDenominator,regular_z1w]
    linear_combination (7*(2*s - 9)*(2*s - 1)*(3*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)/8)*a +
      (- (2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(128*s^2 - 407*s - 113)/8)*b +
      (7*(2*s - 1)*(3*s - 1)*(3*s + 5)*(5*s - 1)*(125*s^2 + 5*s - 74)/4)*c +
      (- 25*(s - 1)*(2*s + 1)*(25*s^2 - 45*s + 11)*(110*s^2 - 249*s + 188)/18)*d +
      (- 25*(2*s + 1)*(110*s^2 - 249*s + 188)*(50*s^3 + 205*s^2 - 245*s + 32)/36)*e +
      (- 25*(2*s + 1)*(3*s - 2)*(25*s^2 - 45*s + 11)*(110*s^2 - 249*s + 188)/18)*f +
      ((2*s - 1)*(5*s - 1)*(110*s^2 - 249*s + 188)*(125*s^2 + 5*s - 74))*g +
      (5*(2*s - 1)*(2*s + 1)*(110*s^2 - 249*s + 188)*(125*s^2 + 5*s - 74)/2)*i +
      ((2*s - 1)*(2*s + 1)*(5*s - 1)*(110*s^2 - 249*s + 188)*(125*s^2 + 5*s - 74)/2)*j
  · dsimp only [regularDenominator,regular_r2w]
    linear_combination (5*(s - 1)^2*(5*s - 1)*(20*s - 17)*(170*s^2 + 16*s + 93)/12)*d +
      (5*(s - 1)*(5*s - 1)*(20*s^2 + 56*s - 55)*(170*s^2 + 16*s + 93)/12)*e +
      (5*(s - 1)*(3*s - 2)*(5*s - 1)*(20*s - 17)*(170*s^2 + 16*s + 93)/12)*f
  · dsimp only [regularDenominator,regular_rw2]
    linear_combination (- (s - 1)*(5*s - 1)*(10*s + 11)*(25*s - 9)*(170*s^2 + 16*s + 93)/12)*d +
      ((s - 1)*(5*s - 1)*(10*s + 11)*(50*s - 3)*(170*s^2 + 16*s + 93)/12)*e +
      ((s - 1)*(5*s - 1)*(170*s^2 + 16*s + 93)*(750*s^2 + 5*s - 246)/12)*f
  · dsimp only [regularDenominator,regular_z2w]
    linear_combination (5*(s - 1)^2*(5*s - 1)*(25*s - 9)*(170*s^2 + 16*s + 93)/12)*d +
      (- 5*(s - 1)^2*(5*s - 1)*(50*s - 3)*(170*s^2 + 16*s + 93)/12)*e +
      (5*(s - 1)*(3*s - 2)*(5*s - 1)*(25*s - 9)*(170*s^2 + 16*s + 93)/12)*f
  · dsimp only [regularDenominator,regular_rot1]
    linear_combination (- 7*s*(2*s - 9)*(2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)/8)*a +
      (- (2*s - 1)*(5*s - 1)*(14*s^2 + 89*s + 93)*(125*s^2 + 5*s - 74)/8)*b +
      (- 7*s*(2*s - 1)*(3*s + 5)*(5*s - 1)*(125*s^2 + 5*s - 74)/4)*c +
      (- 25*(s - 1)*(25*s^2 - 45*s + 11)*(420*s^3 - 398*s^2 + 296*s - 465)/36)*d +
      (- 25*(50*s^3 + 205*s^2 - 245*s + 32)*(420*s^3 - 398*s^2 + 296*s - 465)/72)*e +
      (- 25*(3*s - 2)*(25*s^2 - 45*s + 11)*(420*s^3 - 398*s^2 + 296*s - 465)/36)*f +
      (- (2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(130*s^2 - 174*s + 93)/2)*g +
      (5*(2*s - 1)*(125*s^2 + 5*s - 74)*(420*s^3 - 398*s^2 + 296*s - 465)/4)*i +
      ((2*s - 1)*(5*s - 1)*(125*s^2 + 5*s - 74)*(420*s^3 - 398*s^2 + 296*s - 465)/4)*j
  · dsimp only [regularDenominator,regular_rot2]
    linear_combination (- 25*(s - 1)^2*(25*s - 9)*(170*s^2 + 16*s + 93)/12)*d +
      (25*(s - 1)^2*(50*s - 3)*(170*s^2 + 16*s + 93)/12)*e +
      (- 25*(s - 1)*(3*s - 2)*(25*s - 9)*(170*s^2 + 16*s + 93)/12)*f +
      (- 5*(s - 1)*(2*s - 1)*(125*s^2 + 5*s - 74)*(170*s^2 + 16*s + 93))*i

def angularDenominator (s : ℝ) : ℝ := (s - 1)*(1200*s^4 - 1000*s^3 - 1464*s^2 - 722*s + 465)

def angular_q (s l h : ℝ) : ℝ :=
  (- 13*(s - 1)*(2*s - 1)*(8400*s^4 + 10200*s^3 - 38948*s^2 + 41622*s - 10627)/49)*l + (- 3380*(s - 1)*(2*s - 9)*(2*s - 1)*(25*s^2 - 45*s + 11)/49)*h

def angular_l (s l h : ℝ) : ℝ :=
  (312*(s - 1)^2*(25*s - 9)*(170*s^2 + 16*s + 93)/245)*l + (- 104*(s - 1)*(25*s^2 - 45*s + 11)*(420*s^3 - 398*s^2 + 296*s - 465)/245)*h

def angular_h (s l h : ℝ) : ℝ :=
  (24*(s - 1)*(2*s - 1)*(170*s^2 + 16*s + 93)*(2625*s^2 - 2645*s + 636)/6125)*l + (2*(2*s - 1)*(2436000*s^5 - 5780360*s^4 + 3689558*s^3 - 2808715*s^2 + 2198299*s - 401574)/1225)*h

def angular_r1w (s l h : ℝ) : ℝ :=
  (2*(s - 1)*(5200*s^4 - 10080*s^3 + 20720*s^2 - 4542*s - 651)/7)*l + (208*s*(s - 1)*(2*s - 9)*(25*s^2 - 45*s + 11)/7)*h

def angular_rw1 (s l h : ℝ) : ℝ :=
  (- 2*(s - 1)*(400*s^4 - 12500*s^3 - 16678*s^2 + 9872*s - 867)/7)*l + (- 260*(s - 1)*(2*s - 1)*(2*s + 3)*(25*s^2 - 45*s + 11)/7)*h

def angular_z1w (s l h : ℝ) : ℝ :=
  (2*(s - 1)*(4400*s^4 - 15150*s^3 + 35637*s^2 - 16083*s + 1843)/7)*l + (130*(s - 1)*(2*s - 9)*(2*s - 1)*(25*s^2 - 45*s + 11)/7)*h

def angular_r2w (s l h : ℝ) : ℝ :=
  (- 12*(s - 1)^2*(20*s - 7)*(170*s^2 + 16*s + 93)/35)*l + (- 3*(s - 1)*(2*s - 1)*(1360*s^3 - 3296*s^2 + 1768*s - 651)/7)*h

def angular_rw2 (s l h : ℝ) : ℝ :=
  (12*(s - 1)*(10*s + 1)*(25*s - 9)*(170*s^2 + 16*s + 93)/175)*l + (3*(76000*s^5 - 133440*s^4 + 27756*s^3 - 53460*s^2 + 20663*s - 1023)/35)*h

def angular_z2w (s l h : ℝ) : ℝ :=
  (- 12*(s - 1)^2*(25*s - 9)*(170*s^2 + 16*s + 93)/35)*l + (- (s - 1)*(14400*s^4 - 32792*s^3 + 20454*s^2 - 15079*s + 3441)/7)*h

theorem angular_coordinates {v : MixedChannel} {s : ℝ} (he : v.Equations s) :
    angularDenominator s*v.q=angular_q s v.rot1 v.rot2 ∧
    angularDenominator s*v.l=angular_l s v.rot1 v.rot2 ∧
    angularDenominator s*v.h=angular_h s v.rot1 v.rot2 ∧
    angularDenominator s*v.r1w=angular_r1w s v.rot1 v.rot2 ∧
    angularDenominator s*v.rw1=angular_rw1 s v.rot1 v.rot2 ∧
    angularDenominator s*v.z1w=angular_z1w s v.rot1 v.rot2 ∧
    angularDenominator s*v.r2w=angular_r2w s v.rot1 v.rot2 ∧
    angularDenominator s*v.rw2=angular_rw2 s v.rot1 v.rot2 ∧
    angularDenominator s*v.z2w=angular_z2w s v.rot1 v.rot2 := by
  obtain ⟨⟨a,b,c,d,e,f⟩,g,i,j⟩ := he
  repeat' apply And.intro
  · dsimp only [angularDenominator,angular_q]
    linear_combination (- 65*(s - 1)*(2*s - 9)*(2*s - 1)*(20*s - 7)/28)*a +
      (13*(s - 1)*(2*s - 9)*(2800*s^2 + 1390*s - 849)/196)*b +
      (- 65*(s - 1)*(2*s - 1)*(3*s + 5)*(20*s - 7)/14)*c +
      (21125*(s - 1)*(2*s - 9)*(2*s - 1)/98)*e +
      (- 26*(s - 1)*(2*s - 1)*(4200*s^3 + 3000*s^2 - 16099*s + 5168)/49)*g +
      (- 4225*(s - 1)*(2*s - 9)*(2*s - 1)*(20*s - 17)/49)*i +
      (- 2535*(s - 1)*(2*s - 9)*(2*s - 1)*(25*s - 9)/49)*j
  · dsimp only [angularDenominator,angular_l]
    linear_combination (39*s*(s - 1)*(2*s - 9)*(25*s - 9)/35)*a +
      (39*(s - 1)*(25*s - 9)*(14*s^2 + 89*s + 93)/245)*b +
      (78*s*(s - 1)*(3*s + 5)*(25*s - 9)/35)*c +
      (65*(s - 1)*(420*s^3 - 398*s^2 + 296*s - 465)/49)*e +
      (156*(s - 1)*(25*s - 9)*(130*s^2 - 174*s + 93)/245)*g +
      (- 26*(s - 1)*(20*s - 17)*(420*s^3 - 398*s^2 + 296*s - 465)/49)*i +
      (- 78*(s - 1)*(25*s - 9)*(420*s^3 - 398*s^2 + 296*s - 465)/245)*j
  · dsimp only [angularDenominator,angular_h]
    linear_combination (3*s*(2*s - 9)*(2*s - 1)*(2625*s^2 - 2645*s + 636)/875)*a +
      (3*(2*s - 1)*(14*s^2 + 89*s + 93)*(2625*s^2 - 2645*s + 636)/6125)*b +
      (6*s*(2*s - 1)*(3*s + 5)*(2625*s^2 - 2645*s + 636)/875)*c +
      ((s - 1)*(1200*s^4 - 1000*s^3 - 1464*s^2 - 722*s + 465)/10)*d +
      ((58800*s^5 - 189280*s^4 + 472340*s^3 - 434216*s^2 + 139162*s - 58125)/490)*e +
      ((3*s - 2)*(1200*s^4 - 1000*s^3 - 1464*s^2 - 722*s + 465)/10)*f +
      (12*(2*s - 1)*(130*s^2 - 174*s + 93)*(2625*s^2 - 2645*s + 636)/6125)*g +
      (4*(2*s - 1)*(887250*s^4 - 2066035*s^3 + 802523*s^2 - 566851*s + 560325)/1225)*i +
      (- 6*(2*s - 1)*(2625*s^2 - 2645*s + 636)*(420*s^3 - 398*s^2 + 296*s - 465)/6125)*j
  · dsimp only [angularDenominator,angular_r1w]
    linear_combination (s*(s - 1)*(2*s - 9)*(20*s - 7))*a +
      ((s - 1)*(20*s - 7)*(14*s^2 + 89*s + 93)/7)*b +
      (2*s*(s - 1)*(3*s + 5)*(20*s - 7))*c +
      (- 650*s*(s - 1)*(2*s - 9)/7)*e +
      (4*(s - 1)*(20*s - 7)*(130*s^2 - 174*s + 93)/7)*g +
      (260*s*(s - 1)*(2*s - 9)*(20*s - 17)/7)*i +
      (156*s*(s - 1)*(2*s - 9)*(25*s - 9)/7)*j
  · dsimp only [angularDenominator,angular_rw1]
    linear_combination (- 5*(s - 1)*(2*s - 1)*(2*s + 3)*(20*s - 7)/4)*a +
      ((s - 1)*(2*s + 3)*(2800*s^2 + 1390*s - 849)/28)*b +
      ((s - 1)*(600*s^3 + 310*s^2 - 59*s - 45)/2)*c +
      (1625*(s - 1)*(2*s - 1)*(2*s + 3)/14)*e +
      (- 2*(s - 1)*(400*s^3 - 2950*s^2 - 8963*s + 3531)/7)*g +
      (- 325*(s - 1)*(2*s - 1)*(2*s + 3)*(20*s - 17)/7)*i +
      (- 195*(s - 1)*(2*s - 1)*(2*s + 3)*(25*s - 9)/7)*j
  · dsimp only [angularDenominator,angular_z1w]
    linear_combination (5*(s - 1)*(2*s - 9)*(2*s - 1)*(20*s - 7)/8)*a +
      (- (s - 1)*(2*s - 9)*(2800*s^2 + 1390*s - 849)/56)*b +
      (5*(s - 1)*(2*s - 1)*(3*s + 5)*(20*s - 7)/4)*c +
      (- 1625*(s - 1)*(2*s - 9)*(2*s - 1)/28)*e +
      ((s - 1)*(8800*s^3 - 24950*s^2 + 31489*s - 8423)/7)*g +
      (325*(s - 1)*(2*s - 9)*(2*s - 1)*(20*s - 17)/14)*i +
      (195*(s - 1)*(2*s - 9)*(2*s - 1)*(25*s - 9)/14)*j
  · dsimp only [angularDenominator,angular_r2w]
    linear_combination (- 3*s*(s - 1)*(2*s - 9)*(20*s - 7)/10)*a +
      (- 3*(s - 1)*(20*s - 7)*(14*s^2 + 89*s + 93)/70)*b +
      (- 3*s*(s - 1)*(3*s + 5)*(20*s - 7)/5)*c +
      (195*s*(s - 1)*(2*s - 9)/7)*e +
      (- 6*(s - 1)*(20*s - 7)*(130*s^2 - 174*s + 93)/35)*g +
      (- 78*s*(s - 1)*(2*s - 9)*(20*s - 17)/7)*i +
      (3*(s - 1)*(20*s - 7)*(420*s^3 - 398*s^2 + 296*s - 465)/35)*j
  · dsimp only [angularDenominator,angular_rw2]
    linear_combination (3*s*(2*s - 9)*(10*s + 1)*(25*s - 9)/50)*a +
      (3*(10*s + 1)*(25*s - 9)*(14*s^2 + 89*s + 93)/350)*b +
      (3*s*(3*s + 5)*(10*s + 1)*(25*s - 9)/25)*c +
      ((10*s + 1)*(420*s^3 - 398*s^2 + 296*s - 465)/14)*e +
      ((1200*s^4 - 1000*s^3 - 1464*s^2 - 722*s + 465)/2)*f +
      (6*(10*s + 1)*(25*s - 9)*(130*s^2 - 174*s + 93)/175)*g +
      (6*(27500*s^4 - 48540*s^3 - 5439*s^2 - 14627*s + 4650)/35)*i +
      (- 3*(10*s + 1)*(25*s - 9)*(420*s^3 - 398*s^2 + 296*s - 465)/175)*j
  · dsimp only [angularDenominator,angular_z2w]
    linear_combination (- 3*s*(s - 1)*(2*s - 9)*(25*s - 9)/10)*a +
      (- 3*(s - 1)*(25*s - 9)*(14*s^2 + 89*s + 93)/70)*b +
      (- 3*s*(s - 1)*(3*s + 5)*(25*s - 9)/5)*c +
      (- 5*(s - 1)*(420*s^3 - 398*s^2 + 296*s - 465)/14)*e +
      (- 6*(s - 1)*(25*s - 9)*(130*s^2 - 174*s + 93)/35)*g +
      (- 2*(s - 1)*(4050*s^3 - 11467*s^2 + 4639*s - 2325)/7)*i +
      (3*(s - 1)*(25*s - 9)*(420*s^3 - 398*s^2 + 296*s - 465)/35)*j

end EuclideanMidpointRigidity.MixedChannel
