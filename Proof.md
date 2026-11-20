# Proof guide

Write Kₓ(u, v) for the vector satisfying ⟨Kₓ(u, v), w⟩ = Cₓ(u, v, w).
If C takes a nonzero value, the argument finds a ball on which a nonzero
subspace can be removed while preserving the midpoint hypothesis.
Induction on dimension then gives a point where DC = 0 in every open ball
contained in the domain.

## What the midpoint identity implies

Join p − εh to p + εh by the short geodesic for each sign. Expanding the two
boundary-value problems gives polynomial approximations through degree six.
Their acceleration residual is O(ε⁷) uniformly on the time interval. A
Dirichlet estimate transfers that bound to the actual midpoints. The fourth-
and sixth-order coefficients of the midpoint sum therefore vanish separately.
At p, let J(ℓ) denote the derivative of K in direction ℓ, put k = K(h, h)
and put U = J(h)(h, h). The fourth-order equation is

> 2K(h, U) + 5J(k)(h, h) − 4J(h)(h, k) = 0.

The short-geodesic and fourth-order arguments adapt the planar formalization. The sixth-order equation retains all terms involving spatial derivatives of the field. [PlanarMidpoint](https://github.com/JD-Jones-ASES/PlanarMidpoint/tree/f277b89a3b0db20872101fd61580ecced748e7c1) · [Fourth order](EuclideanMidpointRigidity/GeometricObstruction.lean) · [Sixth order](EuclideanMidpointRigidity/GeometricSixth.lean)

## Finding a fixed direction

Let a(x) be the maximum of Cₓ(h, h, h) over h in the closed unit ball. At a
positive maximum with unit direction e, one has K(e, e) = ae. On a smooth
maximizing section the fourth-order identity restricts the gradient of the
maximum to the sum of two eigenspaces of K(e, ·), with eigenvalues −a/2 and
a/5. The sixth-order identity, the fourth-order identity and the unit-ball
bound exclude a nonzero gradient in either space or their sum. An envelope
argument allows the maximizing direction to change. Thus a is constant on
the connected domain. If a = 0, polarization gives C = 0.
[Spectral exclusion](EuclideanMidpointRigidity/MixedGradientExclusion.lean) · [Constant maximum](EuclideanMidpointRigidity/ConstantAmplitude.lean)

For a > 0, variations of the two endpoints along a maximizing line yield a
linear differential equation for the tensor on that line. Its characteristic
roots are real. Analytic continuation of the fourth- and sixth-order equations
bounds its solutions on both tails, forcing the derivative of C along e to
vanish. On a smaller ball, choose a smooth maximizing section of least possible
derivative rank bound. Translating its graph, then differentiating the
complementary-midpoint law, shows that DC annihilates every derivative of e.
The span of these derivatives and e itself is fixed near a point of maximal
span dimension. [Maximizing lines](EuclideanMidpointRigidity/ConstantRulings.lean) · [Derivatives of the section](EuclideanMidpointRigidity/Osculation.lean) · [Fixed span](EuclideanMidpointRigidity/FixedOsculatingSpace.lean)

Fix u = e(p)/a. Along this spatially stationary direction, a finite family of
tilted chords bounds the derivative of q(x) = Kₓ(u, u) − u by a constant
times ‖q(x)‖. The fifth, seventh and ninth boundary derivatives detect every
pair of axial eigenvalues. Since q(p) = 0, q vanishes nearby. The fixed-axis
equations then give J(ℓ)(u, v) = 0 for every ℓ and v.
[Tilt separation](EuclideanMidpointRigidity/FirstTiltSeparation.lean) · [Fixed direction](EuclideanMidpointRigidity/FixedDirections.lean)

## Removing a factor

Write DC[w] for the derivative of C in direction w. On this ball let S consist
of the vectors z satisfying DC[z] = 0 and J(ℓ)(z, v) = 0 everywhere for all ℓ
and v. It contains u. For z in S, the operator B = Kₓ(z, ·) is independent
of x. The fourth-order equation gives DC[By](y, y, y) = 0. Polarization and
commutation of derivatives imply that the fourth derivative of C along Bv
vanishes. Extend the resulting polynomial of degree at most three in that
coordinate to the whole line. Its continued fourth- and sixth-order equations
force its spherical maximum to stay bounded. Hence DC[Bv] = 0. The remaining
quartic equations give a Killing vector field x ↦ Kₓ(Bv, Bv) with zero
acceleration. This field is parallel. Polarization now gives Bv in S for
every v. [Polynomial continuation](EuclideanMidpointRigidity/PolynomialCoordinate.lean) · [Products of fixed directions](EuclideanMidpointRigidity/FixedProducts.lean)

Orthogonal projection onto the complement of S therefore takes short
geodesics to short geodesics for the restricted cubic and preserves the
midpoint sum. Uniqueness identifies their midpoints with the canonical ones.
Since S contains the nonzero vector u, its orthogonal complement has dimension
less than d. Induction makes the restricted cubic constant. All components of
DC at the ball center vanish. Such centers are dense, so continuity gives
DC = 0 throughout the domain, and connectedness gives the result.
[Projected geodesics](EuclideanMidpointRigidity/FactorGeodesics.lean) · [Dimension induction](EuclideanMidpointRigidity/Rigidity.lean)
