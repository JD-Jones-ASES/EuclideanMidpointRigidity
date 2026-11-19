# Proof guide

Write $K_x(u,v)$ for the vector satisfying $\langle K_x(u,v),w\rangle=C_x(u,v,w)$. The argument finds a ball on which a nonzero subspace can be removed while preserving the midpoint hypothesis. Induction on the dimension then gives a point where $DC=0$ in every open ball.

## What the midpoint identity implies

Join $p-\varepsilon h$ to $p+\varepsilon h$ by the short geodesic for each sign. Expanding the two boundary-value problems gives polynomial approximations through degree six. Their acceleration residual is $O(\varepsilon^7)$ uniformly on the time interval. A Dirichlet estimate transfers that bound to the actual midpoints, so the sums of the fourth and sixth coefficients vanish. If $J_l=D_lK$, $k=K(h,h)$ and $U=J_h(h,h)$ at $p$, the fourth-order equation is

$$2K(h,U)+5J_k(h,h)-4J_h(h,k)=0.$$

The short-geodesic and fourth-order arguments adapt the planar formalization. The sixth-order equation retains all terms involving spatial derivatives of the field. [PlanarMidpoint](https://github.com/JD-Jones-ASES/PlanarMidpoint/tree/f277b89a3b0db20872101fd61580ecced748e7c1) · [Fourth order](EuclideanMidpointRigidity/GeometricObstruction.lean) · [Sixth order](EuclideanMidpointRigidity/GeometricSixth.lean)

## Finding a fixed direction

Let $a(x)$ be the maximum of $C_x(h,h,h)$ on the closed unit ball. At a positive maximum with unit direction $e$, one has $K(e,e)=ae$. The fourth-order identity constrains the derivative of the maximum to two eigenspaces of $K(e,\cdot)$, with eigenvalues $-a/2$ and $a/5$. On smooth maximizing sections the sixth-order identity, the fourth-order identity and the unit-ball bound exclude a nonzero derivative in either eigenspace or their sum. An envelope argument allows the maximizing direction to change. Thus $a$ is constant on the connected domain. If $a=0$, polarization gives $C=0$. [Spectral exclusion](EuclideanMidpointRigidity/MixedGradientExclusion.lean) · [Constant maximum](EuclideanMidpointRigidity/ConstantAmplitude.lean)

For $a>0$, variations of the two endpoints along a maximizing line yield a linear differential equation for the tensor on that line. Its characteristic roots are real. Analytic continuation of the fourth- and sixth-order equations bounds its solutions on both tails, forcing $D_e C=0$. On a smaller ball, choose a smooth maximizing section of least possible derivative rank bound. Translating its graph, then differentiating the complementary-midpoint law, shows that $DC$ annihilates every derivative of $e$. The span of these derivatives and $e$ itself is fixed near a point of maximal span dimension. [Maximizing lines](EuclideanMidpointRigidity/ConstantRulings.lean) · [Derivatives of the section](EuclideanMidpointRigidity/Osculation.lean) · [Fixed span](EuclideanMidpointRigidity/FixedOsculatingSpace.lean)

Fix $u=e(p)/a$. Along this spatially stationary direction, a finite family of tilted chords bounds the derivative of $q(x)=K_x(u,u)-u$ by a constant times $\|q(x)\|$. The fifth, seventh and ninth boundary derivatives detect every pair of axial eigenvalues. Since $q(p)=0$, it vanishes nearby. The fixed-axis equations then give $(D_lK)(u,v)=0$ for every $l,v$. [Tilt separation](EuclideanMidpointRigidity/FirstTiltSeparation.lean) · [Fixed direction](EuclideanMidpointRigidity/FixedDirections.lean)

## Removing a factor

On this ball let $S$ consist of the vectors $z$ satisfying $D_zC=0$ and $(D_lK)(z,v)=0$ everywhere for all $l,v$. It contains $u$. For $z\in S$, the operator $B=K_x(z,\cdot)$ is independent of $x$. The fourth-order equation gives $(D_{By}C)(y,y,y)=0$. Polarization and commutation of derivatives imply $D_{Bv}^4 C=0$. Extend the resulting cubic polynomial in that coordinate to the whole line. Its continued fourth- and sixth-order equations force its spherical maximum to stay bounded. Hence $D_{Bv}C=0$. The remaining quartic rows give a Killing vector field $x\mapsto K_x(Bv,Bv)$ with zero acceleration. This field is parallel. Polarization now gives $Bv\in S$ for every $v$. [Polynomial continuation](EuclideanMidpointRigidity/PolynomialCoordinate.lean) · [Products of fixed directions](EuclideanMidpointRigidity/FixedProducts.lean)

Orthogonal projection onto $S^\perp$ therefore takes short geodesics to short geodesics for the restricted cubic and preserves the midpoint sum. Uniqueness identifies their midpoints with the canonical ones. Since $\dim S^\perp<d$, induction makes the restricted cubic constant. All components of $DC$ at the ball center vanish. Such centers are dense, so continuity gives $DC=0$ throughout the domain, and connectedness gives the result. [Projected geodesics](EuclideanMidpointRigidity/FactorGeodesics.lean) · [Dimension induction](EuclideanMidpointRigidity/Rigidity.lean)
