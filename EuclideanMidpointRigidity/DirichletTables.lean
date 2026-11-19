module

public import EuclideanMidpointRigidity.SixthRecursion

/-! # Coefficients of the two signed Dirichlet paths

The two paths share their rooted trees. Reversing the sign of the connection
changes the sign of a coefficient once for each product in its tree. The
equalities below verify the forcing and integration separately at each order.
-/

@[expose] public section
namespace EuclideanMidpointRigidity.Jet.DirichletTables
open EuclideanMidpointRigidity.Jet.Tree (direction)

set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

private def withSign (negative : Bool) (q : ℚ) : ℚ := if negative then -q else q

private def tree1 : Tree := .k direction direction
private def tree2 : Tree := .j direction direction direction
private def tree3 : Tree := .k direction tree1
private def tree4 : Tree := .hess direction direction direction direction
private def tree5 : Tree := .j tree1 direction direction
private def tree6 : Tree := .j direction direction tree1
private def tree7 : Tree := .k direction tree2
private def tree8 : Tree := .k direction tree3
private def tree9 : Tree := .k tree1 tree1
private def tree10 : Tree := .third direction direction direction direction direction
private def tree11 : Tree := .hess direction tree1 direction direction
private def tree12 : Tree := .hess direction direction direction tree1
private def tree13 : Tree := .j tree2 direction direction
private def tree14 : Tree := .j tree3 direction direction
private def tree15 : Tree := .j tree1 direction tree1
private def tree16 : Tree := .j direction direction tree2
private def tree17 : Tree := .j direction direction tree3
private def tree18 : Tree := .j direction tree1 tree1
private def tree19 : Tree := .k direction tree4
private def tree20 : Tree := .k direction tree5
private def tree21 : Tree := .k direction tree6
private def tree22 : Tree := .k direction tree7
private def tree23 : Tree := .k direction tree8
private def tree24 : Tree := .k direction tree9
private def tree25 : Tree := .k tree1 tree2
private def tree26 : Tree := .k tree1 tree3
private def tree27 : Tree := .fourth direction direction direction direction direction direction
private def tree28 : Tree := .third direction direction tree1 direction direction
private def tree29 : Tree := .third direction direction direction direction tree1
private def tree30 : Tree := .hess direction tree2 direction direction
private def tree31 : Tree := .hess direction tree3 direction direction
private def tree32 : Tree := .hess tree1 tree1 direction direction
private def tree33 : Tree := .hess direction tree1 direction tree1
private def tree34 : Tree := .hess direction direction direction tree2
private def tree35 : Tree := .hess direction direction direction tree3
private def tree36 : Tree := .hess direction direction tree1 tree1
private def tree37 : Tree := .j tree4 direction direction
private def tree38 : Tree := .j tree5 direction direction
private def tree39 : Tree := .j tree6 direction direction
private def tree40 : Tree := .j tree7 direction direction
private def tree41 : Tree := .j tree8 direction direction
private def tree42 : Tree := .j tree9 direction direction
private def tree43 : Tree := .j tree2 direction tree1
private def tree44 : Tree := .j tree3 direction tree1
private def tree45 : Tree := .j tree1 direction tree2
private def tree46 : Tree := .j tree1 direction tree3
private def tree47 : Tree := .j tree1 tree1 tree1
private def tree48 : Tree := .j direction direction tree4
private def tree49 : Tree := .j direction direction tree5
private def tree50 : Tree := .j direction direction tree6
private def tree51 : Tree := .j direction direction tree7
private def tree52 : Tree := .j direction direction tree8
private def tree53 : Tree := .j direction direction tree9
private def tree54 : Tree := .j direction tree1 tree2
private def tree55 : Tree := .j direction tree1 tree3
private def tree56 : Tree := .k direction tree10
private def tree57 : Tree := .k direction tree11
private def tree58 : Tree := .k direction tree12
private def tree59 : Tree := .k direction tree13
private def tree60 : Tree := .k direction tree14
private def tree61 : Tree := .k direction tree15
private def tree62 : Tree := .k direction tree16
private def tree63 : Tree := .k direction tree17
private def tree64 : Tree := .k direction tree18
private def tree65 : Tree := .k direction tree19
private def tree66 : Tree := .k direction tree20
private def tree67 : Tree := .k direction tree21
private def tree68 : Tree := .k direction tree22
private def tree69 : Tree := .k direction tree23
private def tree70 : Tree := .k direction tree24
private def tree71 : Tree := .k direction tree25
private def tree72 : Tree := .k direction tree26
private def tree73 : Tree := .k tree1 tree4
private def tree74 : Tree := .k tree1 tree5
private def tree75 : Tree := .k tree1 tree6
private def tree76 : Tree := .k tree1 tree7
private def tree77 : Tree := .k tree1 tree8
private def tree78 : Tree := .k tree1 tree9
private def tree79 : Tree := .k tree2 tree2
private def tree80 : Tree := .k tree3 tree2
private def tree81 : Tree := .k tree3 tree3

private def force2 (negative : Bool) : TimePolynomial :=
  [⟨tree1, 0, withSign negative (-1)⟩]

private def path2 (negative : Bool) : TimePolynomial :=
  [⟨tree1, 0, withSign negative (1/2)⟩, ⟨tree1, 2, withSign negative (-1/2)⟩]

private def force3 (negative : Bool) : TimePolynomial :=
  [⟨tree2, 1, withSign negative (-1)⟩, ⟨tree3, 1, 2⟩]

private def path3 (negative : Bool) : TimePolynomial :=
  [⟨tree3, 1, -1/3⟩, ⟨tree3, 3, 1/3⟩, ⟨tree2, 1, withSign negative (1/6)⟩,
    ⟨tree2, 3, withSign negative (-1/6)⟩]

private def force4 (negative : Bool) : TimePolynomial :=
  [⟨tree4, 2, withSign negative (-1/2)⟩, ⟨tree5, 2, 1/2⟩, ⟨tree5, 0, -1/2⟩,
    ⟨tree6, 2, 2⟩, ⟨tree7, 2, 1⟩, ⟨tree7, 0, -1/3⟩,
    ⟨tree8, 2, withSign negative (-2)⟩, ⟨tree8, 0, withSign negative (2/3)⟩, ⟨tree9, 2, withSign negative (-1)⟩]

private def path4 (negative : Bool) : TimePolynomial :=
  [⟨tree9, 0, withSign negative (1/12)⟩, ⟨tree9, 4, withSign negative (-1/12)⟩, ⟨tree8, 0, withSign negative (-1/6)⟩,
    ⟨tree8, 2, withSign negative (1/3)⟩, ⟨tree8, 4, withSign negative (-1/6)⟩, ⟨tree7, 0, 1/12⟩,
    ⟨tree7, 2, -1/6⟩, ⟨tree7, 4, 1/12⟩, ⟨tree6, 0, -1/6⟩,
    ⟨tree6, 4, 1/6⟩, ⟨tree5, 0, 5/24⟩, ⟨tree5, 2, -1/4⟩,
    ⟨tree5, 4, 1/24⟩, ⟨tree4, 0, withSign negative (1/24)⟩, ⟨tree4, 4, withSign negative (-1/24)⟩]

private def force5 (negative : Bool) : TimePolynomial :=
  [⟨tree10, 3, withSign negative (-1/6)⟩, ⟨tree11, 3, 1/2⟩, ⟨tree11, 1, -1/2⟩,
    ⟨tree12, 3, 1⟩, ⟨tree13, 3, 1/6⟩, ⟨tree13, 1, -1/6⟩,
    ⟨tree14, 3, withSign negative (-1/3)⟩, ⟨tree14, 1, withSign negative (1/3)⟩, ⟨tree15, 3, withSign negative (-1)⟩,
    ⟨tree15, 1, withSign negative (1)⟩, ⟨tree16, 3, 1⟩, ⟨tree16, 1, -1/3⟩,
    ⟨tree17, 3, withSign negative (-2)⟩, ⟨tree17, 1, withSign negative (2/3)⟩, ⟨tree18, 3, withSign negative (-1)⟩,
    ⟨tree19, 3, 1/3⟩, ⟨tree20, 3, withSign negative (-1/3)⟩, ⟨tree20, 1, withSign negative (1)⟩,
    ⟨tree21, 3, withSign negative (-4/3)⟩, ⟨tree22, 3, withSign negative (-2/3)⟩, ⟨tree22, 1, withSign negative (2/3)⟩,
    ⟨tree23, 3, 4/3⟩, ⟨tree23, 1, -4/3⟩, ⟨tree24, 3, 2/3⟩,
    ⟨tree25, 3, withSign negative (-1)⟩, ⟨tree25, 1, withSign negative (1/3)⟩, ⟨tree26, 3, 2⟩,
    ⟨tree26, 1, -2/3⟩]

private def path5 (negative : Bool) : TimePolynomial :=
  [⟨tree26, 1, 1/90⟩, ⟨tree26, 3, -1/9⟩, ⟨tree26, 5, 1/10⟩,
    ⟨tree25, 1, withSign negative (-1/180)⟩, ⟨tree25, 3, withSign negative (1/18)⟩, ⟨tree25, 5, withSign negative (-1/20)⟩,
    ⟨tree24, 1, -1/30⟩, ⟨tree24, 5, 1/30⟩, ⟨tree23, 1, 7/45⟩,
    ⟨tree23, 3, -2/9⟩, ⟨tree23, 5, 1/15⟩, ⟨tree22, 1, withSign negative (-7/90)⟩,
    ⟨tree22, 3, withSign negative (1/9)⟩, ⟨tree22, 5, withSign negative (-1/30)⟩, ⟨tree21, 1, withSign negative (1/15)⟩,
    ⟨tree21, 5, withSign negative (-1/15)⟩, ⟨tree20, 1, withSign negative (-3/20)⟩, ⟨tree20, 3, withSign negative (1/6)⟩,
    ⟨tree20, 5, withSign negative (-1/60)⟩, ⟨tree19, 1, -1/60⟩, ⟨tree19, 5, 1/60⟩,
    ⟨tree18, 1, withSign negative (1/20)⟩, ⟨tree18, 5, withSign negative (-1/20)⟩, ⟨tree17, 1, withSign negative (-1/90)⟩,
    ⟨tree17, 3, withSign negative (1/9)⟩, ⟨tree17, 5, withSign negative (-1/10)⟩, ⟨tree16, 1, 1/180⟩,
    ⟨tree16, 3, -1/18⟩, ⟨tree16, 5, 1/20⟩, ⟨tree15, 1, withSign negative (-7/60)⟩,
    ⟨tree15, 3, withSign negative (1/6)⟩, ⟨tree15, 5, withSign negative (-1/20)⟩, ⟨tree14, 1, withSign negative (-7/180)⟩,
    ⟨tree14, 3, withSign negative (1/18)⟩, ⟨tree14, 5, withSign negative (-1/60)⟩, ⟨tree13, 1, 7/360⟩,
    ⟨tree13, 3, -1/36⟩, ⟨tree13, 5, 1/120⟩, ⟨tree12, 1, -1/20⟩,
    ⟨tree12, 5, 1/20⟩, ⟨tree11, 1, 7/120⟩, ⟨tree11, 3, -1/12⟩,
    ⟨tree11, 5, 1/40⟩, ⟨tree10, 1, withSign negative (1/120)⟩, ⟨tree10, 5, withSign negative (-1/120)⟩]

private def force6 (negative : Bool) : TimePolynomial :=
  [⟨tree27, 4, withSign negative (-1/24)⟩, ⟨tree28, 4, 1/4⟩, ⟨tree28, 2, -1/4⟩,
    ⟨tree29, 4, 1/3⟩, ⟨tree30, 4, 1/6⟩, ⟨tree30, 2, -1/6⟩,
    ⟨tree31, 4, withSign negative (-1/3)⟩, ⟨tree31, 2, withSign negative (1/3)⟩, ⟨tree32, 4, withSign negative (-1/8)⟩,
    ⟨tree32, 2, withSign negative (1/4)⟩, ⟨tree32, 0, withSign negative (-1/8)⟩, ⟨tree33, 4, withSign negative (-1)⟩,
    ⟨tree33, 2, withSign negative (1)⟩, ⟨tree34, 4, 1/2⟩, ⟨tree34, 2, -1/6⟩,
    ⟨tree35, 4, withSign negative (-1)⟩, ⟨tree35, 2, withSign negative (1/3)⟩, ⟨tree36, 4, withSign negative (-1/2)⟩,
    ⟨tree37, 4, 1/24⟩, ⟨tree37, 0, -1/24⟩, ⟨tree38, 4, withSign negative (-1/24)⟩,
    ⟨tree38, 2, withSign negative (1/4)⟩, ⟨tree38, 0, withSign negative (-5/24)⟩, ⟨tree39, 4, withSign negative (-1/6)⟩,
    ⟨tree39, 0, withSign negative (1/6)⟩, ⟨tree40, 4, withSign negative (-1/12)⟩, ⟨tree40, 2, withSign negative (1/6)⟩,
    ⟨tree40, 0, withSign negative (-1/12)⟩, ⟨tree41, 4, 1/6⟩, ⟨tree41, 2, -1/3⟩,
    ⟨tree41, 0, 1/6⟩, ⟨tree42, 4, 1/12⟩, ⟨tree42, 0, -1/12⟩,
    ⟨tree43, 4, withSign negative (-1/3)⟩, ⟨tree43, 2, withSign negative (1/3)⟩, ⟨tree44, 4, 2/3⟩,
    ⟨tree44, 2, -2/3⟩, ⟨tree45, 4, withSign negative (-1/2)⟩, ⟨tree45, 2, withSign negative (2/3)⟩,
    ⟨tree46, 4, 1⟩, ⟨tree46, 2, -4/3⟩, ⟨tree45, 0, withSign negative (-1/6)⟩,
    ⟨tree46, 0, 1/3⟩, ⟨tree47, 4, 1/2⟩, ⟨tree47, 2, -1/2⟩,
    ⟨tree48, 4, 1/3⟩, ⟨tree49, 4, withSign negative (-1/3)⟩, ⟨tree49, 2, withSign negative (1)⟩,
    ⟨tree50, 4, withSign negative (-4/3)⟩, ⟨tree51, 4, withSign negative (-2/3)⟩, ⟨tree51, 2, withSign negative (2/3)⟩,
    ⟨tree52, 4, 4/3⟩, ⟨tree52, 2, -4/3⟩, ⟨tree53, 4, 2/3⟩,
    ⟨tree54, 4, withSign negative (-1)⟩, ⟨tree54, 2, withSign negative (1/3)⟩, ⟨tree55, 4, 2⟩,
    ⟨tree55, 2, -2/3⟩, ⟨tree56, 4, 1/12⟩, ⟨tree56, 0, -1/60⟩,
    ⟨tree57, 4, withSign negative (-1/4)⟩, ⟨tree57, 2, withSign negative (1/2)⟩, ⟨tree57, 0, withSign negative (-7/60)⟩,
    ⟨tree58, 4, withSign negative (-1/2)⟩, ⟨tree58, 0, withSign negative (1/10)⟩, ⟨tree59, 4, withSign negative (-1/12)⟩,
    ⟨tree59, 2, withSign negative (1/6)⟩, ⟨tree59, 0, withSign negative (-7/180)⟩, ⟨tree60, 4, 1/6⟩,
    ⟨tree60, 2, -1/3⟩, ⟨tree60, 0, 7/90⟩, ⟨tree61, 4, 1/2⟩,
    ⟨tree61, 2, -1⟩, ⟨tree61, 0, 7/30⟩, ⟨tree62, 4, withSign negative (-1/2)⟩,
    ⟨tree62, 2, withSign negative (1/3)⟩, ⟨tree62, 0, withSign negative (-1/90)⟩, ⟨tree63, 4, 1⟩,
    ⟨tree63, 2, -2/3⟩, ⟨tree63, 0, 1/45⟩, ⟨tree64, 4, 1/2⟩,
    ⟨tree64, 0, -1/10⟩, ⟨tree65, 4, withSign negative (-1/6)⟩, ⟨tree65, 0, withSign negative (1/30)⟩,
    ⟨tree66, 4, 1/6⟩, ⟨tree66, 2, -1⟩, ⟨tree66, 0, 3/10⟩,
    ⟨tree67, 4, 2/3⟩, ⟨tree67, 0, -2/15⟩, ⟨tree68, 4, 1/3⟩,
    ⟨tree68, 2, -2/3⟩, ⟨tree68, 0, 7/45⟩, ⟨tree69, 4, withSign negative (-2/3)⟩,
    ⟨tree69, 2, withSign negative (4/3)⟩, ⟨tree69, 0, withSign negative (-14/45)⟩, ⟨tree70, 4, withSign negative (-1/3)⟩,
    ⟨tree70, 0, withSign negative (1/15)⟩, ⟨tree71, 4, 1/2⟩, ⟨tree71, 2, -1/3⟩,
    ⟨tree71, 0, 1/90⟩, ⟨tree72, 4, withSign negative (-1)⟩, ⟨tree72, 2, withSign negative (2/3)⟩,
    ⟨tree72, 0, withSign negative (-1/45)⟩, ⟨tree73, 4, withSign negative (-1/3)⟩, ⟨tree74, 4, 1/3⟩,
    ⟨tree74, 2, -1⟩, ⟨tree75, 4, 4/3⟩, ⟨tree76, 4, 2/3⟩,
    ⟨tree76, 2, -2/3⟩, ⟨tree77, 4, withSign negative (-4/3)⟩, ⟨tree77, 2, withSign negative (4/3)⟩,
    ⟨tree78, 4, withSign negative (-2/3)⟩, ⟨tree79, 4, withSign negative (-1/4)⟩, ⟨tree79, 2, withSign negative (1/6)⟩,
    ⟨tree80, 4, 1⟩, ⟨tree80, 2, -2/3⟩, ⟨tree79, 0, withSign negative (-1/36)⟩,
    ⟨tree80, 0, 1/9⟩, ⟨tree81, 4, withSign negative (-1)⟩, ⟨tree81, 2, withSign negative (2/3)⟩,
    ⟨tree81, 0, withSign negative (-1/9)⟩]

private def path6 (negative : Bool) : TimePolynomial :=
  [⟨tree81, 2, withSign negative (-1/18)⟩, ⟨tree81, 4, withSign negative (1/18)⟩, ⟨tree81, 0, withSign negative (1/30)⟩,
    ⟨tree81, 6, withSign negative (-1/30)⟩, ⟨tree80, 2, 1/18⟩, ⟨tree79, 2, withSign negative (-1/72)⟩,
    ⟨tree80, 4, -1/18⟩, ⟨tree80, 0, -1/30⟩, ⟨tree80, 6, 1/30⟩,
    ⟨tree79, 4, withSign negative (1/72)⟩, ⟨tree79, 0, withSign negative (1/120)⟩, ⟨tree79, 6, withSign negative (-1/120)⟩,
    ⟨tree78, 0, withSign negative (1/45)⟩, ⟨tree78, 6, withSign negative (-1/45)⟩, ⟨tree77, 0, withSign negative (-1/15)⟩,
    ⟨tree77, 4, withSign negative (1/9)⟩, ⟨tree77, 6, withSign negative (-2/45)⟩, ⟨tree76, 0, 1/30⟩,
    ⟨tree76, 4, -1/18⟩, ⟨tree76, 6, 1/45⟩, ⟨tree75, 0, -2/45⟩,
    ⟨tree75, 6, 2/45⟩, ⟨tree74, 0, 13/180⟩, ⟨tree74, 4, -1/12⟩,
    ⟨tree74, 6, 1/90⟩, ⟨tree73, 0, withSign negative (1/90)⟩, ⟨tree73, 6, withSign negative (-1/90)⟩,
    ⟨tree72, 0, withSign negative (-1/90)⟩, ⟨tree72, 2, withSign negative (-1/90)⟩, ⟨tree72, 4, withSign negative (1/18)⟩,
    ⟨tree72, 6, withSign negative (-1/30)⟩, ⟨tree71, 0, 1/180⟩, ⟨tree71, 2, 1/180⟩,
    ⟨tree71, 4, -1/36⟩, ⟨tree71, 6, 1/60⟩, ⟨tree70, 0, withSign negative (-1/45)⟩,
    ⟨tree70, 2, withSign negative (1/30)⟩, ⟨tree70, 6, withSign negative (-1/90)⟩, ⟨tree69, 0, withSign negative (1/15)⟩,
    ⟨tree69, 2, withSign negative (-7/45)⟩, ⟨tree69, 4, withSign negative (1/9)⟩, ⟨tree69, 6, withSign negative (-1/45)⟩,
    ⟨tree68, 0, -1/30⟩, ⟨tree68, 2, 7/90⟩, ⟨tree68, 4, -1/18⟩,
    ⟨tree68, 6, 1/90⟩, ⟨tree67, 0, 2/45⟩, ⟨tree67, 2, -1/15⟩,
    ⟨tree67, 6, 1/45⟩, ⟨tree66, 0, -13/180⟩, ⟨tree66, 2, 3/20⟩,
    ⟨tree66, 4, -1/12⟩, ⟨tree66, 6, 1/180⟩, ⟨tree65, 0, withSign negative (-1/90)⟩,
    ⟨tree65, 2, withSign negative (1/60)⟩, ⟨tree65, 6, withSign negative (-1/180)⟩, ⟨tree64, 0, 1/30⟩,
    ⟨tree64, 2, -1/20⟩, ⟨tree64, 6, 1/60⟩, ⟨tree63, 0, 1/90⟩,
    ⟨tree63, 2, 1/90⟩, ⟨tree63, 4, -1/18⟩, ⟨tree63, 6, 1/30⟩,
    ⟨tree62, 0, withSign negative (-1/180)⟩, ⟨tree62, 2, withSign negative (-1/180)⟩, ⟨tree62, 4, withSign negative (1/36)⟩,
    ⟨tree62, 6, withSign negative (-1/60)⟩, ⟨tree61, 0, -1/20⟩, ⟨tree61, 2, 7/60⟩,
    ⟨tree61, 4, -1/12⟩, ⟨tree61, 6, 1/60⟩, ⟨tree60, 0, -1/60⟩,
    ⟨tree60, 2, 7/180⟩, ⟨tree60, 4, -1/36⟩, ⟨tree60, 6, 1/180⟩,
    ⟨tree59, 0, withSign negative (1/120)⟩, ⟨tree59, 2, withSign negative (-7/360)⟩, ⟨tree59, 4, withSign negative (1/72)⟩,
    ⟨tree59, 6, withSign negative (-1/360)⟩, ⟨tree58, 0, withSign negative (-1/30)⟩, ⟨tree58, 2, withSign negative (1/20)⟩,
    ⟨tree58, 6, withSign negative (-1/60)⟩, ⟨tree57, 0, withSign negative (1/40)⟩, ⟨tree57, 2, withSign negative (-7/120)⟩,
    ⟨tree57, 4, withSign negative (1/24)⟩, ⟨tree57, 6, withSign negative (-1/120)⟩, ⟨tree56, 0, 1/180⟩,
    ⟨tree56, 2, -1/120⟩, ⟨tree56, 6, 1/360⟩, ⟨tree55, 0, -1/90⟩,
    ⟨tree55, 4, -1/18⟩, ⟨tree55, 6, 1/15⟩, ⟨tree54, 0, withSign negative (1/180)⟩,
    ⟨tree54, 4, withSign negative (1/36)⟩, ⟨tree54, 6, withSign negative (-1/30)⟩, ⟨tree53, 0, -1/45⟩,
    ⟨tree53, 6, 1/45⟩, ⟨tree52, 0, 1/15⟩, ⟨tree52, 4, -1/9⟩,
    ⟨tree52, 6, 2/45⟩, ⟨tree51, 0, withSign negative (-1/30)⟩, ⟨tree51, 4, withSign negative (1/18)⟩,
    ⟨tree51, 6, withSign negative (-1/45)⟩, ⟨tree50, 0, withSign negative (2/45)⟩, ⟨tree50, 6, withSign negative (-2/45)⟩,
    ⟨tree49, 0, withSign negative (-13/180)⟩, ⟨tree49, 4, withSign negative (1/12)⟩, ⟨tree49, 6, withSign negative (-1/90)⟩,
    ⟨tree48, 0, -1/90⟩, ⟨tree48, 6, 1/90⟩, ⟨tree47, 0, 1/40⟩,
    ⟨tree47, 4, -1/24⟩, ⟨tree47, 6, 1/60⟩, ⟨tree46, 0, -4/45⟩,
    ⟨tree46, 2, 1/6⟩, ⟨tree45, 0, withSign negative (2/45)⟩, ⟨tree45, 2, withSign negative (-1/12)⟩,
    ⟨tree46, 4, -1/9⟩, ⟨tree46, 6, 1/30⟩, ⟨tree45, 4, withSign negative (1/18)⟩,
    ⟨tree45, 6, withSign negative (-1/60)⟩, ⟨tree44, 0, 1/30⟩, ⟨tree44, 4, -1/18⟩,
    ⟨tree44, 6, 1/45⟩, ⟨tree43, 0, withSign negative (-1/60)⟩, ⟨tree43, 4, withSign negative (1/36)⟩,
    ⟨tree43, 6, withSign negative (-1/90)⟩, ⟨tree42, 0, 7/180⟩, ⟨tree42, 2, -1/24⟩,
    ⟨tree42, 6, 1/360⟩, ⟨tree41, 0, -11/180⟩, ⟨tree41, 2, 1/12⟩,
    ⟨tree41, 4, -1/36⟩, ⟨tree41, 6, 1/180⟩, ⟨tree40, 0, withSign negative (11/360)⟩,
    ⟨tree40, 2, withSign negative (-1/24)⟩, ⟨tree40, 4, withSign negative (1/72)⟩, ⟨tree40, 6, withSign negative (-1/360)⟩,
    ⟨tree39, 0, withSign negative (-7/90)⟩, ⟨tree39, 2, withSign negative (1/12)⟩, ⟨tree39, 6, withSign negative (-1/180)⟩,
    ⟨tree38, 0, withSign negative (61/720)⟩, ⟨tree38, 2, withSign negative (-5/48)⟩, ⟨tree38, 4, withSign negative (1/48)⟩,
    ⟨tree38, 6, withSign negative (-1/720)⟩, ⟨tree37, 0, 7/360⟩, ⟨tree37, 2, -1/48⟩,
    ⟨tree37, 6, 1/720⟩, ⟨tree36, 0, withSign negative (1/60)⟩, ⟨tree36, 6, withSign negative (-1/60)⟩,
    ⟨tree35, 0, withSign negative (1/180)⟩, ⟨tree35, 4, withSign negative (1/36)⟩, ⟨tree35, 6, withSign negative (-1/30)⟩,
    ⟨tree34, 0, -1/360⟩, ⟨tree34, 4, -1/72⟩, ⟨tree34, 6, 1/60⟩,
    ⟨tree33, 0, withSign negative (-1/20)⟩, ⟨tree33, 4, withSign negative (1/12)⟩, ⟨tree33, 6, withSign negative (-1/30)⟩,
    ⟨tree32, 0, withSign negative (11/240)⟩, ⟨tree32, 2, withSign negative (-1/16)⟩, ⟨tree32, 4, withSign negative (1/48)⟩,
    ⟨tree32, 6, withSign negative (-1/240)⟩, ⟨tree31, 0, withSign negative (-1/60)⟩, ⟨tree31, 4, withSign negative (1/36)⟩,
    ⟨tree31, 6, withSign negative (-1/90)⟩, ⟨tree30, 0, 1/120⟩, ⟨tree30, 4, -1/72⟩,
    ⟨tree30, 6, 1/180⟩, ⟨tree29, 0, -1/90⟩, ⟨tree29, 6, 1/90⟩,
    ⟨tree28, 0, 1/80⟩, ⟨tree28, 4, -1/48⟩, ⟨tree28, 6, 1/120⟩,
    ⟨tree27, 0, withSign negative (1/720)⟩, ⟨tree27, 6, withSign negative (-1/720)⟩]

private def paths (negative : Bool) : List TimePolynomial :=
  [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative, path5 negative, path6 negative]

private theorem force2_prefix (negative : Bool) :
    forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩]] 2 = force2 negative := by
  cases negative <;> decide +kernel

private theorem integrate2 (negative : Bool) : dirichlet (force2 negative) = path2 negative := by
  cases negative <;> decide +kernel

private theorem step2 (negative : Bool) :
    [[], [⟨direction, 1, 1⟩]] ++ [dirichlet (forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩]] 2)] =
      [[], [⟨direction, 1, 1⟩], path2 negative] := by
  rw [force2_prefix, integrate2]
  simp only [List.cons_append, List.nil_append]

private theorem force3_prefix (negative : Bool) :
    forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative] 3 = force3 negative := by
  cases negative <;> decide +kernel

private theorem integrate3 (negative : Bool) : dirichlet (force3 negative) = path3 negative := by
  cases negative <;> decide +kernel

private theorem step3 (negative : Bool) :
    [[], [⟨direction, 1, 1⟩], path2 negative] ++ [dirichlet (forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative] 3)] =
      [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative] := by
  rw [force3_prefix, integrate3]
  simp only [List.cons_append, List.nil_append]

private theorem force4_prefix (negative : Bool) :
    forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative] 4 = force4 negative := by
  cases negative <;> decide +kernel

private theorem integrate4 (negative : Bool) : dirichlet (force4 negative) = path4 negative := by
  cases negative <;> decide +kernel

private theorem step4 (negative : Bool) :
    [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative] ++ [dirichlet (forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative] 4)] =
      [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative] := by
  rw [force4_prefix, integrate4]
  simp only [List.cons_append, List.nil_append]

private theorem force5_prefix (negative : Bool) :
    forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative] 5 = force5 negative := by
  cases negative <;> decide +kernel

private theorem integrate5 (negative : Bool) : dirichlet (force5 negative) = path5 negative := by
  cases negative <;> decide +kernel

private theorem step5 (negative : Bool) :
    [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative] ++ [dirichlet (forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative] 5)] =
      [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative, path5 negative] := by
  rw [force5_prefix, integrate5]
  simp only [List.cons_append, List.nil_append]

private theorem force6_prefix (negative : Bool) :
    forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative, path5 negative] 6 = force6 negative := by
  cases negative <;> decide +kernel

private theorem integrate6 (negative : Bool) : dirichlet (force6 negative) = path6 negative := by
  cases negative <;> decide +kernel

private theorem step6 (negative : Bool) :
    [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative, path5 negative] ++ [dirichlet (forcing (withSign negative 1) [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative, path5 negative] 6)] =
      [[], [⟨direction, 1, 1⟩], path2 negative, path3 negative, path4 negative, path5 negative, path6 negative] := by
  rw [force6_prefix, integrate6]
  simp only [List.cons_append, List.nil_append]

private theorem paths_checked (negative : Bool) : signedPaths (withSign negative 1) = paths negative := by
  unfold signedPaths paths
  rw [List.foldl_cons, step2, List.foldl_cons, step3, List.foldl_cons, step4, List.foldl_cons, step5, List.foldl_cons, step6]
  rfl

private def boundaryTest (negative : Bool) (n : ℕ) : Bool :=
  let p := (paths negative)[n]?.getD []
  same (differentiate (differentiate p)) (forcing (withSign negative 1) (paths negative) n) &&
    same (atTime p (-1)) [] && same (atTime p 1) []

private theorem force2_full (negative : Bool) :
    forcing (withSign negative 1) (paths negative) 2 = force2 negative := by
  cases negative <;> decide +kernel

private theorem boundary2 (negative : Bool) : boundaryTest negative 2 = true := by
  unfold boundaryTest
  change (same (differentiate (differentiate (path2 negative))) (forcing (withSign negative 1) (paths negative) 2) &&
    same (atTime (path2 negative) (-1)) [] && same (atTime (path2 negative) 1) []) = true
  rw [force2_full]
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  all_goals cases negative <;> as_aux_lemma => decide +kernel

private theorem force3_full (negative : Bool) :
    forcing (withSign negative 1) (paths negative) 3 = force3 negative := by
  cases negative <;> decide +kernel

private theorem boundary3 (negative : Bool) : boundaryTest negative 3 = true := by
  unfold boundaryTest
  change (same (differentiate (differentiate (path3 negative))) (forcing (withSign negative 1) (paths negative) 3) &&
    same (atTime (path3 negative) (-1)) [] && same (atTime (path3 negative) 1) []) = true
  rw [force3_full]
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  all_goals cases negative <;> as_aux_lemma => decide +kernel

private theorem force4_full (negative : Bool) :
    forcing (withSign negative 1) (paths negative) 4 = force4 negative := by
  cases negative <;> decide +kernel

private theorem boundary4 (negative : Bool) : boundaryTest negative 4 = true := by
  unfold boundaryTest
  change (same (differentiate (differentiate (path4 negative))) (forcing (withSign negative 1) (paths negative) 4) &&
    same (atTime (path4 negative) (-1)) [] && same (atTime (path4 negative) 1) []) = true
  rw [force4_full]
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  all_goals cases negative <;> as_aux_lemma => decide +kernel

private theorem force5_full (negative : Bool) :
    forcing (withSign negative 1) (paths negative) 5 = force5 negative := by
  cases negative <;> decide +kernel

private theorem boundary5 (negative : Bool) : boundaryTest negative 5 = true := by
  unfold boundaryTest
  change (same (differentiate (differentiate (path5 negative))) (forcing (withSign negative 1) (paths negative) 5) &&
    same (atTime (path5 negative) (-1)) [] && same (atTime (path5 negative) 1) []) = true
  rw [force5_full]
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  all_goals cases negative <;> as_aux_lemma => decide +kernel

private theorem force6_full (negative : Bool) :
    forcing (withSign negative 1) (paths negative) 6 = force6 negative := by
  cases negative <;> decide +kernel

private theorem boundary6 (negative : Bool) : boundaryTest negative 6 = true := by
  unfold boundaryTest
  change (same (differentiate (differentiate (path6 negative))) (forcing (withSign negative 1) (paths negative) 6) &&
    same (atTime (path6 negative) (-1)) [] && same (atTime (path6 negative) 1) []) = true
  rw [force6_full]
  simp only [Bool.and_eq_true]
  repeat' apply And.intro
  all_goals cases negative <;> as_aux_lemma => decide +kernel

private theorem boundaries (negative : Bool) : boundaryEquations (withSign negative 1) = true := by
  unfold boundaryEquations
  rw [paths_checked]
  change [2, 3, 4, 5, 6].all (boundaryTest negative) = true
  simp only [List.all_cons, List.all_nil, boundary2, boundary3, boundary4, boundary5, boundary6, Bool.and_self]

theorem positiveBoundary : boundaryEquations 1 = true := boundaries false
theorem negativeBoundary : boundaryEquations (-1) = true := boundaries true

theorem quarticCoefficient : same (midpointCoefficient 4) quartic = true := by
  have hp : signedPaths 1 = paths false := paths_checked false
  have hm : signedPaths (-1) = paths true := paths_checked true
  rw [midpointCoefficient, hp, hm]
  decide +kernel

theorem sixthCoefficient : same (midpointCoefficient 6) (affineSixth ++ higherSixth) = true := by
  have hp : signedPaths 1 = paths false := paths_checked false
  have hm : signedPaths (-1) = paths true := paths_checked true
  rw [midpointCoefficient, hp, hm]
  decide +kernel

end EuclideanMidpointRigidity.Jet.DirichletTables
