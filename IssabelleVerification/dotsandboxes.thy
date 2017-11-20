theory dotsandboxes
  imports Main "VDMToolkit"

begin

text{* NAME DOTSANDBOXES *}

(*==============================================================*)
section{*Introduction*}

text{*
  Author: Thomas Hutchinson
  File  : dotsandboxes.thy
  Description:
    Provide mathematical proof that the dots and boxes vdm model works correctly.
    See dotsandboxesV2.vdmsl for full description of the game as well as the manner
    of implimentation.
  Proves: dotsandboxesV2.vdmsl
  *}

(*==============================================================*)
section{*VDMvalues*}
abbreviation
  GRID_WIDTH \<equiv> (5::VDMNat1)

abbreviation
  GRID_HEIGHT \<equiv> (5::VDMNat1)


(*==============================================================*)
section{*VDMtypes and their Invarients*}
datatype
  player = P1 | P2

record cord =
  xcord :: VDMNat1
  ycord :: VDMNat1

definition
  inv-cord :: cord \<Rightarrow> \<bool>
where
  "inv-cord c \<equiv> (xcord c) \<le> GRID_WIDTH \<and> (ycord c) \<le> GRID_HEIGHT" 


record move =
  c1 :: cord
  c2 :: cord

definition
  inv-move :: move \<Rightarrow> \<bool>
where
 "inv-move m \<equiv> (testValidMove (m c1) (m c2)) \<and> (m (c1 x)) \<le> (m (c2 x)) \<and> (m (c1 y) \<le> (m (c2 y))" 

type_synonym 
  bonusTurn = \<bool>

type_synonym
  turn = player

type_synonym
  play = "move VDMSet"

(*==============================================================*)
section{*VDMfunctions*}

definition
  testHorizontalMove cord * cord \<Rightarrow> \<bool>
where
  "testHorizontalMove c1, c2 \<equiv> (inv-cord c1) \<and> (inv-cord c2) \<and> ((c1 x) - (c2 x) = (1::nat)) \<and>
    (c1 y) = (c2 y)"

definition
  testVerticalMove cord * cord \<Rightarrow> \<bool>
where
  "testVerticalMove c1,c2 \<equiv> (inv-cord c1) \<and> (inv-cord c2) \<and> ((c1 y) - (c2 y) = (1::nat)) \<and>
    (c1 x) = (c2 x)"

definition
  testValidMove cord * cord \<Rightarrow> \<bool>
where
  "testValidMove c1,c2 \<equiv> (inv-cord c1) \<and> (inv-cord c2) \<and> ((testVerticalMove c1 c2) \<or>
    (testHorizontalMove c1 c2))"

definition
  outOfBounds cord \<Rightarrow> \<bool>
where
  "outOfBounds c \<equiv> (xcord c) = (GRID_WIDTH \<or> (ycord c) = GRID_HEIGHT) \<and> (inv-cord c)"

definition
  squaresLeft cord VDMSet \<Rightarrow> nat
where
 " squaresLeft c \<equiv> ((GRID_WIDTH - 1) * (GRID_HEIGHT - 1)) - (*sizeof*) c"


(*==============================================================*)
section{*VDMstate*}


(*==============================================================*)
section{*VDMoperations*}


(*==============================================================*)
section{*VDMproofobligations*}


end