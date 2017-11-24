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
 "GRID_WIDTH \<equiv> (5::VDMNat1)"

abbreviation
  "GRID_HEIGHT \<equiv> (5::VDMNat1)"


(*==============================================================*)
section{*VDMtypes and their Invarients*}
datatype
  player = P1 | P2

record cord =
  xcord :: VDMNat1
  ycord :: VDMNat1

definition
  inv_cord :: "cord \<Rightarrow> \<bool>"
where
  "inv_cord c1 \<equiv> (inv_VDMNat1 (xcord c1)) \<and> (inv_VDMNat1 (ycord c1))
        \<and> (xcord c1) \<le> GRID_WIDTH \<and> (ycord c1) \<le> GRID_HEIGHT" 


record move =
  c1 :: cord
  c2 :: cord
  
type_synonym 
  bonusTurn = \<bool>

type_synonym
  turn = player

type_synonym
  play = "move VDMSet"

(*==============================================================*)
section{*VDMfunctions*}

definition
  testHorizontalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testHorizontalMove cord1 cord2 \<equiv> (inv_cord cord1) \<and> (inv_cord cord2) 
      \<and> abs((xcord cord1) - (xcord cord2)) = (1::VDMNat) \<and> (ycord cord1) = (ycord cord2)"
    
definition
  testVerticalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testVerticalMove cord1 cord2 \<equiv> (inv_cord cord1) \<and> (inv_cord cord2)
      \<and> abs((ycord cord1) - (ycord cord2)) = (1::VDMNat) \<and> (xcord cord1) = (xcord cord2)"
    
definition
  testValidMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testValidMove cord1 cord2 \<equiv> (testVerticalMove cord1 cord2) 
        \<or> (testHorizontalMove cord1 cord2) \<and> ((inv_cord cord1) \<and> (inv_cord cord2))"
    
definition
  testNormalisedMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testNormalisedMove cord1 cord2 \<equiv> (xcord cord1) \<le> (xcord cord2) 
      \<or> (ycord cord1) \<le> (ycord cord2)" 
    
definition
  inv_move :: "move \<Rightarrow> \<bool>"
where
  "inv_move m \<equiv> inv_cord (c1 m) \<and> inv_cord (c2 m) \<and> (testValidMove (c1 m) (c2 m)) 
    \<and> testNormalisedMove (c1 m) (c2 m) "

(* to-do *)  
definition
  normaliseMove :: "move \<Rightarrow> move"
  where
    "normaliseMove m \<equiv> m"
    
definition
  anchorNotCaputred :: "cord \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
where
  "anchorNotCaputred cord1 capturedAnchors \<equiv> (cord1 \<notin> capturedAnchors) \<and> (inv_cord cord1)
    \<and> inv_SetElems inv_cord capturedAnchors "

(*==============================================================*)
section{*VDMstate*}


(*==============================================================*)
section{*VDMoperations*}


(*==============================================================*)
section{*VDMproofobligations*}


end