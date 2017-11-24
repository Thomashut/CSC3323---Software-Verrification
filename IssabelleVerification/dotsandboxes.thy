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
 
definition
  outOfBounds :: "cord \<Rightarrow> \<bool>"
where
  "outOfBounds c \<equiv> (xcord c) \<le> GRID_WIDTH \<or> (ycord c) \<le> GRID_HEIGHT"
  
(* to-do *)
definition
  testNorthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
where
  "testNorthVertex c play \<equiv> False "
  
(* to-do *)
definition
  testWestVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
where
  "testWestVertex c play \<equiv> False "
  
(* to-do *)
definition
  testEastVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
where
  "testEastVertex c play \<equiv> False "
  
(* to-do *)
definition
  testSouthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
where
  "testSouthVertex c play \<equiv> False "
  
(* to-do *)
definition
  upNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
where
  "upNeighbourTest c play capturedAnchors \<equiv> False"
  
(* to-do *)
definition
  rightNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
where
  "rightNeighbourTest c play capturedAnchors \<equiv> False"
  
(* to-do *)
definition
  leftNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
where
  "leftNeighbourTest c play capturedAnchors \<equiv> False"
  
(* to-do *)
definition
  downNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
where
  "downNeighbourTest c play capturedAnchors \<equiv> False"
  

definition
  validBoxTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
where
  "validBoxTest c play \<equiv> testNorthVertex c play \<and>
                          testEastVertex c play \<and>
                          testWestVertex c play \<and>
                          testSouthVertex c play"

(* to-do *)
definition
  testForDoubleBoxCompletion :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> cord"
where
  "testForDoubleBoxCompletion c play capturedAnchors \<equiv> if upNeighbourTest c play capturedAnchors then c 
    else if rightNeighbourTest c play capturedAnchors then c 
    else if leftNeighbourTest c play capturedAnchors then c
    else if downNeighbourTest c play capturedAnchors then c
    else c "
  
definition
  testForBoxCompletion :: "move \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
where
  "testForBoxCompletion m play \<equiv> if outOfBounds (c1 m) then False else validBoxTest (c1 m) play"
  
(*==============================================================*)
section{*Invarients, Pres and Posts *}

(* to-do *)
definition
  pre_captureAnchors ::  "move \<Rightarrow> player \<Rightarrow> \<bool>"
  where
  "pre_capturedAnchors m currentplayer \<equiv> testForBoxCompletion m"

(* to-do *)
definition
  pre_makeAMove :: "move \<Rightarrow> \<bool>"
where
  "pre_makeAMove m \<equiv> False"
  
(* NOTE TO SELF, NEED TO CREATE THE PRES FOR EVERY SINGLE FUNCTION ABOVE TO TEST THEIR INVS
    ON THE TYPES *)

(*==============================================================*)
section{*VDMstate*}

  (* need to figure out how to create state *)

(*==============================================================*)
section{*VDMoperations*}
  
(* to-do *)  
definition
  captureAnchor :: "move \<Rightarrow> player \<Rightarrow> ()"
where
  "captureAnchor m currentPlayer \<equiv> "
  
(* to-do *)
definition
  saveTheMove :: "move \<Rightarrow> ()"
where
  "saveTheMove m \<equiv> False"
  
(* to-do *)
definition
  makeAMove :: "move \<Rightarrow> ()"
where
  "makeAMove m \<equiv> False"    
  



(*==============================================================*)
section{*VDMproofobligations*}


end