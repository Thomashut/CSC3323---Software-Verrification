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
  
record state =
   play       :: "move VDMSet"
   turn       :: player
   bonusTurn  :: \<bool>
   capturedAnchors :: "player \<rightharpoonup> cord"
   
type_synonym 
  bonusTurn = \<bool>

type_synonym
  turn = player

type_synonym
  play = "move VDMSet"

(*==============================================================*)
section{*VDMfunctions*}
  
definition
  anchorNotCaputred :: "cord \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "anchorNotCaputred cord1 captured_Anchors \<equiv> (cord1 \<notin> captured_Anchors) \<and> (inv_cord cord1)
      \<and> inv_SetElems inv_cord captured_Anchors "
  
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
 
definition
  normaliseMove :: "move \<Rightarrow> move"
  where
    "normaliseMove m \<equiv> \<lparr>c1 = c2 m, c2 = c1 m\<rparr>"
   

    
definition
  outOfBounds :: "cord \<Rightarrow> \<bool>"
  where
    "outOfBounds c \<equiv> (xcord c) \<le> GRID_WIDTH \<or> (ycord c) \<le> GRID_HEIGHT"


    

    

  
definition
  testNorthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testNorthVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c + (1::VDMNat1) \<rparr>,
                                    c2 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c + (1::VDMNat1) \<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  testWestVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testWestVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c\<rparr>,
                                    c2 = \<lparr>xcord = xcord c, ycord = ycord c + (1::VDMNat1) \<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  testEastVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testEastVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c \<rparr>,
                                    c2 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c + (1::VDMNat1) \<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  testSouthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testSouthVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c\<rparr>,
                                    c2 = \<lparr>xcord = xcord c + (1::VDMNat1) , ycord = ycord c\<rparr>
                                  \<rparr> \<in> set_play "

    
definition
  validBoxTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "validBoxTest c set_play \<equiv> (testNorthVertex c set_play) \<and>
                          (testEastVertex c set_play) \<and>
                          (testWestVertex c set_play) \<and>
                          (testSouthVertex c set_play)"

    
definition
  testForBoxCompletion :: "move \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testForBoxCompletion m set_play \<equiv> if outOfBounds (c1 m) then False else validBoxTest (c1 m) set_play"


definition
  upNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "upNeighbourTest c set_play captured_Anchors \<equiv> 
      if( ( ycord c + (1::VDMNat1)) > (GRID_HEIGHT - (1::VDMNat1)) ) then
        False
      else if ( \<lparr>xcord = xcord c, ycord = ycord c + (1::VDMNat1)\<rparr> \<notin> captured_Anchors ) then
        testForBoxCompletion \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c + (1::VDMNat1)\<rparr>,
                               c2 = \<lparr>xcord = xcord c, ycord = ycord c + (2::VDMNat1)\<rparr> \<rparr> set_play
      else
        False
    "
    
definition
  rightNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "rightNeighbourTest c set_play captured_Anchors \<equiv> 
      if( ( ycord c + (1::VDMNat1)) > (GRID_HEIGHT - (1::VDMNat1)) ) then
        False
      else if ( \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c\<rparr> \<notin> captured_Anchors ) then
        testForBoxCompletion \<lparr> c1 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c\<rparr>,
                               c2 = \<lparr>xcord = xcord c + (2::VDMNat1), ycord = ycord c\<rparr> \<rparr> set_play
      else
        False
    "
    
definition
  leftNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "leftNeighbourTest c set_play captured_Anchors \<equiv> 
      if( ( ycord c + (1::VDMNat1)) > (GRID_HEIGHT - (1::VDMNat1)) ) then
        False
      else if ( \<lparr>xcord = xcord c - (1::VDMNat1), ycord = ycord c\<rparr> \<notin> captured_Anchors ) then
        testForBoxCompletion \<lparr> c1 = \<lparr>xcord = xcord c - (1::VDMNat1), ycord = ycord c\<rparr>,
                               c2 = \<lparr>xcord = xcord c, ycord = ycord c\<rparr> \<rparr> set_play
      else
        False
    "
    
definition
  downNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "downNeighbourTest c set_play captured_Anchors \<equiv> 
      if( ( ycord c + (1::VDMNat1)) > (GRID_HEIGHT - (1::VDMNat1)) ) then
        False
      else if ( \<lparr>xcord = xcord c, ycord = ycord c - (1::VDMNat1)\<rparr> \<notin> captured_Anchors ) then
        testForBoxCompletion \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c - (1::VDMNat1)\<rparr>,
                               c2 = \<lparr>xcord = xcord c, ycord = ycord c\<rparr> \<rparr> set_play
      else
        False
    "
  
  


    
definition
  testForDoubleBoxCompletion :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> cord"
  where
    "testForDoubleBoxCompletion c set_play captured_Anchors \<equiv> 
      if upNeighbourTest c set_play captured_Anchors then \<lparr>xcord = (xcord c), ycord = (ycord c + (1::VDMNat1))\<rparr> 
      else if downNeighbourTest  c set_play captured_Anchors then \<lparr>xcord = (xcord c), ycord = (ycord c - (1::VDMNat1))\<rparr> 
      else if rightNeighbourTest  c set_play captured_Anchors then \<lparr>xcord = (xcord c + (1::VDMNat1)), ycord = (ycord c)\<rparr>
      else if leftNeighbourTest c set_play captured_Anchors then \<lparr>xcord = (xcord c - (1::VDMNat1)), ycord = (ycord c)\<rparr>
      else c "
 
     
(*==============================================================*)
section{*Invarients, Pres and Posts *}
  
(* NOTE TO SELF, NEED TO CREATE THE PRES FOR EVERY SINGLE FUNCTION ABOVE TO TEST THEIR INVS
    ON THE TYPES *)
  
definition
  pre_TestHorizontalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_TestHorizontalMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"
    
definition
  pre_TestVerticalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_TestVerticalMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"
    
definition
  pre_testValidMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_testValidMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"

definition
  pre_testNormalisedMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_testNormalisedMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"

definition
  pre_anchorNotCaptured :: "cord \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_anchorNotCaptured cord1 captured_Anchors \<equiv> inv_cord cord1 \<and> 
      inv_SetElems inv_cord captured_Anchors "
    
definition
  pre_outOfBounds :: "cord \<Rightarrow> \<bool>"
  where
    "pre_outOfBounds cord1 \<equiv> inv_cord cord1"
    
(* Pre_condition for all of the testVertex functions (north, east, west and south) *)    
definition
  pre_testVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "pre_testVertex c set_play \<equiv> inv_cord c \<and> inv_SetElems inv_move set_play"
    
(* Pre_Condition for all of the neighbour test functions (Up,left,right and down) *)    
definition
  pre_NeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_NeighbourTest c set_play captured_Anchors \<equiv> inv_cord c \<and> inv_SetElems inv_move set_play \<and>
      inv_SetElems inv_cord captured_Anchors"
    
definition
  pre_validBoxTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "pre_validBoxTest c set_play \<equiv> inv_cord c \<and> inv_SetElems inv_move set_play"

definition
  pre_testForDoubleBoxCompletion :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_testForDoubleBoxCompletion c set_play captured_Anchors \<equiv> inv_cord c \<and>
      inv_SetElems inv_move set_play \<and> inv_SetElems inv_cord captured_Anchors"

definition
  pre_testForBoxCompletion :: "move \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "pre_testForBoxCompletion m set_play \<equiv> inv_move m \<and> inv_SetElems inv_move set_play"
    
definition
  inv_player :: "player \<Rightarrow> \<bool>"
  where
    "inv_player p \<equiv> p = P1 \<or> p = P2"

definition
  pre_captureAnchor :: "move \<Rightarrow> player \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_captureAnchor m currentPlayer currentState \<equiv> inv_move m \<and> inv_player currentPlayer \<and>
      testForBoxCompletion m (play currentState) "
    
definition
  pre_saveTheMove :: "move \<Rightarrow> \<bool>"
  where
    "pre_saveTheMove m \<equiv> inv_move m"

definition
  pre_makeAMove :: "move \<Rightarrow> \<bool>"
  where
    "pre_makeAMove m \<equiv> inv_move m"
   
(*==============================================================*)
section{*VDMstate*}

  (* need to figure out how to create state *)

(*==============================================================*)
section{*VDMoperations*}
  
(* to-do *)  
definition
  captureAnchor :: "move \<Rightarrow> player \<Rightarrow> state \<Rightarrow> state"
  where
    "captureAnchor m currentPlayer currentState \<equiv> ((capturedAnchors currentState) munion \<lparr> currentPlayer \<rightharpoonup> (c1 m) \<rparr>) state"
  
(* to-do *)
definition
  saveTheMove :: "move \<Rightarrow> state \<Rightarrow> cord"
  where
    "saveTheMove m currentState \<equiv> \<lparr>play = (play current state) \<union> m,
                      turn = turn currentState,
                      bonusTurn = bonusTurn currentState,
                      capturedAnchors = capturedAnchors currentState\<rparr> 
      testForBoxCompletion((c1 m) (play currentState) range (capturedAnchors currentState))"
  
(* to-do *)
definition
  makeAMove :: "move \<Rightarrow> state"
  where
    "makeAMove m \<equiv> False"
  
definition
  playGame :: "move \<Rightarrow> state"
  where
    "playGame m \<equiv> gah!"    
  



(*==============================================================*)
section{*VDMproofobligations*}


end