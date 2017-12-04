theory dotsandboxesv2
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
section{*VDMTypes*}
  
datatype
  player = P1 | P2
  
(*==============================================================*)
subsection{*cord*}
  
record cord =
  xcord :: VDMNat1
  ycord :: VDMNat1
  
definition
  inv_cord :: "cord \<Rightarrow> \<bool>"
  where
    "inv_cord c1 \<equiv> (inv_VDMNat1 (xcord c1)) \<and> (inv_VDMNat1 (ycord c1))
          \<and> (xcord c1) \<le> GRID_WIDTH \<and> (ycord c1) \<le> GRID_HEIGHT"

(*==============================================================*)
subsection{*move*}
  
record move =
  c1 :: cord
  c2 :: cord
 
(*==============================================================*)
subsection{*state*}
  
type_synonym
  capturedPoints = "cord \<rightharpoonup> player"  

record state =
   play       :: "move VDMSet"
   turn       :: player
   bonusTurn  :: \<bool>
   capturedAnchors :: capturedPoints
   
(*==============================================================*)
section{*VDMFunctions*}
  
definition
  anchorNotCaputred :: "cord \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "anchorNotCaputred cord1 captured_Anchors \<equiv> (cord1 \<notin> captured_Anchors) \<and> (inv_cord cord1)
      \<and> inv_SetElems inv_cord captured_Anchors "
    
definition
  pre_anchorNotCaptured :: "cord \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_anchorNotCaptured cord1 captured_Anchors \<equiv> inv_cord cord1 \<and> 
      inv_SetElems inv_cord captured_Anchors "
    
definition
  post_anchorNotCaptured :: "cord \<Rightarrow> cord VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_anchorNotCaptured cord1 captured_Anchors RESULT \<equiv> 
      if cord1 \<notin> captured_Anchors then RESULT = True 
        else if cord1 \<in> captured_Anchors then RESULT = False
          else RESULT = False "
    
(*==============================================================*)
subsection{*testHorizontalMove*}

definition
  testHorizontalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testHorizontalMove cord1 cord2 \<equiv> (inv_cord cord1) \<and> (inv_cord cord2) 
      \<and> abs((xcord cord1) - (xcord cord2)) = (1::VDMNat) \<and> (ycord cord1) = (ycord cord2)"
    
definition
  pre_TestHorizontalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_TestHorizontalMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"
    
definition
  post_TestHorizontalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_TestHorizontalMove cord1 cord2 RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*testVerticalMove*}

definition
  testVerticalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testVerticalMove cord1 cord2 \<equiv> (inv_cord cord1) \<and> (inv_cord cord2)
      \<and> abs((ycord cord1) - (ycord cord2)) = (1::VDMNat) \<and> (xcord cord1) = (xcord cord2)"
  
definition
  pre_TestVerticalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_TestVerticalMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"
    
definition
  post_TestVerticalMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_TestVerticalMove cord1 cord2 RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*testValidMove*}    

definition
  testValidMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testValidMove cord1 cord2 \<equiv> (testVerticalMove cord1 cord2) 
        \<or> (testHorizontalMove cord1 cord2) \<and> ((inv_cord cord1) \<and> (inv_cord cord2))"
    
definition
  pre_testValidMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_testValidMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"
    
definition
  post_testValidMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testValidMove cord1 cord2 RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*testNormalisedMove*}

definition
  testNormalisedMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "testNormalisedMove cord1 cord2 \<equiv> (xcord cord1) \<le> (xcord cord2) 
      \<or> (ycord cord1) \<le> (ycord cord2)"   

definition
  pre_testNormalisedMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_testNormalisedMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"
    
definition
  post_testNormalisedMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testNormalisedMove cord1 cord2 RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*inv_move*}
  
definition
  inv_move :: "move \<Rightarrow> \<bool>"
  where
    "inv_move m \<equiv> inv_cord (c1 m) \<and> inv_cord (c2 m) \<and> (testValidMove (c1 m) (c2 m)) 
      \<and> testNormalisedMove (c1 m) (c2 m) "
    
(*==============================================================*)
subsection{*outofbounds*}

definition
  outOfBounds :: "cord \<Rightarrow> \<bool>"
  where
    "outOfBounds c \<equiv> (xcord c) \<le> GRID_WIDTH \<or> (ycord c) \<le> GRID_HEIGHT"
  
definition
  pre_outOfBounds :: "cord \<Rightarrow> \<bool>"
  where
    "pre_outOfBounds cord1 \<equiv> inv_cord cord1"
    
definition
  post_outOfBounds :: "cord \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_outOfBounds cord1 RESULTS \<equiv> True"
    
(*==============================================================*)
subsection{*testNorthVertex*}

definition
  testNorthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testNorthVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c + (1::VDMNat1) \<rparr>,
                                    c2 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c + (1::VDMNat1) \<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  post_testNorthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testNorthVertex c set_play RESULT \<equiv> True"

(*==============================================================*)
subsection{*testWestVertex*}
  
definition
  testWestVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testWestVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c\<rparr>,
                                    c2 = \<lparr>xcord = xcord c, ycord = ycord c + (1::VDMNat1) \<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  post_testWestVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testWestVertex c set_play RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*testEastVertex*}
  
definition
  testEastVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testEastVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c \<rparr>,
                                    c2 = \<lparr>xcord = xcord c + (1::VDMNat1), ycord = ycord c + (1::VDMNat1) \<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  post_testEastVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testEastVertex c set_play RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*testsouthVertex*}

definition
  testSouthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testSouthVertex c set_play \<equiv> \<lparr> c1 = \<lparr>xcord = xcord c, ycord = ycord c\<rparr>,
                                    c2 = \<lparr>xcord = xcord c + (1::VDMNat1) , ycord = ycord c\<rparr>
                                  \<rparr> \<in> set_play "
    
definition
  post_testSouthVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testSouthVertex c set_play RESULT \<equiv> True"
(*==============================================================*)
subsection{*testVertex*}

(* this is the pre condition for all of the above test vertex functions *)  
  
definition
  pre_testVertex :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "pre_testVertex c set_play \<equiv> inv_cord c \<and> inv_SetElems inv_move set_play"
    
(*==============================================================*)
subsection{*validBoxTest*}
  
definition
  validBoxTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "validBoxTest c set_play \<equiv> (testNorthVertex c set_play) \<and>
                          (testEastVertex c set_play) \<and>
                          (testWestVertex c set_play) \<and>
                          (testSouthVertex c set_play)"
    
definition
  pre_validBoxTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "pre_validBoxTest c set_play \<equiv> inv_cord c \<and> inv_SetElems inv_move set_play"
    
definition
  post_validBoxTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_validBoxTest c set_play RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*testforboxcompletion*}
    
definition
  testForBoxCompletion :: "move \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "testForBoxCompletion m set_play \<equiv> if outOfBounds (c1 m) then False else validBoxTest (c1 m) set_play"

definition
  pre_testForBoxCompletion :: "move \<Rightarrow> move VDMSet \<Rightarrow> \<bool>"
  where
    "pre_testForBoxCompletion m set_play \<equiv> inv_move m \<and> inv_SetElems inv_move set_play"
    
definition
  post_testForBoxCompletion :: "move \<Rightarrow> move VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testForBoxCompletion m set_play RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*upNeighbourTest*}
  
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
  post_upNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_upNeighbourTest c set_play captured_Anchors RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*rightNeighbourTest*}
  
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
  post_rightNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_rightNeighbourTest c set_play captured_Anchors RESULT \<equiv> True"
    
(*==============================================================*)
subsection{*leftNeighbourTest*}
  
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
  post_leftNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_leftNeighbourTest c set_play captured_Anchors RESULT \<equiv> True"    
    
(*==============================================================*)
subsection{*downNeighbourTest*}    

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
  post_downNeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_downNeighbourTest c set_play captured_Anchors RESULT \<equiv> True"       
    
(*==============================================================*)
subsection{*NeighbourTest*}
  
(* this is the pre test for all the above neighbour tests *)  
  
definition
  pre_NeighbourTest :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_NeighbourTest c set_play captured_Anchors \<equiv> inv_cord c \<and> inv_SetElems inv_move set_play \<and>
      inv_SetElems inv_cord captured_Anchors"
    
(*==============================================================*)
subsection{*testForDobuleBoxCompletion*}
  
definition
  testForDoubleBoxCompletion :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> cord"
  where
    "testForDoubleBoxCompletion c set_play captured_Anchors \<equiv> 
      if upNeighbourTest c set_play captured_Anchors then \<lparr>xcord = (xcord c), ycord = (ycord c + (1::VDMNat1))\<rparr> 
      else if downNeighbourTest  c set_play captured_Anchors then \<lparr>xcord = (xcord c), ycord = (ycord c - (1::VDMNat1))\<rparr> 
      else if rightNeighbourTest  c set_play captured_Anchors then \<lparr>xcord = (xcord c + (1::VDMNat1)), ycord = (ycord c)\<rparr>
      else if leftNeighbourTest c set_play captured_Anchors then \<lparr>xcord = (xcord c - (1::VDMNat1)), ycord = (ycord c)\<rparr>
      else c "
    
definition
  pre_testForDoubleBoxCompletion :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_testForDoubleBoxCompletion c set_play captured_Anchors \<equiv> inv_cord c \<and>
      inv_SetElems inv_move set_play \<and> inv_SetElems inv_cord captured_Anchors"
    
definition
  post_testForDobuleBoxCompletion :: "cord \<Rightarrow> move VDMSet \<Rightarrow> cord VDMSet \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_testForDobuleBoxCompletion c set_play captured_Anchors RESULT \<equiv> True"

(*==============================================================*)
subsection{*inv_player*}
  
definition
  inv_player :: "player \<Rightarrow> \<bool>"
  where
    "inv_player p \<equiv> (p = P1) \<or> (p = P2)"
    
(*==============================================================*)
subsection{*init_state*}
  
definition
  init_state :: "move VDMSet \<Rightarrow> player \<Rightarrow> \<bool> \<Rightarrow> capturedPoints  \<Rightarrow> state"
  where
    "init_state p t bt ca \<equiv> \<lparr> play = p, turn = t, bonusTurn = bt, capturedAnchors = ca \<rparr>" 
    
(*==============================================================*)
subsection{*inv_state*}

definition
  inv_state :: "state \<Rightarrow> \<bool>"
  where
    "inv_state s \<equiv> (inv_SetElems inv_move (play s)) \<and> (inv_Map inv_cord inv_player (capturedAnchors s))
      \<and> inv_player (turn s)"
    
(*==============================================================*)
subsection{*captureAnchor*}
 
definition
  captureAnchor :: "move \<Rightarrow> player \<Rightarrow> state \<Rightarrow> state"
  where
    "captureAnchor m currentPlayer currentState \<equiv> 
      \<lparr>play = (play currentState), turn = (turn currentState), bonusTurn = (bonusTurn CurrentState),
        capturedAnchors = ((capturedAnchors currentState) munion [ (c1 m) \<mapsto> currentPlayer ]) \<rparr>"

definition
  pre_captureAnchor :: "move \<Rightarrow> player \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_captureAnchor m currentPlayer currentState \<equiv> inv_move m \<and> inv_player currentPlayer \<and>
      testForBoxCompletion m (play currentState) "
    
definition
  post_captureAnchor :: "move \<Rightarrow> player \<Rightarrow> state \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_captureAnchor m currentPlayer currentState RESULT \<equiv> True" 
    
(*==============================================================*)
subsection{*saveTheMove*}

definition
  saveTheMove :: "move \<Rightarrow> state \<Rightarrow> state \<times> cord"
  where
    "saveTheMove m currentState \<equiv>( \<lparr>play = (play currentState) \<union> {m},
                      turn = turn currentState,
                      bonusTurn = bonusTurn currentState,
                      capturedAnchors = capturedAnchors currentState\<rparr>,
      (testForDoubleBoxCompletion (c1 m) (play currentState) (dom (capturedAnchors currentState))) ) "
    
definition
  pre_saveTheMove :: "move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_saveTheMove m currentState \<equiv> inv_move m \<and> inv_state currentState "
    
definition
  post_saveTheMove :: "move \<Rightarrow> \<bool> \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_saveTheMove m RESULT RESULT_STATE \<equiv> True"
 
(*==============================================================*)
subsection{*makeAMove*}
  
definition
  makeAMove :: "move \<Rightarrow> state \<Rightarrow> state"
  where
    "makeAMove m gameState \<equiv> gameState"
    
definition
  pre_makeAMove :: "move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_makeAMove m currentState \<equiv> inv_move m \<and> m \<notin> (play currentState) "
    
definition
  post_makeAMove :: "move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_makeAMove m RESULT \<equiv> True"
 
(*==============================================================*)
subsection{*SquaresLeft*}
  
definition
  SquaresLeft :: "cord VDMSet \<Rightarrow> VDMNat"
  where
    "SquaresLeft capturedAnchors \<equiv> (((GRID_WIDTH -1 ) * (GRID_HEIGHT - 1)) - (vdm_card capturedAnchors))"

definition
  pre_SquaresLeft :: "cord VDMSet \<Rightarrow> \<bool>"
  where
    "SquaresLeft capturedAnchors \<equiv> inv_SetElems inv_cord capturedAnchors"
    
(*==============================================================*)