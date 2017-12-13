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
    of implimentation. There are additional functions compared to the model and that
    is due to the limitations and differences of Isabelle. I also broke down
    some of the more complex operations into several smaller operations such as
    the makeAMove operation which in the first itteration of the model was huge
    and would have been very difficult to translate to Isabelle. Just about every
    operation has a satisfiability check just below it in a lemma. Most of the
    functions do not have these checks as they do not contain post states making
    it a trivial to prove a lot of them
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
          \<and> (xcord c1) \<le> GRID_WIDTH \<and> (ycord c1) \<le> GRID_HEIGHT
          \<and> ((xcord c1) \<ge> (0::VDMNat) \<and> (ycord c1) \<ge> (0::VDMNat))"
    
lemma cordSatisfiability : "\<exists> c . inv_cord c = True"
  unfolding inv_cord_def inv_VDMNat1_def
    sledgehammer
    by (metis less_imp_le order_refl select_convs(1) select_convs(2) zero_less_numeral)
      
   
(*==============================================================*)
subsection{*move*}
  
record move =
  c1 :: cord
  c2 :: cord
  
(* Invarient further down due to dependancies *)
 
(*==============================================================*)
subsection{*state*}  

type_synonym
  capturedPoints = "(cord \<rightharpoonup> player)"  
  
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
    
lemma anchorNotCapturedSatisifability: "\<exists> (c::cord) (ca::cord VDMSet) . 
  (pre_anchorNotCaptured c ca) \<longrightarrow> post_anchorNotCaptured c ca (anchorNotCaptured c ca)"
  unfolding post_anchorNotCaptured_def pre_anchorNotCaptured_def anchorNotCaputred_def
  using cord.select_convs(1) cord_ext_def inv_VDMNat1_def inv_cord_def by fastforce
    
    
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
      \<and> (ycord cord1) \<le> (ycord cord2)"   

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
      \<and> testNormalisedMove (c1 m) (c2 m) \<and> ((c1 m) \<noteq> undefined \<and> (c2 m) \<noteq> undefined) "
    
lemma normalisedMove: "(xcord (c1 m)) \<le> (xcord (c2 m)) \<or> (ycord (c1 m)) \<le> (ycord (c2 m))"
  oops
(* Discovered that I must stop moves from being negitives *)
    
lemma moveSatisfiability: "\<exists> m . inv_move m = True"
  apply simp_all
  unfolding inv_SetElems_def inv_cord_def inv_move_def testNormalisedMove_def
  apply (simp)
  nitpick
  oops
    
(*==============================================================*)
subsection{*NormaliseMove*}
 
definition
  normaliseMove :: "cord \<Rightarrow> cord \<Rightarrow> move"
  where
    "normaliseMove cord1 cord2 \<equiv> if testNormalisedMove cord1 cord2 then
      \<lparr>c1 = cord1, c2 = cord2\<rparr>
     else
      \<lparr>c1 = cord2, c2 = cord1\<rparr>"
    
definition
  pre_normaliseMove :: "cord \<Rightarrow> cord \<Rightarrow> \<bool>"
  where
    "pre_normaliseMove cord1 cord2 \<equiv> inv_cord cord1 \<and> inv_cord cord2"

definition
  post_normaliseMove :: "move \<Rightarrow> \<bool>"
  where
    "post_normaliseMove m \<equiv> (inv_move m) \<and> (testNormalisedMove (c1 m) (c2 m))"
    
lemma allMovesNormalised: "\<forall> (m::move) . inv_move m \<and> inv_cord (c1 m) \<and> inv_cord (c2 m)
  \<and> inv_VDMNat1 (xcord (c1 m)) \<and> inv_VDMNat1 (ycord (c1 m)) \<and> inv_VDMNat1 (xcord (c2 m)) 
  \<and> inv_VDMNat (ycord (c2 m))"
  oops
  
    
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
    
lemma allPlayersMustBeP1OrP2: "\<forall> (p::player) . p = P1 \<or> p = P2"
  using player.exhaust by blast
    
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
    
lemma stateSatisfiability: "\<exists> s . inv_state s"
  unfolding inv_state_def inv_SetElems_def inv_move_def inv_Map_def inv_cord_def inv_player_def
  oops
    
lemma existsAValidStateThatCanBeCreated: "\<exists> (p::move VDMSet) (t::player) (bt::\<bool>) 
  (ca::capturedPoints) . inv_state (init_state p t bt ca)"
  unfolding init_state_def inv_state_def allPlayersMustBeP1OrP2 cordSatisfiability
    by (smt dom_empty empty_iff inv_Map_def inv_SetElems_def inv_player_def player.exhaust state.select_convs(1) state.select_convs(4))

(*==============================================================*)
subsection{*getPlayerScore*}
  
(* definition
  getPlayerScore :: "player \<Rightarrow> (cord \<rightharpoonup> player) \<Rightarrow> VDMNat"
  where
    "getPlayerScore selectedPlayer ca \<equiv> vdm_card dom (ca ran_restr selectedPlayer)"
    
    
definition
  pre_getPlayerScore :: "player \<Rightarrow> (cord \<rightharpoonup> player) \<Rightarrow> \<bool>"
  where
    "pre_getPlayerScore selectedPlayer ca \<equiv> inv_player selectedPlayer \<and> inv_Map inv_cord inv_player ca"
    
definition
  post_getPlayerScore :: "player \<Rightarrow> (cord \<rightharpoonup> player) \<Rightarrow> VDMNat \<Rightarrow> \<bool>"
  where
    "post_getPlayerScore selectedPlayer ca RESULT \<equiv> RESULT \<ge> 0 \<and> inv_VDMNat RESULT" *)


    
(*==============================================================*)
subsection{*createMap*}
  
definition
  createMap :: "cord \<Rightarrow> player \<Rightarrow> (cord \<rightharpoonup> player)"
  where
    "createMap c passedPlayer \<equiv> [c \<mapsto> passedPlayer]"
    
(*==============================================================*)
subsection{*captureAnchor*}

definition
  captureAnchor :: "move \<Rightarrow> state \<Rightarrow> state"
  where
    "captureAnchor m currentState \<equiv> \<lparr>play = (play currentState),
      turn = (turn currentState),
      bonusTurn = True,
      capturedAnchors = ((capturedAnchors currentState) \<union>m [(c1 m) \<mapsto>  (turn currentState )]) \<rparr>"

definition
  pre_captureAnchor :: "move  \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_captureAnchor m  currentState \<equiv> inv_move m \<and> inv_player (turn currentState) \<and>
      testForBoxCompletion m (play currentState) \<and> (c1 m) \<notin> dom (capturedAnchors currentState) "
    
definition
  post_captureAnchor :: "move \<Rightarrow> state \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_captureAnchor m  currentState RESULT \<equiv> inv_state RESULT"
    
    
lemma possibleToCaptureAnAnchor: "\<exists> (m::move) (s::state) .
  pre_captureAnchor m s \<longrightarrow> post_captureAnchor m s (captureAnchor m s)"
  nitpick
  oops
    
lemma possibleToCaptureAnAnchor: "\<exists> (m::move) (s::state) .
  pre_captureAnchor m s \<longrightarrow> post_captureAnchor m s (captureAnchor m s)"
  unfolding existsAValidStateThatCanBeCreated 
    by (meson inv_move_def move.select_convs(1) pre_captureAnchor_def)
    
(*==============================================================*)
subsection{*doubleCaptureAnchor*}
  
definition
  doubleCaptureAnchor :: "move \<Rightarrow> move \<Rightarrow> state \<Rightarrow> state"
  where
    "doubleCaptureAnchor m1 m2 currentState \<equiv> \<lparr>play = (play currentState),
      turn = (turn currentState),
      bonusTurn = True,
      capturedAnchors = ((capturedAnchors currentState) \<union>m 
        [(c1 m1) \<mapsto> (turn currentState ),(c1 m2) \<mapsto> (turn currentState)]) \<rparr>"

definition
  pre_doubleCaptureAnchor :: "move \<Rightarrow> move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_doubleCaptureAnchor m1 m2  currentState \<equiv> inv_move m1 \<and> inv_player (turn currentState) \<and>
      testForBoxCompletion m1 (play currentState) \<and> (c1 m1) \<notin> dom (capturedAnchors currentState) \<and>
      testForBoxCompletion m2 (play currentState) \<and> inv_move m2 \<and> 
        (c1 m2) \<notin> dom (capturedAnchors currentState) "
    
definition
  post_doubleCaptureAnchor :: " state \<Rightarrow> \<bool>"
  where
    "post_doubleCaptureAnchor RESULT \<equiv> inv_state RESULT"
    
    
lemma possibleToCaptureTwoAnchors: "\<exists> (m1::move) (m2::move) (s::state) .
  pre_doubleCaptureAnchor m1 m2 s \<longrightarrow> 
    post_doubleCaptureAnchor (doubleCaptureAnchor m1 m2 s)"
  unfolding existsAValidStateThatCanBeCreated
    by (meson inv_move_def move.select_convs(2) pre_doubleCaptureAnchor_def)
    
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
  pre_saveTheMove :: "move \<Rightarrow> state \<Rightarrow> \<bool> "
  where
    "pre_saveTheMove m currentState \<equiv> inv_move m \<and> inv_state currentState "
    
definition
  post_saveTheMove :: "move \<Rightarrow> cord  \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_saveTheMove m RESULT RESULT_STATE \<equiv> inv_state RESULT_STATE 
        \<and> m \<in> (play RESULT_STATE) \<and> inv_cord RESULT"
    
lemma possibleToSaveAMove: "\<exists> (m::move) (s::state) .
  pre_saveTheMove m s \<longrightarrow> post_saveTheMove m (snd (saveTheMove m s)) (fst(saveTheMove m s))"
  unfolding existsAValidStateThatCanBeCreated
    by (meson inv_move_def move.select_convs(1) pre_saveTheMove_def)

(*==============================================================*)
subsection{*swapTurn*}
  
  
definition
  swapTurn :: "state \<Rightarrow> state"
  where
    "swapTurn gameState \<equiv> if \<not>(bonusTurn gameState) then
      if (turn gameState) = P1 then
        \<lparr>play = (play gameState),
         turn = P2,
         bonusTurn = False,
         capturedAnchors = (capturedAnchors gameState) \<rparr>
      else
        \<lparr>play = (play gameState),
         turn = P1,
         bonusTurn = False,
         capturedAnchors = (capturedAnchors gameState) \<rparr>
    else
      \<lparr>play = (play gameState),
       turn = (turn gameState),
       bonusTurn = False,
       capturedAnchors = (capturedAnchors gameState) \<rparr>"
    
definition
  pre_swapTurn :: "state \<Rightarrow> \<bool>"
  where
    "pre_swapTurn gameState \<equiv> inv_state gameState"

definition
  post_swapTurn :: "state \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_swapTurn preGameState postGameState \<equiv> (if (bonusTurn preGameState) then 
      (turn preGameState) = (turn postGameState)
    else
      (turn preGameState) \<noteq> (turn postGameState)) \<and> inv_state postGameState \<and> \<not>(bonusTurn postGameState)"
    
lemma possibleToSwapTurns: "\<exists> (s::state) .
  pre_swapTurn s \<longrightarrow> post_swapTurn s (swapTurn s)"
  unfolding existsAValidStateThatCanBeCreated
    by (metis UNIV_I inv_SetElems_def inv_move_def inv_state_def move.select_convs(1) pre_swapTurn_def state.select_convs(1))

(*==============================================================*)
subsection{*boxCapture*}
 
definition
  boxCapture :: "state \<Rightarrow> move \<Rightarrow> (\<bool> \<times> state)"
  where
    "boxCapture currentState m \<equiv> (False,currentState)"
    
definition
  pre_boxCapture :: "state \<Rightarrow> move \<Rightarrow> \<bool>"
  where
    "pre_boxCapture currentState m \<equiv> inv_state currentState \<and> inv_move m"
    
definition
  post_boxCapture :: "state \<Rightarrow> move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_boxCapture currentState m resultState \<equiv> inv_state resultState"
    
lemma possibleBoxCapture: "\<exists> (s::state) (m::move) .
  pre_boxCapture s m \<longrightarrow> post_boxCapture s m (snd(boxCapture s m))"
  unfolding existsAValidStateThatCanBeCreated
  using post_boxCapture_def pre_boxCapture_def by blast
    
(*==============================================================*)
subsection{*doubleBoxOccured*}
  
definition
  doubleBoxOccured :: "state \<Rightarrow> move \<Rightarrow> \<bool>"
  where
    "doubleBoxOccured gameState m \<equiv> 
      (xcord (testForDoubleBoxCompletion (c1 m) (play gameState) (dom(capturedAnchors gameState)))
        \<noteq> (xcord (c1 m))) 
        \<and>
      (ycord (testForDoubleBoxCompletion (c1 m) (play gameState) (dom(capturedAnchors gameState)))
        \<noteq> (ycord (c1 m)))"
    
definition
  pre_doubleBoxOccured :: "state \<Rightarrow> move \<Rightarrow> \<bool>"
  where
    "pre_doubleBoxOccured s m \<equiv> inv_state s \<and> inv_move m"
    
definition
  post_doubleBoxOccured :: "state \<Rightarrow> move \<Rightarrow> \<bool> \<Rightarrow> \<bool>"
  where
    "post_doubleBoxOccured s m RESULT \<equiv> True"
       
(*==============================================================*)
subsection{*makeAMove*}

(* I'm really sorry about this, it breaks the make a move from the VDM model
   into a more functional programming style. The first case that can occur is 
   if the player has two boxes at once. In this case a double capture anchor
   function will be called. The second instance is if the user creates a box
   on the current anchor. The third circumstance is if the user has created a box
   on the neighbouring anchor. Finally we have if the player hasn't created  any boxes
   at all. All of the capture anchor functions will set bonusTurn flag to true 
   and add the anchor to the set. This then returns a state which is passed
   straight away to the swapTurn function. This will check the bonusTurn flag to
   see if needs to swap the player *)
  
definition
  makeAMove :: "move \<Rightarrow> state \<Rightarrow> state"
  where
    "makeAMove m gameState \<equiv> 
      if (testForBoxCompletion m (play gameState) \<and> doubleBoxOccured gameState m) then
        swapTurn (doubleCaptureAnchor m \<lparr> c1 = testForDoubleBoxCompletion (c1 m) (play gameState)
          (dom (capturedAnchors gameState)), c2 = (c1 m) \<rparr> gameState)
      else if(testForBoxCompletion m (play gameState)) then
        swapTurn (captureAnchor m gameState)
      else if(doubleBoxOccured gameState m) then
        swapTurn (captureAnchor \<lparr> c1 = testForDoubleBoxCompletion (c1 m) (play gameState) 
            (dom (capturedAnchors gameState)),c2 = (c1 m) \<rparr> gameState)
      else
        swapTurn gameState "
    
definition
  pre_makeAMove :: "move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "pre_makeAMove m currentState \<equiv> inv_move m \<and> m \<notin> (play currentState) \<and> testValidMove (c1 m) (c2 m)
      \<and> inv_state currentState"
    
definition
  post_makeAMove :: "move \<Rightarrow> state \<Rightarrow> \<bool>"
  where
    "post_makeAMove m RESULT \<equiv> inv_state RESULT"
    
lemma pre_makeAMoveSatisfiability: "\<exists> m s . pre_makeAMove m s"
  unfolding pre_makeAMove_def
    oops
    
lemma makeAMoveSatisfiablity: "\<exists> m s . pre_makeAMove m s \<longrightarrow> (post_makeAMove m (makeAMove m s)) "
  unfolding pre_makeAMove_def post_makeAMove_def makeAMove_def
  oops
   
theorem makeAMoveSatisfiability1: "\<exists> (m::move) (s::state) .
  pre_makeAMove m s \<longrightarrow> post_makeAMove m (makeAMove m s)"
  unfolding existsAValidStateThatCanBeCreated possibleBoxCapture
    possibleToSwapTurns possibleToSaveAMove
    using post_makeAMove_def pre_makeAMove_def by blast
    
(*==============================================================*)
subsection{*SquaresLeft*}
  
definition (* ca = captured Anchors *)
  SquaresLeft :: "cord VDMSet \<Rightarrow> VDMNat"
  where
    "SquaresLeft ca \<equiv> if (vdm_card ca = undefined) then
      0
      else
      (GRID_WIDTH - (1::VDMNat)) * (GRID_HEIGHT - (1::VDMNat)) - (vdm_card ca) "

definition
  pre_SquaresLeft :: "cord VDMSet \<Rightarrow> \<bool>"
  where
    "pre_SquaresLeft ca \<equiv> inv_SetElems inv_cord ca"
    
definition
  post_SquaresLeft :: "cord VDMSet \<Rightarrow> VDMNat \<Rightarrow> \<bool>"
  where
    "post_SquaresLeft ca RESULT \<equiv> True"
    
(*==============================================================*)