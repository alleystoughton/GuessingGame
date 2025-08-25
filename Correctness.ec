(* Correctness of the Real Protocol as Applied to the Honest Party
   and a Clone of the Honest Party

   For correctness, we let both parties be Honest, and show that no
   matter which roles we assign them (chooser/guesser) and whatever
   choices/guesses we tell them to use (using from_adv), there is a
   sequence of calls to the queue and deliver procedures such that
   when to_adv is called for the chooser/guesser, the results
   correctly say who won/lost. *)

prover ["Z3" "Alt-Ergo"].  (* both must succeed for all smt goals *)

require import AllCore List FMap FSet.

(* physical and party-indexed virtual memories *)

require import Memory.

(* guessing game protocols, adversaries, experiments, real protocol
   and honest party *)

require import Protocol.

(* we have two instances of the honest party:

   Honest.Honest      : PARTY
   OtherHonest.Honest : PARTY
*)

clone Honest as OtherHonest
proof *.

(********************************* Correctness ********************************)

(* in our correctness theorem, we quantify over a module with
   type: *)

module type INPUTS = {
  proc chooser() : party  (* decide which party will be the chooser *)

  proc choice_and_guess() : bool  (* the chooser's choice *)
                          * bool  (* the guesser's guess *)
}.

(* turn an INPUTS module into an adversary *)

module (CorrectAdv (Inputs : INPUTS) : ADV) (Proto : PROTOCOL) = {
  var chooser : party

  proc chooser() : party = {
    chooser <@ Inputs.chooser();
    return chooser;
  }

  proc distinguish() : bool = {
    var choice, guess : bool;
    var chooser_msg, guesser_msg : msg option;
    var guesser : party <- other chooser;
    (* get the choice and guess from Inputs *)
    (choice, guess) <@ Inputs.choice_and_guess();
    (* we'll ignore the returned booleans, which given
       how Honest is defined, will be true *)
    Proto.from_adv(chooser, Choice choice);
    Proto.from_adv(guesser, Guess guess);
    (* chooser sends locked cell to guesser *)
    Proto.queue(chooser);
    Proto.deliver(guesser);
    (* guesser sends guess to chooser *)
    Proto.queue(guesser);
    Proto.deliver(chooser);
    (* chooser sends key that will unlock cell to guesser *)
    Proto.queue(chooser);
    Proto.deliver(guesser);
    (* both chooser and guesser now will be ready to send
       results (whether they won) to adversary *)
    chooser_msg <@ Proto.to_adv(chooser);
    guesser_msg <@ Proto.to_adv(guesser);
    return
      (chooser_msg <> None /\ guesser_msg <> None /\
       let chooser_res_opt = get_as_Result (oget chooser_msg) in
       let guesser_res_opt = get_as_Result (oget guesser_msg) in
       chooser_res_opt <> None /\ guesser_res_opt <> None /\
       let chooser_res = oget chooser_res_opt in
       let guesser_res = oget guesser_res_opt in
       if choice = guess
       then ! chooser_res /\ guesser_res
       else chooser_res   /\ ! guesser_res);
  }
}.

(* we will prove that the main procedure of this experiment always
   returns true, assuming the procedures of Inputs terminate *)

module CorrectExper (Inputs : INPUTS) =
  Exper(RealProtocol(Honest.Honest, OtherHonest.Honest), CorrectAdv(Inputs)).

section.

declare module
  Inputs <:
  INPUTS{-RealProtocol, -Honest.Honest, -OtherHonest.Honest, -CorrectAdv}.

declare axiom chooser_ll          : islossless Inputs.chooser.
declare axiom choice_and_guess_ll : islossless Inputs.choice_and_guess.

local lemma Exper_distinguish :
  hoare
  [Exper(RealProtocol(Honest.Honest, OtherHonest.Honest),
         CorrectAdv(Inputs)).A.distinguish :
   RealProtocol.to_malicious_queue = [] /\
   RealProtocol.to_honest_queue = [] /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest then Honest.HPS_Chooser_WaitFromAdvChoice
    else Honest.HPS_Guesser_WaitFromAdvGuess) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitFromAdvGuess
    else OtherHonest.HPS_Chooser_WaitFromAdvChoice) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 0 /\ Memory.next_phys_addr = 0 /\
   Memory.phys_map = empty /\
   Memory.next_virt_addr = empty.[Honest <- 0].[Malicious <- 0] /\
   Memory.virt_map       = empty.[Honest <- empty].[Malicious <- empty] ==>
   res].
proof.
proc.
sp.
seq 1 : #pre.
call (_ : true); first auto.
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   RealProtocol.to_malicious_queue = [] /\
   RealProtocol.to_honest_queue = [] /\
  (Honest.Honest.state =
   if CorrectAdv.chooser = Honest
   then Honest.HPS_Chooser_WaitToOtherCellAddr choice 0 1
   else Honest.HPS_Guesser_WaitFromAdvGuess) /\
  (OtherHonest.Honest.state =
   if CorrectAdv.chooser = Honest
   then OtherHonest.HPS_Guesser_WaitFromAdvGuess
   else OtherHonest.HPS_Chooser_WaitToOtherCellAddr choice 0 1) /\
  gm_invar (glob Memory) /\
  Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
  Memory.phys_map =
    empty
      .[0 <- Key 0]
      .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
  (if CorrectAdv.chooser = Honest
   then (oget Memory.next_virt_addr.[Honest] = 2 /\
         oget Memory.virt_map.[Honest] = (empty.[0 <- 0]).[1 <- 1] /\
         oget Memory.next_virt_addr.[Malicious] = 0 /\
         oget Memory.virt_map.[Malicious] = empty)
   else (oget Memory.next_virt_addr.[Malicious] = 2 /\
         oget Memory.virt_map.[Malicious] = (empty.[0 <- 0]).[1 <- 1] /\
         oget Memory.next_virt_addr.[Honest] = 0 /\
         oget Memory.virt_map.[Honest] = empty))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).from_adv.
sp.
match.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.from_adv.
sp.
match HPS_Chooser_WaitFromAdvChoice 1; first auto.
match Choice 1; first auto; smt().
wp.
seq 1 :
  (choice0 = choice /\ CorrectAdv.chooser = Honest /\
   Honest.Honest.state = Honest.HPS_Chooser_WaitFromAdvChoice /\
   OtherHonest.Honest.state = OtherHonest.HPS_Guesser_WaitFromAdvGuess /\
   guesser = other CorrectAdv.chooser /\
   RealProtocol.to_malicious_queue = [] /\
   RealProtocol.to_honest_queue = [] /\
   key_addr = 0 /\ gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 1 /\
   Memory.phys_map = empty.[0 <- Key 0] /\
   oget Memory.next_virt_addr.[Honest] = 1 /\
   oget Memory.virt_map.[Honest] = empty.[0 <- 0] /\
   oget Memory.next_virt_addr.[Malicious] = 0 /\
   oget Memory.virt_map.[Malicious] = empty).
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_create_key gm).
auto; progress [-delta]; smt(get_setE).
exlim (glob Memory) => gm'.
exlim choice0 => ch.
call (HonestMemory.party_memory_create_cell gm' 0 ch).
auto; smt(mem_set get_set_sameE).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.from_adv.
sp.
match HPS_Chooser_WaitFromAdvChoice 1; first auto.
match Choice 1; first auto; smt().
wp.
seq 1 :
  (choice0 = choice /\ CorrectAdv.chooser = Malicious /\
   Honest.Honest.state = Honest.HPS_Guesser_WaitFromAdvGuess /\
   OtherHonest.Honest.state = OtherHonest.HPS_Chooser_WaitFromAdvChoice /\
   guesser = other CorrectAdv.chooser /\
   RealProtocol.to_malicious_queue = [] /\
   RealProtocol.to_honest_queue = [] /\
   key_addr = 0 /\ gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 1 /\
   Memory.phys_map = empty.[0 <- Key 0] /\
   oget Memory.next_virt_addr.[Malicious] = 1 /\
   oget Memory.virt_map.[Malicious] = empty.[0 <- 0] /\
   oget Memory.next_virt_addr.[Honest] = 0 /\
   oget Memory.virt_map.[Honest] = empty).
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_create_key gm); first auto; smt(get_setE).
exlim (glob Memory) => gm'.
exlim choice0 => ch.
call (MaliciousMemory.party_memory_create_cell gm' 0 ch).
auto; smt(mem_set get_set_sameE).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.from_adv.
sp.
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   RealProtocol.to_malicious_queue = [] /\
   RealProtocol.to_honest_queue = [] /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitToOtherCellAddr choice 0 1
    else Honest.HPS_Guesser_WaitFromOtherCellAddr guess) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitFromOtherCellAddr guess
    else OtherHonest.HPS_Chooser_WaitToOtherCellAddr choice 0 1) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 0 /\
          oget Memory.virt_map.[Malicious] = empty)
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 0 /\
          oget Memory.virt_map.[Honest] = empty))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).from_adv.
sp.
match.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.from_adv.
sp.
match HPS_Guesser_WaitFromAdvGuess 1; first auto; smt().
match Guess 1; first auto; smt().
auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.from_adv.
sp.
match HPS_Guesser_WaitFromAdvGuess 1; first auto; smt().
match Guess 1; first auto; smt().
auto; smt().
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [CellAddr 0] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [CellAddr 0])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitFromOtherGuess choice 0
    else Honest.HPS_Guesser_WaitFromOtherCellAddr guess) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitFromOtherCellAddr guess
    else OtherHonest.HPS_Chooser_WaitFromOtherGuess choice 0) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 1 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 1 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).queue.
sp.
match.
wp.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.to_other.
sp.
match HPS_Chooser_WaitToOtherCellAddr 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_trans_virt_addr gm 1).
auto; smt(mem_set get_setE).
wp.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.to_other.
sp.
match HPS_Chooser_WaitToOtherCellAddr 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_trans_virt_addr gm 1).
auto; smt(mem_set get_setE).
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitFromOtherGuess choice 0
    else Honest.HPS_Guesser_WaitToOtherGuess guess 0) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitToOtherGuess guess 0
    else OtherHonest.HPS_Chooser_WaitFromOtherGuess choice 0) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 1 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 1 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).deliver.
sp.
match.
match (::) 1; first auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.from_other.
sp.
match HPS_Guesser_WaitFromOtherCellAddr 1; first auto; smt().
sp.
match CellAddr 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_is_cell_true gm).
auto; smt(mem_set get_setE).
match (::) 1; first auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.from_other.
sp.
match HPS_Guesser_WaitFromOtherCellAddr 1; first auto; smt().
sp.
match CellAddr 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_is_cell_true gm).
auto; smt(mem_set get_setE).
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [Guess guess])
    else (RealProtocol.to_malicious_queue = [Guess guess] /\
          RealProtocol.to_honest_queue = [])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitFromOtherGuess choice 0
    else Honest.HPS_Guesser_WaitFromOtherKeyAddr guess 0) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitFromOtherKeyAddr guess 0
    else OtherHonest.HPS_Chooser_WaitFromOtherGuess choice 0) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 1 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 1 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).queue.
sp.
match.
wp.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.to_other.
sp.
match HPS_Guesser_WaitToOtherGuess 1; first auto; smt().
auto; smt().
wp.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.to_other.
sp.
match HPS_Guesser_WaitToOtherGuess 1; first auto; smt().
auto; smt().
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitToOtherKeyAddr (guess <> choice) 0
    else Honest.HPS_Guesser_WaitFromOtherKeyAddr guess 0) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitFromOtherKeyAddr guess 0
    else OtherHonest.HPS_Chooser_WaitToOtherKeyAddr (guess <> choice) 0) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 1 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 1 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).deliver.
sp.
match.
match (::) 1; first auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.from_other.
sp.
match HPS_Chooser_WaitFromOtherGuess 1; first auto; smt().
sp.
match Guess 1; first auto; smt().
auto; smt().
match (::) 1; first auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.from_other.
sp.
match HPS_Chooser_WaitFromOtherGuess 1; first auto; smt().
sp.
match Guess 1; first auto; smt().
auto; smt().
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [KeyAddr 1] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [KeyAddr 1])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitToAdvResult (guess <> choice)
    else Honest.HPS_Guesser_WaitFromOtherKeyAddr guess 0) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitFromOtherKeyAddr guess 0
    else OtherHonest.HPS_Chooser_WaitToAdvResult (guess <> choice)) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 2 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1].[1 <- 0])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1].[1 <- 0]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).queue.
sp.
match.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.to_other.
sp.
match HPS_Chooser_WaitToOtherKeyAddr 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_trans_virt_addr gm 0).
auto; smt(mem_set get_setE).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.to_other.
sp.
match HPS_Chooser_WaitToOtherKeyAddr 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_trans_virt_addr gm 0).
auto; smt(mem_set get_setE).
seq 1 :
  (guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_WaitToAdvResult (guess <> choice)
    else Honest.HPS_Guesser_WaitToAdvResult (guess = choice)) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitToAdvResult (guess = choice)
    else OtherHonest.HPS_Chooser_WaitToAdvResult (guess <> choice)) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 3 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}]
       .[2 <- Cell {|key = 0; cont = choice; locked = false|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 3 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1].[1 <- 0].[2 <- 2])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 3 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1].[1 <- 0].[2 <- 2]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).deliver.
sp.
match.
match (::) 1; first auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.from_other.
sp.
match HPS_Guesser_WaitFromOtherKeyAddr 1; first auto; smt().
sp.
match KeyAddr 1; first auto; smt().
elim* => state' r'.
seq 1 :
  (r = true /\  guess = guess0 /\ cell_addr = 0 /\ key_addr = 1 /\
   msgs = [] /\ party = Honest /\ party = guesser /\
   guesser = other CorrectAdv.chooser /\
   RealProtocol.to_honest_queue = [KeyAddr 1] /\
   RealProtocol.to_malicious_queue = [] /\
   OtherHonest.Honest.state =
   OtherHonest.HPS_Chooser_WaitToAdvResult (guess <> choice) /\
   gm_invar (glob Memory) /\
   unlocked_cell_addr_opt = Some 2 /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 3 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}]
       .[2 <- Cell {|key = 0; cont = choice; locked = false|}] /\
    (oget Memory.next_virt_addr.[Malicious] = 2 /\
     oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
     oget Memory.next_virt_addr.[Honest] = 3 /\
     oget Memory.virt_map.[Honest] = empty.[0 <- 1].[1 <- 0].[2 <- 2])).
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_unlock_cell gm 0 1).
auto; smt(mem_set get_setE oget_some).
match Some 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
exlim unlocked_cell_addr => cell_addr'.
call (HonestMemory.party_memory_contents_cell gm cell_addr').
auto; smt(mem_set get_setE).
match (::) 1; first auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.from_other.
sp.
match HPS_Guesser_WaitFromOtherKeyAddr 1; first auto; smt().
sp.
match KeyAddr 1; first auto; smt().
elim* => state' r'.
seq 1 :
  (r = true /\  guess = guess0 /\ cell_addr = 0 /\ key_addr = 1 /\
   msgs = [] /\ party = Malicious /\ party = guesser /\
   guesser = other CorrectAdv.chooser /\
   RealProtocol.to_malicious_queue = [KeyAddr 1] /\
   RealProtocol.to_honest_queue = [] /\
   Honest.Honest.state =
   Honest.HPS_Chooser_WaitToAdvResult (guess <> choice) /\
   gm_invar (glob Memory) /\
   unlocked_cell_addr_opt = Some 2 /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 3 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}]
       .[2 <- Cell {|key = 0; cont = choice; locked = false|}] /\
    (oget Memory.next_virt_addr.[Honest] = 2 /\
     oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
     oget Memory.next_virt_addr.[Malicious] = 3 /\
     oget Memory.virt_map.[Malicious] = empty.[0 <- 1].[1 <- 0].[2 <- 2])).
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_unlock_cell gm 0 1).
auto; progress; smt(mem_set get_setE oget_some).
match Some 1; first auto; smt().
wp.
exlim (glob Memory) => gm.
exlim unlocked_cell_addr => cell_addr'.
call (MaliciousMemory.party_memory_contents_cell gm cell_addr').
auto; smt(mem_set get_setE oget_some).
seq 1 :
  (chooser_msg = Some (Result (guess <> choice)) /\
   guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_Final
    else Honest.HPS_Guesser_WaitToAdvResult (guess = choice)) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_WaitToAdvResult (guess = choice)
    else OtherHonest.HPS_Chooser_Final) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 3 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}]
       .[2 <- Cell {|key = 0; cont = choice; locked = false|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 3 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1].[1 <- 0].[2 <- 2])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 3 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1].[1 <- 0].[2 <- 2]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).to_adv.
sp.
match.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.to_adv.
sp.
match HPS_Chooser_WaitToAdvResult 1; first auto; smt().
auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.to_adv.
sp.
match HPS_Chooser_WaitToAdvResult 1; first auto; smt().
auto; smt().
seq 1 :
  (chooser_msg = Some (Result (guess <> choice)) /\
   guesser_msg = Some (Result (guess = choice)) /\
   guesser = other CorrectAdv.chooser /\
   (if CorrectAdv.chooser = Honest
    then (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])
    else (RealProtocol.to_malicious_queue = [] /\
          RealProtocol.to_honest_queue = [])) /\
   (Honest.Honest.state =
    if CorrectAdv.chooser = Honest
    then Honest.HPS_Chooser_Final
    else Honest.HPS_Guesser_Final) /\
   (OtherHonest.Honest.state =
    if CorrectAdv.chooser = Honest
    then OtherHonest.HPS_Guesser_Final
    else OtherHonest.HPS_Chooser_Final) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 1 /\ Memory.next_phys_addr = 3 /\
   Memory.phys_map =
     empty
       .[0 <- Key 0]
       .[1 <- Cell {|key = 0; cont = choice; locked = true|}]
       .[2 <- Cell {|key = 0; cont = choice; locked = false|}] /\
   (if CorrectAdv.chooser = Honest
    then (oget Memory.next_virt_addr.[Honest] = 2 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Malicious] = 3 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 1].[1 <- 0].[2 <- 2])
    else (oget Memory.next_virt_addr.[Malicious] = 2 /\
          oget Memory.virt_map.[Malicious] = empty.[0 <- 0].[1 <- 1] /\
          oget Memory.next_virt_addr.[Honest] = 3 /\
          oget Memory.virt_map.[Honest] = empty.[0 <- 1].[1 <- 0].[2 <- 2]))).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).to_adv.
sp.
match.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.to_adv.
sp.
match HPS_Guesser_WaitToAdvResult 1; first auto; smt().
auto; smt().
inline RealProtocol(Honest.Honest, OtherHonest.Honest).M.to_adv.
sp.
match HPS_Guesser_WaitToAdvResult 1; first auto; smt().
auto; smt().
auto; smt().
qed.

lemma CorrectExpr_main_ll : islossless CorrectExper(Inputs).main.
proof.
islossless; do ? (match; islossless).
apply choice_and_guess_ll.
apply chooser_ll.
qed.

lemma correct &m :
  Pr[CorrectExper(Inputs).main() @ &m : res] = 1%r.
proof.
byphoare => //.
conseq (_ : true ==> true) (_ : true ==> res) => //; last first.
apply CorrectExpr_main_ll.
proc.
seq 1 : (chooser = CorrectAdv.chooser).
inline*; wp.
call (_ : true).
auto.
seq 1 :
  (chooser = CorrectAdv.chooser /\
   RealProtocol.to_malicious_queue = [] /\
   RealProtocol.to_honest_queue = [] /\
   (Honest.Honest.state =
      if chooser = Honest
      then Honest.HPS_Chooser_WaitFromAdvChoice
      else Honest.HPS_Guesser_WaitFromAdvGuess) /\
   (OtherHonest.Honest.state =
      if chooser = Honest
      then OtherHonest.HPS_Guesser_WaitFromAdvGuess
      else OtherHonest.HPS_Chooser_WaitFromAdvChoice) /\
   gm_invar (glob Memory) /\
   Memory.next_key = 0 /\ Memory.next_phys_addr = 0 /\
   Memory.phys_map = empty /\
   Memory.next_virt_addr = empty.[Honest <- 0].[Malicious <- 0] /\
   Memory.virt_map       = empty.[Honest <- empty].[Malicious <- empty]).
inline RealProtocol(Honest.Honest, OtherHonest.Honest).init.
call memory_init.
sp.
match.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.init
       RealProtocol(Honest.Honest, OtherHonest.Honest).M.init.
auto.
inline RealProtocol(Honest.Honest, OtherHonest.Honest).H.init
       RealProtocol(Honest.Honest, OtherHonest.Honest).M.init.
auto.
call Exper_distinguish.
auto.
qed.

end section.

lemma correctness
      (Inputs <:
       INPUTS{-RealProtocol, -Honest.Honest, -OtherHonest.Honest, -CorrectAdv})
      &m :
  islossless Inputs.chooser =>
  islossless Inputs.choice_and_guess =>
  Pr[CorrectExper(Inputs).main() @ &m : res] = 1%r.
proof.
move => chooser_ll choice_and_guess_ll.
apply (correct Inputs chooser_ll choice_and_guess_ll).
qed.
