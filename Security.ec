(* Definition and Proof of Security of Honest Party Against
   Malicious Party/Adversary

   Security is defined via an ideal protocol, parameterized by
   a simulator (whose definition is part of the proof of security) *)

prover ["Z3" "Alt-Ergo"].  (* both must succeed for all smt goals *)

require import AllCore List FMap FSet.

(* physical and party-indexed virtual memories *)

require import Memory.

(* guessing game protocols, adversaries, experiments, real protocol
   and honest party *)

require import Protocol.

(********************************** Security **********************************)

(* outputs from the simulator's honest_output procedure *)

type sim_honest_output = [
  | SHO_Nothing          (* nothing to report *)
  | SHO_Choice  of bool  (* the malicious party's choice *)
  | SHO_Guess   of bool  (* the malicious party's guess *)
  | SHO_OK               (* simulator terminated normally *)
  | SHO_Error            (* simulator terminated with error - caused
                            by simulation of malicious party *)
].

(* module interface of the simulator

   inside the simulator we define, there is a modified version of
   the real protocol

   it uses the actual malicious party

   but the honest party is replaced by one with a somewhat different
   interface, and with greater powers over the memory *)

module type SIMULATOR = {
  (* initialize the simulator, telling it which party is the chooser *)

  proc init(chooser : party) : unit

  (* start the honest party *)

  proc honest_start() : unit

  (* tell the honest party its choice (only done after the malicious
     party's guess is known, and when the result (won/lost) is fixed)
     *)

  proc honest_choice(choice : bool) : unit

  (* tell the honest party its guess (only done after the malicious
     party's choice is known, and when the result (won/lost) is fixed)
     *)

  proc honest_guess(guess : bool) : unit

  (* these procedures also produce an output, which can be
     SHO_Nothing *)

  proc honest_queue()   : sim_honest_output
  proc honest_deliver() : sim_honest_output

  (* the following procedures are analogous to those of the real
     protocol *)

  proc malicious_from_adv(msg : msg) : bool
  proc malicious_to_adv()            : msg option
  proc malicious_queue()             : unit
  proc malicious_deliver()           : unit
}.

(* state of the ideal protocol *)

type ideal_protocol_state = [
  (* chooser *)
  | IPS_Chooser_WaitFromAdvChoice
  | IPS_Chooser_WaitSimGuess      of bool  (* choice *)
  | IPS_Chooser_WaitSimOK         of bool  (* result *)
  | IPS_Chooser_WaitToAdvResult   of bool  (* result *)
  | IPS_Chooser_WaitToAdvError
  | IPS_Chooser_Final
  (* guesser *)
  | IPS_Guesser_WaitFromAdvGuess
  | IPS_Guesser_WaitSimChoice     of bool  (* guess *)
  | IPS_Guesser_WaitSimOK         of bool  (* result *)
  | IPS_Guesser_WaitToAdvResult   of bool  (* result *)
  | IPS_Guesser_WaitToAdvError
  | IPS_Guesser_Final
].

(* ideal protocol, parameterized by a simulator

   the ideal protocol itself does not use the memory, but the
   standard simulator does

   when the honest party is the chooser, the simulator only learns
   the choice after it commits to the guess, and so the choice
   cannot be exfilatrated via to_adv(Malicious, ...) before
   the guess is committed to and the honest party's outcome is
   determined

   when the honest party is the guesser, the simulator only learns
   the guess after it commits to the choice, and so the guess
   cannot be exfilatrated via to_adv(Malicious, ...) before
   the choice is committed to and the honest party's outcome is
   determined

   (of course the adversary knows both the choice and guess, so it
   could, e.g., instruct the malicious party to guess so as to win) *)

module IdealProtocol (Sim : SIMULATOR) : PROTOCOL = {
  var state : ideal_protocol_state

  proc init(chooser : party) : unit = {
    Sim.init(chooser);
    state <-
      match chooser with
      | Honest    => IPS_Chooser_WaitFromAdvChoice
      | Malicious => IPS_Guesser_WaitFromAdvGuess
      end;
  }

  proc from_adv(party : party, msg : msg) : bool = {
    var r : bool;
    match party with
    | Honest    => {
        r <- false;  (* default is reject *)
        match state with
        | IPS_Chooser_WaitFromAdvChoice => {
            match msg with
            | Result _      => { }
            | Choice choice => {
                Sim.honest_start();
                state <- IPS_Chooser_WaitSimGuess choice; r <- true;
              }
            | Guess _       => { }
            | CellAddr _    => { }
            | KeyAddr  _    => { }
            | Error         => { }
            | Int _         => { }
            end;
          }
        | IPS_Chooser_WaitSimGuess _    => { }
        | IPS_Chooser_WaitSimOK _       => { }
        | IPS_Chooser_WaitToAdvResult _ => { }
        | IPS_Chooser_WaitToAdvError    => { }
        | IPS_Chooser_Final             => { }
        | IPS_Guesser_WaitFromAdvGuess  => {
            match msg with
            | Result _     => { }
            | Choice _     => { }
            | Guess guess  => {
                Sim.honest_start();
                state <- IPS_Guesser_WaitSimChoice guess; r <- true;
              }
            | CellAddr _   => { }
            | KeyAddr  _   => { }
            | Error        => { }
            | Int _        => { }
            end;
          }
        | IPS_Guesser_WaitSimChoice _   => { }
        | IPS_Guesser_WaitSimOK _       => { }
        | IPS_Guesser_WaitToAdvResult _ => { }
        | IPS_Guesser_WaitToAdvError    => { }
        | IPS_Guesser_Final             => { }
        end;
      }
    | Malicious => {
        r <@ Sim.malicious_from_adv(msg);
      }
    end;
    return r;
  }

  proc to_adv(party : party) : msg option = {
    var r : msg option;
    match party with
    | Honest    => {
        r <- None;  (* default is no message *)
        match state with
        | IPS_Chooser_WaitFromAdvChoice      => { }
        | IPS_Chooser_WaitSimGuess _         => { }
        | IPS_Chooser_WaitSimOK _            => { }
        | IPS_Chooser_WaitToAdvResult result => {
            r <- Some (Result result); state <- IPS_Chooser_Final;
          }
        | IPS_Chooser_WaitToAdvError         => {
            r <- Some Error; state <- IPS_Chooser_Final;
          }
        | IPS_Chooser_Final                  => { }
        | IPS_Guesser_WaitFromAdvGuess       => { }
        | IPS_Guesser_WaitSimChoice _        => { }
        | IPS_Guesser_WaitSimOK _            => { }
        | IPS_Guesser_WaitToAdvResult result => {
            r <- Some (Result result); state <- IPS_Guesser_Final;
          }
        | IPS_Guesser_WaitToAdvError         => {
            r <- Some Error; state <- IPS_Guesser_Final;
          }
        | IPS_Guesser_Final                  => { }
        end;
      }
    | Malicious => {
        r <@ Sim.malicious_to_adv();
      }
    end;
    return r;
  }

  proc queue(party : party) : unit = {
    var so : sim_honest_output;
    match party with
    | Honest    => {
        so <@ Sim.honest_queue();
        match state with
        | IPS_Chooser_WaitFromAdvChoice   => { }
        | IPS_Chooser_WaitSimGuess _      => { }
        | IPS_Chooser_WaitSimOK result    => {
            match so with
            | SHO_Nothing     => { }
            | SHO_Choice _    => { }  (* should not happen *)
            | SHO_Guess _     => { }  (* should not happen *)
            | SHO_OK          => {
                state <- IPS_Chooser_WaitToAdvResult result;
              }
            | SHO_Error       => { }  (* should not happen *)
            end;
          }
        | IPS_Chooser_WaitToAdvResult _   => { }
        | IPS_Chooser_WaitToAdvError      => { }
        | IPS_Chooser_Final               => { }
        | IPS_Guesser_WaitFromAdvGuess    => { }
        | IPS_Guesser_WaitSimChoice _     => { }
        | IPS_Guesser_WaitSimOK _         => { }
        | IPS_Guesser_WaitToAdvResult _   => { }
        | IPS_Guesser_WaitToAdvError      => { }
        | IPS_Guesser_Final               => { }
        end;
      }
    | Malicious => { Sim.malicious_queue(); }
    end;
  }

  proc deliver(party : party) : unit = {
    var so : sim_honest_output;
    match party with
    | Honest    => {
        so <@ Sim.honest_deliver();
        match state with
        | IPS_Chooser_WaitFromAdvChoice   => { }
        | IPS_Chooser_WaitSimGuess choice => {
            match so with
            | SHO_Nothing     => { }
            | SHO_Choice _    => { }  (* should not happen *)
            | SHO_Guess guess => {
                Sim.honest_choice(choice);
                (* if the guessing party's guess is not equal to
                   choice, then the choosing party wins *)
                state <- IPS_Chooser_WaitSimOK (guess <> choice);
              }
            | SHO_OK          => { }  (* should not happen *)
            | SHO_Error       => {
                state <- IPS_Chooser_WaitToAdvError;
              }
            end;
          }
        | IPS_Chooser_WaitSimOK _         => { }
        | IPS_Chooser_WaitToAdvResult _   => { }
        | IPS_Chooser_WaitToAdvError      => { }
        | IPS_Chooser_Final               => { }
        | IPS_Guesser_WaitFromAdvGuess    => { }
        | IPS_Guesser_WaitSimChoice guess => {
            match so with
            | SHO_Nothing       => { }
            | SHO_Choice choice => {
                Sim.honest_guess(guess);
                (* if the guessing party's guess is equal to the
                   choosing party's choice, the guesser wins *)
                state <- IPS_Guesser_WaitSimOK (guess = choice);
              }
            | SHO_Guess _       => { }  (* should not happen *)
            | SHO_OK            => { }  (* should not happen *)
            | SHO_Error         => {
                state <- IPS_Guesser_WaitToAdvError;
              }
            end;
          }
        | IPS_Guesser_WaitSimOK result    => {
            match so with
            | SHO_Nothing  => { }
            | SHO_Choice _ => { }  (* should not happen *)
            | SHO_Guess _  => { }  (* should not happen *)
            | SHO_OK       => {
                state <- IPS_Guesser_WaitToAdvResult result;
              }
            | SHO_Error    => {
                state <- IPS_Guesser_WaitToAdvError;
              }
            end;
          }
        | IPS_Guesser_WaitToAdvResult _   => { }
        | IPS_Guesser_WaitToAdvError      => { }
        | IPS_Guesser_Final               => { }
        end;
      }
    | Malicious => { Sim.malicious_deliver(); }
    end;
  }
}.

(* relational lemmas relating the malicious party and its interface to
   the memory in the real and ideal protocols *)

(* preservation of gm_invar *)

lemma malic_trans_virt_addr_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.trans_virt_addr ~
   MaliciousMemory.PartyMemory.trans_virt_addr :
   ={glob Memory, addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory, addr} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_trans_virt_addr_gm_invar.
sim.
qed.

lemma malic_create_key_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.create_key ~
   MaliciousMemory.PartyMemory.create_key :
   ={glob Memory} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_create_key_gm_invar.
sim.
qed.

lemma malic_is_key_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.is_key ~
   MaliciousMemory.PartyMemory.is_key :
   ={glob Memory, key_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory, key_addr} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_is_key_gm_invar.
sim.
qed.

lemma malic_create_cell_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.create_cell ~
   MaliciousMemory.PartyMemory.create_cell :
   ={glob Memory, key_addr, b} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory, key_addr, b} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_create_cell_gm_invar.
sim.
qed.

lemma malic_is_cell_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.is_cell ~
   MaliciousMemory.PartyMemory.is_cell :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory, cell_addr} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_is_cell_gm_invar.
sim.
qed.

lemma malic_unlock_cell_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.unlock_cell ~
   MaliciousMemory.PartyMemory.unlock_cell :
   ={glob Memory, cell_addr, key_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory, cell_addr, key_addr} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_unlock_cell_gm_invar.
sim.
qed.

lemma malic_contents_cell_gm_invar_equiv :
  equiv
  [MaliciousMemory.PartyMemory.contents_cell ~
   MaliciousMemory.PartyMemory.contents_cell :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ : ={glob Memory, cell_addr} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
apply MaliciousMemory.party_memory_contents_cell_gm_invar.
sim.
qed.

lemma malicious_party_gm_invar_from_adv (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).from_adv ~
   Malicious(MaliciousMemory.PartyMemory).from_adv :
   ={glob Malicious, glob Memory, msg} /\ gm_invar (glob Memory){1} ==>
   ={glob Malicious, glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
proc (={glob Memory} /\ gm_invar (glob Memory){1}) => //.
by conseq malic_trans_virt_addr_gm_invar_equiv.
by conseq malic_create_key_gm_invar_equiv.
by conseq malic_is_key_gm_invar_equiv.
by conseq malic_create_cell_gm_invar_equiv.
by conseq malic_is_cell_gm_invar_equiv.
by conseq malic_unlock_cell_gm_invar_equiv.
by conseq malic_contents_cell_gm_invar_equiv.
qed.

lemma malicious_party_gm_invar_to_adv (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).to_adv ~
   Malicious(MaliciousMemory.PartyMemory).to_adv :
   ={glob Malicious, glob Memory} /\ gm_invar (glob Memory){1} ==>
   ={glob Malicious, glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
proc (={glob Memory} /\ gm_invar (glob Memory){1}) => //.
by conseq malic_trans_virt_addr_gm_invar_equiv.
by conseq malic_create_key_gm_invar_equiv.
by conseq malic_is_key_gm_invar_equiv.
by conseq malic_create_cell_gm_invar_equiv.
by conseq malic_is_cell_gm_invar_equiv.
by conseq malic_unlock_cell_gm_invar_equiv.
by conseq malic_contents_cell_gm_invar_equiv.
qed.

lemma malicious_party_gm_invar_from_other (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).from_other ~
   Malicious(MaliciousMemory.PartyMemory).from_other :
   ={glob Malicious, glob Memory, msg} /\ gm_invar (glob Memory){1} ==>
   ={glob Malicious, glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
proc (={glob Memory} /\ gm_invar (glob Memory){1}) => //.
by conseq malic_trans_virt_addr_gm_invar_equiv.
by conseq malic_create_key_gm_invar_equiv.
by conseq malic_is_key_gm_invar_equiv.
by conseq malic_create_cell_gm_invar_equiv.
by conseq malic_is_cell_gm_invar_equiv.
by conseq malic_unlock_cell_gm_invar_equiv.
by conseq malic_contents_cell_gm_invar_equiv.
qed.

lemma malicious_party_gm_invar_to_other (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).to_other ~
   Malicious(MaliciousMemory.PartyMemory).to_other :
   ={glob Malicious, glob Memory} /\ gm_invar (glob Memory){1} ==>
   ={glob Malicious, glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
proc (={glob Memory} /\ gm_invar (glob Memory){1}) => //.
by conseq malic_trans_virt_addr_gm_invar_equiv.
by conseq malic_create_key_gm_invar_equiv.
by conseq malic_is_key_gm_invar_equiv.
by conseq malic_create_cell_gm_invar_equiv.
by conseq malic_is_cell_gm_invar_equiv.
by conseq malic_unlock_cell_gm_invar_equiv.
by conseq malic_contents_cell_gm_invar_equiv.
qed.

(* preservation of guesser gm invariant *)

op gm_invar_guesser
   (gm : gm, cell_hon_virt_addr cell_phys_addr : addr, cont : bool) : bool =
  exists (key : key, locked : bool),
  (oget (gm_to_virt_map gm).[Honest]).[cell_hon_virt_addr] =
  Some cell_phys_addr /\
  (gm_to_phys_map gm).[cell_phys_addr] =
  Some (Cell {|key = key; cont = cont; locked = locked|}).

lemma malic_trans_virt_addr_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.trans_virt_addr ~
   MaliciousMemory.PartyMemory.trans_virt_addr :
   ={glob Memory, addr} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory, addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; sp 2.
if.
auto; progress.
rewrite /gm_invar_guesser /gm_to_honest_virt_map /gm_to_phys_map /=.
rewrite /gm_invar_guesser in H0.
elim H0 => key locked H0.
exists key locked.
smt(get_setE oget_some).
auto.
apply malic_trans_virt_addr_gm_invar_equiv.
qed.

lemma malic_create_key_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.create_key ~
   MaliciousMemory.PartyMemory.create_key :
   ={glob Memory} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; auto; smt(get_setE).
apply malic_create_key_gm_invar_equiv.
qed.

lemma malic_is_key_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.is_key ~
   MaliciousMemory.PartyMemory.is_key :
   ={glob Memory, key_addr} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory, key_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; auto.
apply malic_is_key_gm_invar_equiv.
qed.

lemma malic_create_cell_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.create_cell ~
   MaliciousMemory.PartyMemory.create_cell :
   ={glob Memory, key_addr, b} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory, key_addr, b} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; auto; smt(get_setE).
apply malic_create_cell_gm_invar_equiv.
qed.

lemma malic_is_cell_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.is_cell ~
   MaliciousMemory.PartyMemory.is_cell :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; auto.
apply malic_is_cell_gm_invar_equiv.
qed.

lemma malic_unlock_cell_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.unlock_cell ~
   MaliciousMemory.PartyMemory.unlock_cell :
   ={glob Memory, cell_addr, key_addr} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory, cell_addr, key_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; auto; smt(get_setE).
apply malic_unlock_cell_gm_invar_equiv.
qed.

lemma malic_contents_cell_gm_invar_guesser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.contents_cell ~
   MaliciousMemory.PartyMemory.contents_cell :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr
   cell_phys_addr cont].
proof.
conseq
  (_ :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1})
  (_ :
   gm_invar (glob Memory) /\
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont ==>
   gm_invar_guesser (glob Memory) cell_hon_virt_addr cell_phys_addr
   cont)
  (_ : true ==> true) => //.
proc; inline*; auto; smt().
apply malic_contents_cell_gm_invar_equiv.
qed.

lemma malicious_party_gm_invar_guesser_from_adv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).from_adv ~
   Malicious(MaliciousMemory.PartyMemory).from_adv :
   ={glob Malicious, glob Memory, msg} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont ==>
   ={glob Malicious, glob Memory, res} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont].
proof.
proc
  (={glob Memory} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont) => //.
by conseq
   (malic_trans_virt_addr_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_unlock_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_contents_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
qed.

lemma malicious_party_gm_invar_guesser_to_adv
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).to_adv ~
   Malicious(MaliciousMemory.PartyMemory).to_adv :
   ={glob Malicious, glob Memory} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont ==>
   ={glob Malicious, glob Memory, res} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont].
proof.
proc
  (={glob Memory} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont) => //.
by conseq
   (malic_trans_virt_addr_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_unlock_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_contents_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
qed.

lemma malicious_party_gm_invar_guesser_from_other
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).from_other ~
   Malicious(MaliciousMemory.PartyMemory).from_other :
   ={glob Malicious, glob Memory, msg} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont ==>
   ={glob Malicious, glob Memory, res} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont].
proof.
proc
  (={glob Memory} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont) => //.
by conseq
   (malic_trans_virt_addr_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_unlock_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_contents_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
qed.

lemma malicious_party_gm_invar_guesser_to_other
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).to_other ~
   Malicious(MaliciousMemory.PartyMemory).to_other :
   ={glob Malicious, glob Memory} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont ==>
   ={glob Malicious, glob Memory, res} /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont].
proof.
proc
  (={glob Memory} /\ gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr
   cont) => //.
by conseq
   (malic_trans_virt_addr_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_key_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_create_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_is_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_unlock_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
by conseq
   (malic_contents_cell_gm_invar_guesser_equiv
    cell_hon_virt_addr cell_phys_addr cont).
qed.

(* preservation of chooser gm relational invariant *)

op gm_rel_invar_chooser
   (gm1 gm2 : gm, cell_hon_virt_addr cell_phys_addr : addr, key : key,
    cont : bool) : bool =
  gm_to_next_key gm1        = gm_to_next_key gm2              /\
  gm_to_next_phys_addr gm1  = gm_to_next_phys_addr gm2        /\
  gm_to_next_virt_addr gm1  = gm_to_next_virt_addr gm2        /\
  gm_to_virt_map gm1        = gm_to_virt_map gm2              /\
  fdom (gm_to_phys_map gm1) = fdom (gm_to_phys_map gm2)       /\
  (forall (phys_addr' : addr),
   phys_addr' \in gm_to_phys_map gm1 =>
   phys_addr' <> cell_phys_addr =>
   (gm_to_phys_map gm1).[phys_addr'] =
   (gm_to_phys_map gm2).[phys_addr'])                         /\
  (* *)
  (oget (gm_to_virt_map gm1).[Honest])
    .[cell_hon_virt_addr] = Some cell_phys_addr               /\
  (gm_to_phys_map gm1).[cell_phys_addr] =
  Some (Cell {|key = key; cont = cont; locked = true|})       /\
  (gm_to_phys_map gm2).[cell_phys_addr] =
  Some (Cell {|key = key; cont = true; locked = true|})       /\
  (* *)
  (forall (mal_virt_addr : addr),
   mal_virt_addr \in oget (gm_to_virt_map gm1).[Malicious] =>
   let phys_addr' =
     oget
     (oget (gm_to_virt_map gm1).[Malicious])
       .[mal_virt_addr] in
   oget (gm_to_phys_map gm1).[phys_addr'] <> Key key).

lemma gm_rel_invar_chooser_malic_key_not_accessible_gm2
      (gm1 gm2 : gm, cell_hon_virt_addr cell_phys_addr : addr, key : key,
       cont : bool) :
  gm_invar gm1 =>
  gm_rel_invar_chooser gm1 gm2 cell_hon_virt_addr cell_phys_addr key cont =>
  (forall (mal_virt_addr : addr),
   mal_virt_addr \in oget (gm_to_virt_map gm2).[Malicious] =>
   let phys_addr' =
     oget
     (oget (gm_to_virt_map gm2).[Malicious])
       .[mal_virt_addr] in
   oget (gm_to_phys_map gm1).[phys_addr'] <> Key key).
proof. smt(). qed.

lemma malic_trans_virt_addr_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.trans_virt_addr ~
   MaliciousMemory.PartyMemory.trans_virt_addr :
   ={addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_trans_virt_addr_gm_invar.
apply MaliciousMemory.party_memory_trans_virt_addr_gm_invar.
proc; inline*; sp 2 2.
(if; first smt()); auto; progress; smt(get_setE oget_some).
qed.

lemma malic_create_key_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.create_key ~
   MaliciousMemory.PartyMemory.create_key :
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_create_key_gm_invar.
apply MaliciousMemory.party_memory_create_key_gm_invar.
proc; inline*; auto; smt(get_setE fdom_set).
qed.

lemma malic_is_key_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.is_key ~
   MaliciousMemory.PartyMemory.is_key :
   ={key_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={key_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_is_key_gm_invar.
apply MaliciousMemory.party_memory_is_key_gm_invar.
proc; inline*; auto; smt(mem_fdom).
qed.

lemma malic_create_cell_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.create_cell ~
   MaliciousMemory.PartyMemory.create_cell :
   ={key_addr, b} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={key_addr, b} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_create_cell_gm_invar.
apply MaliciousMemory.party_memory_create_cell_gm_invar.
proc; inline*; sp 3 3.
if; first smt().
match; first 2 smt(mem_fdom).
move => key1 key2.
auto; progress; smt(get_setE fdom_set mem_fdom).
move => cell1 cell2.
auto.
auto.
qed.

lemma malic_is_cell_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.is_cell ~
   MaliciousMemory.PartyMemory.is_cell :
   ={cell_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={cell_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_is_cell_gm_invar.
apply MaliciousMemory.party_memory_is_cell_gm_invar.
proc; inline*; auto; smt(mem_fdom).
qed.

lemma malic_unlock_cell_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.unlock_cell ~
   MaliciousMemory.PartyMemory.unlock_cell :
   ={cell_addr, key_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={cell_addr, key_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_unlock_cell_gm_invar.
apply MaliciousMemory.party_memory_unlock_cell_gm_invar.
proc; inline*; sp 3 3.
if; first smt().
sp 2 2.
if; first smt(mem_fdom).
sp 2 2.
if; first smt(mem_fdom).
(auto; progress; first 6 smt(get_setE fdom_set mem_fdom fdomP));
  last 4 smt(get_setE fdom_set mem_fdom fdomP).
rewrite /gm_to_phys_map /=.
case (phys_addr' = Memory.next_phys_addr{1}) => [eq_pa'_npa | neq_pa'_npa].
rewrite 2!get_setE eq_pa'_npa.
have -> // : Memory.next_phys_addr{2} = Memory.next_phys_addr{1}.
smt(). smt(mem_fdom).
rewrite 2!get_setE.
have -> /= : Memory.next_phys_addr{2} = Memory.next_phys_addr{1}.
smt().
rewrite neq_pa'_npa /=; smt(fdomP).
auto. auto. auto.
qed.

lemma malic_contents_cell_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [MaliciousMemory.PartyMemory.contents_cell ~
   MaliciousMemory.PartyMemory.contents_cell :
   ={cell_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={cell_addr} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply MaliciousMemory.party_memory_contents_cell_gm_invar.
apply MaliciousMemory.party_memory_contents_cell_gm_invar.
proc; inline*; auto; smt(mem_fdom).
qed.

lemma malicious_party_gm_rel_invar_chooser_from_adv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).from_adv ~
   Malicious(MaliciousMemory.PartyMemory).from_adv :
   ={glob Malicious, msg} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={glob Malicious, res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
proc
  (gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont) => //.
by conseq
   (malic_trans_virt_addr_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_unlock_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_contents_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
qed.

lemma malicious_party_gm_rel_invar_chooser_to_adv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).to_adv ~
   Malicious(MaliciousMemory.PartyMemory).to_adv :
   ={glob Malicious} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={glob Malicious, res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
proc
  (gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont) => //.
by conseq
   (malic_trans_virt_addr_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_unlock_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_contents_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
qed.

lemma malicious_party_gm_rel_invar_chooser_from_other
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).from_other ~
   Malicious(MaliciousMemory.PartyMemory).from_other :
   ={glob Malicious, msg} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={glob Malicious, res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
proc
  (gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont) => //.
by conseq
   (malic_trans_virt_addr_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_unlock_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_contents_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
qed.

lemma malicious_party_gm_rel_invar_chooser_to_other
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool)
      (Malicious <: PARTY{-Memory}) :
  equiv
  [Malicious(MaliciousMemory.PartyMemory).to_other ~
   Malicious(MaliciousMemory.PartyMemory).to_other :
   ={glob Malicious} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={glob Malicious, res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
proc
  (gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont) => //.
by conseq
   (malic_trans_virt_addr_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_key_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_create_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_is_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_unlock_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
by conseq
   (malic_contents_cell_gm_rel_invar_chooser_equiv
    cell_hon_virt_addr cell_phys_addr key cont).
qed.

(* lemmas regarding the honest party of the simulator and its
   interface to the memory -- which provides greater access
   than the normal party memory (see the procedures defined
   below)

   some of the lemmas are relational, relating the honest party of the
   real protocol with the honest part of the simulator *)

lemma honest_trans_virt_addr_of_cell_gm_invar_chooser_equiv :
  equiv
  [HonestMemory.PartyMemory.trans_virt_addr ~
   HonestMemory.PartyMemory.trans_virt_addr :
   ={glob Memory, addr} /\ gm_invar (glob Memory){1} ==>
   ={glob Memory, res} /\ gm_invar (glob Memory){1}].
proof.
conseq
  (_ :
   ={glob Memory, addr} ==> ={glob Memory, res})
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply HonestMemory.party_memory_trans_virt_addr_gm_invar.
apply HonestMemory.party_memory_trans_virt_addr_gm_invar.
sim.
qed.

lemma honest_trans_virt_addr_of_cell_gm_rel_invar_chooser_equiv
      (cell_hon_virt_addr cell_phys_addr : addr, key : key, cont : bool) :
  equiv
  [HonestMemory.PartyMemory.trans_virt_addr ~
   HonestMemory.PartyMemory.trans_virt_addr :
   ={addr} /\ addr{1} = cell_hon_virt_addr /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){2} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont].
proof.
conseq
  (_ :
   ={addr} /\ addr{1} = cell_hon_virt_addr /\
   gm_invar (glob Memory){1} /\ gm_invar (glob Memory){1} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont ==>
   ={res} /\
   gm_rel_invar_chooser (glob Memory){1} (glob Memory){2}
   cell_hon_virt_addr cell_phys_addr key cont)
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory)) => //.
apply HonestMemory.party_memory_trans_virt_addr_gm_invar.
apply HonestMemory.party_memory_trans_virt_addr_gm_invar.
proc; inline*; sp 2 2.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
auto; smt(get_setE).
qed.

lemma real_simulator_unlock_cell_gm_invar_guesser
      (cell_hon_virt_addr cell_phys_addr : addr, cont : bool) :
  equiv
  [HonestMemory.PartyMemory.unlock_cell ~ HonestMemory.PartyMemory.unlock_cell :
   ={cell_addr, key_addr, glob Memory} /\ cell_addr{1} = cell_hon_virt_addr /\
   gm_invar (glob Memory){1} /\
   gm_invar_guesser (glob Memory){1} cell_hon_virt_addr cell_phys_addr cont ==>
   ={res, glob Memory} /\ gm_invar (glob Memory){1} /\
   (res{1} <> None =>
    (exists (phys_addr : addr, cell : cell),
    (oget (gm_to_virt_map (glob Memory){1}).[Honest]).[oget res{1}] =
    Some phys_addr /\
    (gm_to_phys_map (glob Memory){1}).[phys_addr] = Some (Cell cell) /\
    cell.`cont = cont /\ cell.`locked = false))].
proof.
conseq
  (_ :
   _ ==>
   ={res, glob Memory} /\
   (res{1} <> None =>
    (exists (phys_addr : addr, cell : cell),
    (oget (gm_to_virt_map (glob Memory){1}).[Honest]).[oget res{1}] =
    Some phys_addr /\
    (gm_to_phys_map (glob Memory){1}).[phys_addr] = Some (Cell cell) /\
    cell.`cont = cont /\ cell.`locked = false)))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : _ ==> _) => //.
apply HonestMemory.party_memory_unlock_cell_gm_invar.
proc; inline *; sp 3 3.
if => //.
sp 2 2.
if => //.
sp 2 2.
if => //.
auto => &1 &2 |>.
rewrite /gm_to_virt_map /gm_to_phys_map /= get_set_sameE oget_some.
rewrite get_set_sameE /=.
smt(get_setE).
auto. auto. auto.
qed.

(* extra procedures for honest party of simulator *)

module type EXTRA_HONEST_MEMORY_SIM = {
  (* if cell_addr is the virtual address for the honest party
     of a cell, modify the contents of the cell to be b, without
     changing its physical address; otherwise, do nothing *)

  proc modify_cell(cell_addr : addr, b : bool) : unit

  (* if cell_addr is the virtual address for the honest party of a
     cell, return Some of the cell's contents; otherwise, return None
     *)

  proc read_cell(cell_addr : addr) : bool option
}.

module ExtraHonestMemorySim : EXTRA_HONEST_MEMORY_SIM = {
  proc modify_cell(cell_addr : addr, b : bool) : unit = {
    var r : bool; var phys_addr, virt_addr : addr;
    var obj_cell; var new_cell : cell;
    if (cell_addr \in oget Memory.virt_map.[Honest]) {
      phys_addr <- oget (oget Memory.virt_map.[Honest]).[cell_addr];
      obj_cell <- oget Memory.phys_map.[phys_addr];
      match obj_cell with
      | Key _     => { }
      | Cell cell => {
          new_cell <- {|key = cell.`key; cont = b; locked = cell.`locked|};
          Memory.phys_map.[phys_addr] <- Cell new_cell;
        }
      end;
    }
  }

  proc read_cell(cell_addr : addr) : bool option = {
    var r : bool option;  var phys_addr, virt_addr : addr;
    var obj_cell; var cell : cell;
    if (cell_addr \in oget Memory.virt_map.[Honest]) {
      phys_addr <- oget (oget Memory.virt_map.[Honest]).[cell_addr];
      obj_cell <- oget Memory.phys_map.[phys_addr];
      match obj_cell with
      | Key _     => { r <- None; }
      | Cell cell => { r <- Some cell.`cont; }
      end;
    }
    else { r <- None; }
    return r;
  }
}.

lemma simulator_modify_cell_gm_rel_invar_chooser
      (gm1 : gm, cell_hon_virt_addr cell_phys_addr : addr,
       key : key, cont : bool) :
  phoare
  [ExtraHonestMemorySim.modify_cell :
   cell_addr = cell_hon_virt_addr /\ b = cont /\
   gm_rel_invar_chooser gm1 (glob Memory) cell_hon_virt_addr cell_phys_addr
   key cont ==>
   gm1 = glob Memory] = 1%r.
proof.
conseq (_ : true ==> true) (_ : _ ==> _) => //.
proc => /=.
if.
sp.
match Cell 1; first auto; smt().
(auto; progress; apply gm_eqP; first 2 smt()); last 2 smt().
rewrite /gm_to_phys_map /=.
have -> :
  oget (oget Memory.virt_map{hr}.[Honest]).[cell_addr{hr}] =
  cell_phys_addr by smt().
have doms_eq :
  fdom (gm_to_phys_map gm1) = fdom Memory.phys_map{hr} by smt().
apply fmap_eqP => p_addr.
case (p_addr = cell_phys_addr) => [-> | neq].
have -> : cell{hr}.`key = key by smt().
have -> : cell{hr}.`locked = true by smt().
rewrite get_set_sameE /#.
rewrite get_setE neq /=.
case (p_addr \in (gm_to_phys_map gm1)) => [/# | not_in_dom].
have -> : (gm_to_phys_map gm1).[p_addr] = None by rewrite -domNE.
have -> // : Memory.phys_map{hr}.[p_addr] = None
  by rewrite -domNE -mem_fdom -doms_eq mem_fdom.
auto; smt().
proc; auto; smt().
qed.

lemma is_cell_read_cell_good (gm : gm, cell_addr' : addr) :
  equiv
  [HonestMemory.PartyMemory.is_cell ~ ExtraHonestMemorySim.read_cell :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} /\
   gm = (glob Memory){1} /\ cell_addr' = cell_addr{1} /\
   cell_addr_good Honest gm cell_addr{1} ==>
   res{1} /\
   res{2} = Some ((cell_addr_to_cell Honest gm cell_addr').`cont)].
proof.
proc; inline*; sp 2 0.
if => //; auto; smt().
qed.

lemma is_cell_read_cell_bad (gm : gm, cell_addr' : addr) :
  equiv
  [HonestMemory.PartyMemory.is_cell ~ ExtraHonestMemorySim.read_cell :
   ={glob Memory, cell_addr} /\ gm_invar (glob Memory){1} /\
   gm = (glob Memory){1} /\ cell_addr' = cell_addr{1} /\
   ! cell_addr_good Honest gm cell_addr{1} ==>
   ={glob Memory} /\ gm_invar (glob Memory){1} /\ gm = (glob Memory){1} /\
   ! res{1} /\ res{2} = None].
proof.
proc; inline*; sp 2 0.
if => //; auto; smt().
qed.

type sim_honest_party_state = [
  (* chooser *)
  | SHPS_Chooser_WaitFromIPStart
  | SHPS_Chooser_WaitToOtherCellAddr   of addr  (* key addr *)
                                        & addr  (* cell addr *)
  | SHPS_Chooser_WaitFromOtherGuess    of addr  (* key addr *)
                                        & addr  (* cell addr *)
  | SHPS_Chooser_WaitFromIPChoice      of addr  (* key addr *)
                                        & addr  (* cell addr *)
  | SHPS_Chooser_WaitToOtherKeyAddr    of addr  (* key addr *)
  | SHPS_Chooser_Final
  (* guesser *)
  | SHPS_Guesser_WaitFromIPStart
  | SHPS_Guesser_WaitFromOtherCellAddr
  | SHPS_Guesser_WaitFromIPGuess       of addr  (* cell addr *)
  | SHPS_Guesser_WaitToOtherGuess      of bool  (* choice *)
                                        & addr  (* cell addr *)
  | SHPS_Guesser_WaitFromOtherKeyAddr  of addr  (* cell addr *)
  | SHPS_Guesser_Final
].

(* the simulator, parameterized by a malicious party *)

module Simulator (Malicious : PARTY) : SIMULATOR = {
  (* connect the malicious party with its party memory *)

  module M = Malicious(MaliciousMemory.PartyMemory)

  (* the honest party with its increased powers *)

  module HM   = HonestMemory.PartyMemory
  module EHMS = ExtraHonestMemorySim

  module H = {
    var state : sim_honest_party_state

    proc init(chooser : bool) : unit = {
      state <-
        if chooser
        then SHPS_Chooser_WaitFromIPStart
        else SHPS_Guesser_WaitFromIPStart;
    }

    proc start() : unit = {
      var key_addr : addr; var cell_addr : addr;
      var cell_addr_opt : addr option;
      match state with
      | SHPS_Chooser_WaitFromIPStart         => {
          key_addr <@ HM.create_key();
          (* cell contents is always true, as simulator does
             not yet know choice *)
          cell_addr_opt <@ HM.create_cell(key_addr, true);
          cell_addr <- oget cell_addr_opt;
          state <- SHPS_Chooser_WaitToOtherCellAddr key_addr cell_addr;
        }
      | SHPS_Chooser_WaitToOtherCellAddr _ _ => { }
      | SHPS_Chooser_WaitFromOtherGuess _ _  => { }
      | SHPS_Chooser_WaitFromIPChoice _ _    => { }
      | SHPS_Chooser_WaitToOtherKeyAddr _    => { }
      | SHPS_Chooser_Final                   => { }
      | SHPS_Guesser_WaitFromIPStart         => {
          state <- SHPS_Guesser_WaitFromOtherCellAddr;
        }
      | SHPS_Guesser_WaitFromOtherCellAddr   => { }
      | SHPS_Guesser_WaitFromIPGuess _       => { }
      | SHPS_Guesser_WaitToOtherGuess _ _    => { }
      | SHPS_Guesser_WaitFromOtherKeyAddr _  => { }
      | SHPS_Guesser_Final                   => { }
      end;
    }

    proc choice(choice : bool) : unit = {
      var b : bool;
      match state with
      | SHPS_Chooser_WaitFromIPStart                     => { }
      | SHPS_Chooser_WaitToOtherCellAddr _ _             => { }
      | SHPS_Chooser_WaitFromOtherGuess _ _              => { }
      | SHPS_Chooser_WaitFromIPChoice key_addr cell_addr => {
          EHMS.modify_cell(cell_addr, choice);
          state <- SHPS_Chooser_WaitToOtherKeyAddr key_addr;
        }
      | SHPS_Chooser_WaitToOtherKeyAddr _                => { }
      | SHPS_Chooser_Final                               => { }
      | SHPS_Guesser_WaitFromIPStart                     => { }
      | SHPS_Guesser_WaitFromOtherCellAddr               => { }
      | SHPS_Guesser_WaitFromIPGuess _                   => { }
      | SHPS_Guesser_WaitToOtherGuess _ _                => { }
      | SHPS_Guesser_WaitFromOtherKeyAddr _              => { }
      | SHPS_Guesser_Final                               => { }
      end;
    }

    proc guess(guess : bool) : unit = {
      match state with
      | SHPS_Chooser_WaitFromIPStart           => { }
      | SHPS_Chooser_WaitToOtherCellAddr _ _   => { }
      | SHPS_Chooser_WaitFromOtherGuess _ _    => { }
      | SHPS_Chooser_WaitFromIPChoice _ _      => { }
      | SHPS_Chooser_WaitToOtherKeyAddr _      => { }
      | SHPS_Chooser_Final                     => { }
      | SHPS_Guesser_WaitFromIPStart           => { }
      | SHPS_Guesser_WaitFromOtherCellAddr     => { }
      | SHPS_Guesser_WaitFromIPGuess cell_addr => {
          state <- SHPS_Guesser_WaitToOtherGuess guess cell_addr;
        }
      | SHPS_Guesser_WaitToOtherGuess _ _      => { }
      | SHPS_Guesser_WaitFromOtherKeyAddr _    => { }
      | SHPS_Guesser_Final                     => { }
      end;
    }

    proc from_other(msg : msg) : bool * sim_honest_output = {
      var r : bool <- false; var b_opt : bool option;
      var sho : sim_honest_output <- SHO_Nothing;
      var choice_opt : bool option;
      var unlocked_cell_addr_opt : addr option;
      match state with
      | SHPS_Chooser_WaitFromIPStart                       => { }
      | SHPS_Chooser_WaitToOtherCellAddr _ _               => { }
      | SHPS_Chooser_WaitFromOtherGuess key_addr cell_addr => {
          r <- true; sho <- SHO_Error; state <- SHPS_Chooser_Final;
          match msg with
          | Result _    => { }
          | Choice _    => { }
          | Guess guess => {
              sho <- SHO_Guess guess;
              state <- SHPS_Chooser_WaitFromIPChoice key_addr cell_addr;
            }
          | CellAddr _  => { }
          | KeyAddr  _  => { }
          | Error       => { }
          | Int _       => { }
          end;
        }
      | SHPS_Chooser_WaitFromIPChoice _ _                  => { }
      | SHPS_Chooser_WaitToOtherKeyAddr _                  => { }
      | SHPS_Chooser_Final                                 => { }
      | SHPS_Guesser_WaitFromIPStart                       => { }
      | SHPS_Guesser_WaitFromOtherCellAddr                 => {
          r <- true; sho <- SHO_Error; state <- SHPS_Guesser_Final;
          match msg with
          | Result _           => { }
          | Choice _           => { }
          | Guess _            => { }
          | CellAddr cell_addr => {
              choice_opt <@ EHMS.read_cell(cell_addr);
              match choice_opt with
              | None        => { }
              | Some choice => {
                  sho <- SHO_Choice choice;
                  state <- SHPS_Guesser_WaitFromIPGuess cell_addr;
                }
              end;
            }
          | KeyAddr  _         => { }
          | Error              => { }
          | Int _              => { }
          end;
        }
      | SHPS_Guesser_WaitFromIPGuess _                     => { }
      | SHPS_Guesser_WaitToOtherGuess _ _                  => { }
      | SHPS_Guesser_WaitFromOtherKeyAddr cell_addr        => {
          r <- true; sho <- SHO_Error; state <- SHPS_Guesser_Final;
          match msg with
          | Result _         => { }
          | Choice _         => { }
          | Guess _          => { }
          | CellAddr _       => { }
          | KeyAddr key_addr => {
              unlocked_cell_addr_opt <@ HM.unlock_cell(cell_addr, key_addr);
              match unlocked_cell_addr_opt with
              | None                    => { }
              | Some unlocked_cell_addr => {
                  (* we already know the contents of this cell *)
                  sho <- SHO_OK; state <- SHPS_Guesser_Final;
                }
              end;
            }
          | Error            => { }
          | Int _            => { }
          end;
        }
      | SHPS_Guesser_Final                                 => { }
      end;
      return (r, sho);
    }

    proc to_other() : msg option * sim_honest_output = {
      var r : msg option <- None;
      var sho : sim_honest_output <- SHO_Nothing;
      var trans_addr_opt : addr option;
      match state with
      | SHPS_Chooser_WaitFromIPStart                        => { }
      | SHPS_Chooser_WaitToOtherCellAddr key_addr cell_addr => {
          trans_addr_opt <@ HM.trans_virt_addr(cell_addr);
          r <- Some (CellAddr (oget trans_addr_opt));
          state <- SHPS_Chooser_WaitFromOtherGuess key_addr cell_addr;
        }
      | SHPS_Chooser_WaitFromOtherGuess _ _                 => { }
      | SHPS_Chooser_WaitFromIPChoice _ _                   => { }
      | SHPS_Chooser_WaitToOtherKeyAddr key_addr            => {
          trans_addr_opt <@ HM.trans_virt_addr(key_addr);
          r <- Some (KeyAddr (oget trans_addr_opt));
          sho <- SHO_OK; state <- SHPS_Chooser_Final;
        }
      | SHPS_Chooser_Final                                  => { }
      | SHPS_Guesser_WaitFromIPStart                        => { }
      | SHPS_Guesser_WaitFromOtherCellAddr                  => { }
      | SHPS_Guesser_WaitFromIPGuess _                      => { }
      | SHPS_Guesser_WaitToOtherGuess guess cell_addr       => {
          r <- Some (Guess guess);
          state <- SHPS_Guesser_WaitFromOtherKeyAddr cell_addr;
        }
      | SHPS_Guesser_WaitFromOtherKeyAddr _                 => { }
      | SHPS_Guesser_Final                                  => { }
      end;
      return (r, sho);
    }
  }

  var to_malicious_queue, to_honest_queue : msg list

  proc init(chooser : party) : unit = {
    to_malicious_queue <- []; to_honest_queue <- [];
    match chooser with
    | Honest    => {
        H.init(true); M.init(false);
      }
    | Malicious => {
        H.init(false); M.init(true);
      }
    end;
    Memory.init();  (* H and M can't use memory *)
  }

  proc honest_start  = H.start
  proc honest_choice = H.choice
  proc honest_guess  = H.guess

  proc honest_queue() : sim_honest_output = {
    var msg_opt : msg option; var sho : sim_honest_output;
    (msg_opt, sho) <@ H.to_other();
    match msg_opt with
    | None     => { }
    | Some msg => {
        to_malicious_queue <- to_malicious_queue ++ [msg];
      }
    end;
    return sho;
  }

  proc honest_deliver() : sim_honest_output = {
    var b : bool; var sho : sim_honest_output <- SHO_Nothing;
    match to_honest_queue with
    | []          => { }
    | msg :: msgs => {
        (b, sho) <@ H.from_other(msg);
        if (b) { to_honest_queue <- msgs; }
      }
    end;
    return sho;
  }

  proc malicious_from_adv = M.from_adv
  proc malicious_to_adv   = M.to_adv

  proc malicious_queue() : unit = {
    var msg_opt : msg option;
    msg_opt <@ M.to_other();
    match msg_opt with
    | None     => { }
    | Some msg => {
        to_honest_queue <- to_honest_queue ++ [msg];
      }
    end;
  }

  proc malicious_deliver() : unit = {
    var b : bool;
    match to_malicious_queue with
    | []          => { }
    | msg :: msgs => {
        b <@ M.from_other(msg);
        if (b) { to_malicious_queue <- msgs; }
      }
    end;
  }
}.

(* even though this lemma is trivially true, the *proof*
   checks that Simulator and IdealProtocol do not read/write
   each others' global variables *)

lemma check_simulator_and_ideal_protocol_non_interference :
  forall (Malicious <: PARTY{-IdealProtocol}),
  exists (Sim <: SIMULATOR{-IdealProtocol}), true.
proof.
move => Malicious.
exists (Simulator(Malicious)).  (* this does the check *)
trivial.
qed.

(* the real experiment *)

module RealExper (Malicious : PARTY, Adv : ADV) =
  Exper(RealProtocol(Honest.Honest, Malicious), Adv).

(* the ideal experiment *)

module IdealExper (Malicious : PARTY, Adv : ADV) =
  Exper(IdealProtocol(Simulator(Malicious)), Adv).

(* relational invariant between states of RealProtocol and
   IdealProtocol/Simulator, plus the real and ideal memories *)

op ri_chooser_wait_choice_from_adv
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm) : bool =
  hps = Honest.HPS_Chooser_WaitFromAdvChoice /\
  ips = IPS_Chooser_WaitFromAdvChoice /\
  shps = SHPS_Chooser_WaitFromIPStart /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_chooser_wait_cell_addr_to_other
   (hps            : Honest.honest_party_state,
    ips            : ideal_protocol_state,
    shps           : sim_honest_party_state,
    mem1 mem2      : gm,
    choice         : bool,
    key_addr       : addr,  (* honest virtual *)
    cell_addr      : addr,  (* honest virtual *)
    cell_phys_addr : addr,
    key            : key) : bool =
  hps = Honest.HPS_Chooser_WaitToOtherCellAddr choice key_addr cell_addr /\
  ips = IPS_Chooser_WaitSimGuess choice /\
  shps = SHPS_Chooser_WaitToOtherCellAddr key_addr cell_addr /\
  gm_invar mem1 /\ gm_invar mem2 /\
  gm_rel_invar_chooser mem1 mem2 cell_addr cell_phys_addr key choice.

op ri_chooser_wait_guess_from_other
   (hps            : Honest.honest_party_state,
    ips            : ideal_protocol_state,
    shps           : sim_honest_party_state,
    mem1 mem2      : gm,
    choice         : bool,
    key_addr       : addr,  (* honest virtual *)
    cell_addr      : addr,  (* honest virtual *)
    cell_phys_addr : addr,
    key            : key) : bool =
  hps = Honest.HPS_Chooser_WaitFromOtherGuess choice key_addr /\
  ips = IPS_Chooser_WaitSimGuess choice /\
  shps = SHPS_Chooser_WaitFromOtherGuess key_addr cell_addr /\
  gm_invar mem1 /\ gm_invar mem2 /\
  gm_rel_invar_chooser mem1 mem2 cell_addr cell_phys_addr key choice.

op ri_chooser_wait_error_to_adv_gm_rel_invar_chooser
   (hps            : Honest.honest_party_state,
    ips            : ideal_protocol_state,
    shps           : sim_honest_party_state,
    mem1 mem2      : gm,
    choice         : bool,
    key_addr       : addr,  (* honest virtual *)
    cell_addr      : addr,  (* honest virtual *)
    cell_phys_addr : addr,
    key            : key) : bool =
  hps  = Honest.HPS_Chooser_WaitToAdvError /\
  ips  = IPS_Chooser_WaitToAdvError /\
  shps = SHPS_Chooser_Final /\
  gm_invar mem1 /\ gm_invar mem2 /\
  gm_rel_invar_chooser mem1 mem2 cell_addr cell_phys_addr key choice.

op ri_chooser_final_gm_rel_invar_chooser
   (hps            : Honest.honest_party_state,
    ips            : ideal_protocol_state,
    shps           : sim_honest_party_state,
    mem1 mem2      : gm,
    choice         : bool,
    key_addr       : addr,  (* honest virtual *)
    cell_addr      : addr,  (* honest virtual *)
    cell_phys_addr : addr,
    key            : key) : bool =
  hps  = Honest.HPS_Chooser_Final /\
  ips  = IPS_Chooser_Final /\
  shps = SHPS_Chooser_Final /\
  gm_invar mem1 /\ gm_invar mem2 /\
  gm_rel_invar_chooser mem1 mem2 cell_addr cell_phys_addr key choice.

op ri_chooser_wait_key_addr_to_other
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm,
    choice    : bool,
    key_addr  : addr,  (* honest virtual *)
    guess     : bool) : bool =
  hps = Honest.HPS_Chooser_WaitToOtherKeyAddr (guess <> choice) key_addr /\
  ips = IPS_Chooser_WaitSimOK (guess <> choice) /\
  shps = SHPS_Chooser_WaitToOtherKeyAddr key_addr /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_chooser_wait_result_to_adv
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm,
    result    : bool) : bool =
  hps  = Honest.HPS_Chooser_WaitToAdvResult result /\
  ips  = IPS_Chooser_WaitToAdvResult result /\
  shps = SHPS_Chooser_Final /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_chooser_wait_error_to_adv
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm) : bool =
  hps  = Honest.HPS_Chooser_WaitToAdvError /\
  ips  = IPS_Chooser_WaitToAdvError /\
  shps = SHPS_Chooser_Final /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_chooser_final
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm) : bool =
  hps  = Honest.HPS_Chooser_Final /\
  ips  = IPS_Chooser_Final /\
  shps = SHPS_Chooser_Final /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_guesser_wait_guess_from_adv
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm) : bool =
  hps  = Honest.HPS_Guesser_WaitFromAdvGuess /\
  ips  = IPS_Guesser_WaitFromAdvGuess /\
  shps = SHPS_Guesser_WaitFromIPStart /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_guesser_wait_cell_addr_from_other
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm,
    guess     : bool) : bool =
  hps  = Honest.HPS_Guesser_WaitFromOtherCellAddr guess /\
  ips  = IPS_Guesser_WaitSimChoice guess /\
  shps = SHPS_Guesser_WaitFromOtherCellAddr /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_guesser_wait_guess_to_other
   (hps            : Honest.honest_party_state,
    ips            : ideal_protocol_state,
    shps           : sim_honest_party_state,
    mem1 mem2      : gm,
    guess          : bool,
    cell_addr      : addr,  (* honest virtual *)
    cell_phys_addr : addr,
    cont           : bool,
    result         : bool) : bool =
  hps  = Honest.HPS_Guesser_WaitToOtherGuess guess cell_addr /\
  ips  = IPS_Guesser_WaitSimOK result /\
  shps = SHPS_Guesser_WaitToOtherGuess guess cell_addr /\
  mem1 = mem2 /\ gm_invar mem1 /\
  gm_invar_guesser mem2 cell_addr cell_phys_addr cont /\
  result = (guess = cont).

op ri_guesser_wait_key_addr_from_other
   (hps            : Honest.honest_party_state,
    ips            : ideal_protocol_state,
    shps           : sim_honest_party_state,
    mem1 mem2      : gm,
    guess          : bool,
    cell_addr      : addr,  (* honest virtual *)
    cell_phys_addr : addr,
    cont           : bool,
    result         : bool) : bool =
  hps  = Honest.HPS_Guesser_WaitFromOtherKeyAddr guess cell_addr /\
  ips  = IPS_Guesser_WaitSimOK result /\
  shps = SHPS_Guesser_WaitFromOtherKeyAddr cell_addr /\
  mem1 = mem2 /\ gm_invar mem1 /\
  gm_invar_guesser mem2 cell_addr cell_phys_addr cont /\
  result = (guess = cont).

op ri_guesser_wait_result_to_adv
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm,
    result    : bool) : bool =
  hps  = Honest.HPS_Guesser_WaitToAdvResult result /\
  ips  = IPS_Guesser_WaitToAdvResult result /\
  shps = SHPS_Guesser_Final /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_guesser_wait_error_to_adv
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm) : bool =
  hps  = Honest.HPS_Guesser_WaitToAdvError /\
  ips  = IPS_Guesser_WaitToAdvError /\
  shps = SHPS_Guesser_Final /\
  mem1 = mem2 /\ gm_invar mem1.

op ri_guesser_final
   (hps       : Honest.honest_party_state,
    ips       : ideal_protocol_state,
    shps      : sim_honest_party_state,
    mem1 mem2 : gm) : bool =
  hps  = Honest.HPS_Guesser_Final /\
  ips  = IPS_Guesser_Final /\
  shps = SHPS_Guesser_Final /\
  mem1 = mem2 /\ gm_invar mem1.

inductive rel_invar
          (hps       : Honest.honest_party_state,
           ips       : ideal_protocol_state,
           shps      : sim_honest_party_state,
           mem1 mem2 : gm) =
  | RI_Chooser_WaitChoiceFromAdv of
      (ri_chooser_wait_choice_from_adv hps ips shps mem1 mem2)
  | RI_Chooser_WaitCellAddrToOther
    (choice : bool, key_addr cell_addr cell_phys_addr : addr,
     key : key) of
      (ri_chooser_wait_cell_addr_to_other hps ips shps mem1 mem2
       choice key_addr cell_addr cell_phys_addr key)
  | RI_Chooser_WaitGuessFromOther
    (choice : bool, key_addr cell_addr cell_phys_addr : addr,
     key : key) of
      (ri_chooser_wait_guess_from_other hps ips shps mem1 mem2
       choice key_addr cell_addr cell_phys_addr key)
  | RI_Chooser_WaitErrorToAdv_GMRelInvarChooser
    (choice : bool, key_addr cell_addr cell_phys_addr : addr,
     key : key) of
      (ri_chooser_wait_error_to_adv_gm_rel_invar_chooser
       hps ips shps mem1 mem2
       choice key_addr cell_addr cell_phys_addr key)
  | RI_Chooser_Final_GMRelInvarChooser
    (choice : bool, key_addr cell_addr cell_phys_addr : addr,
     key : key) of
      (ri_chooser_final_gm_rel_invar_chooser
       hps ips shps mem1 mem2
       choice key_addr cell_addr cell_phys_addr key)
  | RI_Chooser_WaitKeyAddrToOther
    (choice : bool, key_addr : addr, guess : bool) of
      (ri_chooser_wait_key_addr_to_other hps ips shps mem1 mem2
       choice key_addr guess)
  | RI_Chooser_WaitResultToAdv (result : bool) of
      (ri_chooser_wait_result_to_adv hps ips shps mem1 mem2 result)
  | RI_Chooser_WaitErrorToAdv of
      (ri_chooser_wait_error_to_adv hps ips shps mem1 mem2)
  | RI_Chooser_Final of
      (ri_chooser_final hps ips shps mem1 mem2)
  | RI_Guesser_WaitGuessFromAdv of
      (ri_guesser_wait_guess_from_adv hps ips shps mem1 mem2)
  | RI_Guesser_WaitCellAddrFromOther
    (guess : bool) of
      (ri_guesser_wait_cell_addr_from_other hps ips shps mem1 mem2
       guess)
  | RI_Guesser_WaitGuessToOther
    (guess : bool, cell_addr : addr, cell_phys_addr : addr,
     cont : bool, result : bool) of
      (ri_guesser_wait_guess_to_other hps ips shps mem1 mem2
       guess cell_addr cell_phys_addr cont result)
  | RI_Guesser_WaitKeyAddrFromOther
    (guess : bool, cell_addr : addr, cell_phys_addr : addr,
     cont : bool, result : bool) of
      (ri_guesser_wait_key_addr_from_other hps ips shps mem1 mem2
       guess cell_addr cell_phys_addr cont result)
  | RI_Guesser_WaitResultToAdv (result : bool) of
      (ri_guesser_wait_result_to_adv hps ips shps mem1 mem2 result)
  | RI_Guesser_WaitErrorToAdv of
      (ri_guesser_wait_error_to_adv hps ips shps mem1 mem2)
  | RI_Guesser_Final of
      (ri_guesser_final hps ips shps mem1 mem2).

section.

declare module
          Malicious <:
          PARTY{-RealProtocol, -Honest.Honest, -IdealProtocol, -Simulator}.

lemma from_adv :
  equiv
  [RealProtocol(Honest.Honest, Malicious).from_adv ~
   IdealProtocol(Simulator(Malicious)).from_adv :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2} ==>
   ={res, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2}].
proof.
proc.
exlim Honest.Honest.state{1}, IdealProtocol.state{2},
      Simulator.H.state{2}, (glob Memory){1}, (glob Memory){2} =>
  hon_state ip_state sim_state mem1 mem2.
(* the "!!" is a hack to make the ambient case be a boolean one *)
case @[ambient] (!! rel_invar hon_state ip_state sim_state mem1 mem2) =>
  [/= [] | ?]; last exfalso; smt().
(* ri_chooser_wait_choice_from_adv *)
move => invar_ri_chooser_wait_choice_from_adv.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Chooser_WaitFromAdvChoice {1} 1; first auto; smt().
match IPS_Chooser_WaitFromAdvChoice {2} 1; first auto; smt().
case (get_as_Choice msg0{1} <> None).
match Choice {1} 1; first auto; smt().
match Choice {2} 1; first auto; smt().
inline Simulator(Malicious).honest_start.
match SHPS_Chooser_WaitFromIPStart {2} 1; first auto; smt().
wp.
exlim (glob Memory){1} => gm.
seq 1 1 :
  (={glob Malicious, glob Memory, party, key_addr, choice} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   gm_invar (glob Memory){1} /\ party{1} = Honest /\
   Memory.next_key{1} = gm_to_next_key gm + 1 /\
   Memory.next_phys_addr{1} = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map{1} =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <- Key (gm_to_next_key gm)] /\
   oget Memory.next_virt_addr.[Honest]{1} =
   oget (gm_to_next_virt_addr gm).[Honest] + 1 /\
   oget Memory.virt_map{1}.[Honest] =
   (oget (gm_to_virt_map gm).[Honest])
     .[oget (gm_to_next_virt_addr gm).[Honest] <- gm_to_next_phys_addr gm] /\
   key_addr{1} = oget (gm_to_next_virt_addr gm).[Honest] /\
   Memory.next_virt_addr{1}.[Malicious] =
   (gm_to_next_virt_addr gm).[Malicious] /\
   Memory.virt_map{1}.[Malicious] = (gm_to_virt_map gm).[Malicious] /\
   (forall (mal_virt_addr : addr),
    mal_virt_addr \in oget (gm_to_virt_map gm).[Malicious] =>
    let phys_addr' =
      oget (oget (gm_to_virt_map gm).[Malicious]).[mal_virt_addr] in
    oget Memory.phys_map{1}.[phys_addr'] <> Key (gm_to_next_key gm))).
call{1} (HonestMemory.party_memory_create_key_phl gm).
call{2} (HonestMemory.party_memory_create_key_phl gm).
auto;
  smt(fmap_eqP mem_fdom fdomP gm_invar_old_virt_addr_does_not_give_new_key).
exlim (glob Memory){1}, key_addr{1}, choice{1} => gm' key_addr' choice'.
call{1} (HonestMemory.party_memory_create_cell_phl gm' key_addr' choice').
call{2} (HonestMemory.party_memory_create_cell_phl gm' key_addr' true).
auto; progress [-delta].
smt(get_setE).
apply
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _ choice{2}
   (oget (gm_to_next_virt_addr gm).[Honest])
   (oget (gm_to_next_virt_addr gm).[Honest] + 1)
   (gm_to_next_phys_addr gm + 1) (gm_to_next_key gm)).
progress;
  smt(get_setE fdom_set fmap_eqP mem_fdom fdomP oget_some some_oget).
wp.
((match => //; first auto; smt(RI_Chooser_WaitChoiceFromAdv));
  first auto; exfalso; smt());
  auto; smt(RI_Chooser_WaitChoiceFromAdv).
call (malicious_party_gm_invar_from_adv Malicious).
auto; smt(RI_Chooser_WaitChoiceFromAdv).
(* ri_chooser_wait_cell_addr_to_other *)
move => choice key_addr cell_addr cell_phys_addr key
        invar_ri_chooser_wait_cell_addr_to_other.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
sp.
match IPS_Chooser_WaitSimGuess {2} 1; first auto; smt().
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Chooser_WaitToOtherCellAddr {1} 1; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_from_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_guess_from_other *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_wait_guess_from_other.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitFromOtherGuess {1} 3; first auto; smt().
match IPS_Chooser_WaitSimGuess {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_from_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_error_to_adv_gm_rel_invar_chooser *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_wait_error_to_adv_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitToAdvError {1} 3; first auto; smt().
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_from_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_final_gm_rel_invar_chooser *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_final_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_Final {1} 3; first auto; smt().
match IPS_Chooser_Final {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_from_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_key_addr_to_other *)
move => choice key_addr guess invar_ri_chooser_wait_key_addr_to_other.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr guess ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitToOtherKeyAddr {1} 3; first auto; smt().
match IPS_Chooser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice key_addr guess) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice key_addr guess) /#.
(* ri_chooser_wait_result_to_adv *)
move => result invar_ri_chooser_wait_result_to_adv.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitToAdvResult {1} 3; first auto; smt().
match IPS_Chooser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result) /#.
(* ri_chooser_wait_error_to_adv *)
move => invar_ri_chooser_wait_error_to_adv.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitToAdvError {1} 3; first auto; smt().
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Chooser_WaitErrorToAdv /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Chooser_WaitErrorToAdv /#.
(* ri_chooser_final *)
move => invar_ri_chooser_final.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_Final {1} 3; first auto; smt().
match IPS_Chooser_Final {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Chooser_Final /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Chooser_Final /#.
(* ri_guesser_wait_guess_from_adv *)
move => invar_ri_guesser_wait_guess_from_adv.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitFromAdvGuess {1} 1; first auto; smt().
match IPS_Guesser_WaitFromAdvGuess {2} 1; first auto; smt().
case (get_as_Guess msg0{1} <> None).
match Guess {1} 1; first auto; smt().
match Guess {2} 1; first auto; smt().
inline Simulator(Malicious).honest_start.
match SHPS_Guesser_WaitFromIPStart {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess{2}) /#.
seq 1 1 : (#pre).
wp.
(match{2}; first 2 auto; smt()); last 4 auto; smt().
exfalso; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitGuessFromAdv _ _ _ _ _) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitGuessFromAdv _ _ _ _ _) /#.
(* ri_guesser_wait_cell_addr_from_other *)
move => guess invar_ri_guesser_wait_cell_addr_from_other.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitFromOtherCellAddr {1} 1; first auto; smt().
match IPS_Guesser_WaitSimChoice {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess) /#.
(* ri_guesser_wait_guess_to_other *)
move =>
  guess cell_addr cell_phys_addr cont result
  invar_ri_guesser_wait_guess_to_other.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitToOtherGuess {1} 1; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 1; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
call
  (malicious_party_gm_invar_guesser_from_adv
   cell_addr cell_phys_addr cont Malicious).

auto; progress [-delta]; first 7 smt().
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
(* ri_guesser_wait_key_addr_from_other *)
move =>
  guess cell_addr cell_phys_addr cont result
  invar_ri_guesser_wait_key_addr_from_other.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitFromOtherKeyAddr {1} 1; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 1; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
call
  (malicious_party_gm_invar_guesser_from_adv
   cell_addr cell_phys_addr cont Malicious).
auto; progress [-delta]; first 7 smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
(* ri_guesser_wait_result_to_adv *)
move => result invar_ri_guesser_wait_result_to_adv.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitToAdvResult {1} 1; first auto; smt().
match IPS_Guesser_WaitToAdvResult {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result) /#.
(* ri_guesser_wait_error_to_adv *)
move => invar_ri_guesser_wait_error_to_adv.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitToAdvError {1} 1; first auto; smt().
match IPS_Guesser_WaitToAdvError {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitErrorToAdv _ _ _ _ _) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitErrorToAdv _ _ _ _ _) /#.
(* ri_guesser_final *)
move => invar_ri_guesser_final.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_Final {1} 1; first auto; smt().
match IPS_Guesser_Final {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_Final _ _ _ _ _) /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_Final _ _ _ _ _) /#.
qed.

lemma to_adv :
  equiv
  [RealProtocol(Honest.Honest, Malicious).to_adv ~
   IdealProtocol(Simulator(Malicious)).to_adv :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2} ==>
   ={res, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2}].
proof.
proc.
exlim Honest.Honest.state{1}, IdealProtocol.state{2},
      Simulator.H.state{2}, (glob Memory){1}, (glob Memory){2} =>
  hon_state ip_state sim_state mem1 mem2.
(* the "!!" is a hack to make the ambient case be a boolean one *)
case @[ambient] (!! rel_invar hon_state ip_state sim_state mem1 mem2) =>
  [/= [] | ?]; last exfalso; smt().
(* ri_chooser_wait_choice_from_adv *)
move => invar_ri_chooser_wait_choice_from_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitFromAdvChoice {1} 2; first auto; smt().
match IPS_Chooser_WaitFromAdvChoice {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Chooser_WaitChoiceFromAdv /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Chooser_WaitChoiceFromAdv /#.
(* ri_chooser_wait_cell_addr_to_other *)
move => choice key_addr cell_addr cell_phys_addr key
        invar_ri_chooser_wait_cell_addr_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
sp.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToOtherCellAddr {1} 2; first auto; smt().
match IPS_Chooser_WaitSimGuess {2} 1; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_to_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_guess_from_other *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_wait_guess_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitFromOtherGuess {1} 2; first auto; smt().
match IPS_Chooser_WaitSimGuess {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_to_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_error_to_adv_gm_rel_invar_chooser *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_wait_error_to_adv_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToAdvError {1} 2; first auto; smt().
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_to_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_final_gm_rel_invar_chooser *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_final_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_Final {1} 2; first auto; smt().
match IPS_Chooser_Final {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
call
  (malicious_party_gm_rel_invar_chooser_to_adv cell_addr cell_phys_addr key
   choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_key_addr_to_other *)
move => choice key_addr guess invar_ri_chooser_wait_key_addr_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_key_addr_to_other
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr guess ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToOtherKeyAddr {1} 2; first auto; smt().
match IPS_Chooser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice key_addr guess) /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice key_addr guess) /#.
(* ri_chooser_wait_result_to_adv *)
move => result invar_ri_chooser_wait_result_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_result_to_adv
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToAdvResult {1} 2; first auto; smt().
match IPS_Chooser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta]; first smt().
rewrite RI_Chooser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result) /#.
(* ri_chooser_wait_error_to_adv *)
move => invar_ri_chooser_wait_error_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToAdvError {1} 2; first auto; smt().
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Chooser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
(* ri_chooser_final *)
move => invar_ri_chooser_final.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_Final {1} 2; first auto; smt().
match IPS_Chooser_Final {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_Final.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Chooser_Final /#.
(* ri_guesser_wait_guess_from_adv *)
move => invar_ri_guesser_wait_guess_from_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitFromAdvGuess {1} 2; first auto; smt().
match IPS_Guesser_WaitFromAdvGuess {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Guesser_WaitGuessFromAdv /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Guesser_WaitGuessFromAdv /#.
(* ri_guesser_wait_cell_addr_from_other *)
move => guess invar_ri_guesser_wait_cell_addr_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitFromOtherCellAddr {1} 2; first auto; smt().
match IPS_Guesser_WaitSimChoice {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess) /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess) /#.
(* ri_guesser_wait_guess_to_other *)
move =>
  guess cell_addr cell_phys_addr cont result
  invar_ri_guesser_wait_guess_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitToOtherGuess {1} 2; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
call
  (malicious_party_gm_invar_guesser_to_adv
   cell_addr cell_phys_addr cont Malicious).
auto; progress [-delta]; first 7 smt().
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
(* ri_guesser_wait_key_addr_from_other *)
move =>
  guess cell_addr cell_phys_addr cont result
  invar_ri_guesser_wait_key_addr_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitFromOtherKeyAddr {1} 2; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
call
  (malicious_party_gm_invar_guesser_to_adv
   cell_addr cell_phys_addr cont Malicious).
auto; progress [-delta]; first 7 smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess cell_addr cell_phys_addr cont result) /#.
(* ri_guesser_wait_result_to_adv *)
move => result invar_ri_guesser_wait_result_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitToAdvResult {1} 2; first auto; smt().
match IPS_Guesser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta]; first smt().
rewrite RI_Guesser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result) /#.
(* ri_guesser_wait_error_to_adv *)
move => invar_ri_guesser_wait_error_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitToAdvError {1} 2; first auto; smt().
match IPS_Guesser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_Final _ _ _ _ _) /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Guesser_WaitErrorToAdv /#.
(* ri_guesser_final *)
move => invar_ri_guesser_final.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_Final {1} 2; first auto; smt().
match IPS_Guesser_Final {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Guesser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Guesser_Final /#.
qed.

lemma queue :
  equiv
  [RealProtocol(Honest.Honest, Malicious).queue ~
   IdealProtocol(Simulator(Malicious)).queue :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2} ==>
   ={glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2}].
proof.
proc.
exlim Honest.Honest.state{1}, IdealProtocol.state{2},
      Simulator.H.state{2}, (glob Memory){1}, (glob Memory){2} =>
  hon_state ip_state sim_state mem1 mem2.
(* the "!!" is a hack to make the ambient case be a boolean one *)
case @[ambient] (!! rel_invar hon_state ip_state sim_state mem1 mem2) =>
  [/= [] | ?]; last exfalso; smt().
(* ri_chooser_wait_choice_from_adv *)
move => invar_ri_chooser_wait_choice_from_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitFromAdvChoice {1} 2; first auto; smt().
match SHPS_Chooser_WaitFromIPStart {2} 3; first auto; smt().
match None {1} 3; first auto; smt().
match None {2} 4; first auto; smt().
match IPS_Chooser_WaitFromAdvChoice {2} 5; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_WaitChoiceFromAdv.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Chooser_WaitChoiceFromAdv /#.
(* ri_chooser_wait_cell_addr_to_other *)
move => choice' key_addr' cell_addr' cell_phys_addr' key'
        invar_ri_chooser_wait_cell_addr_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' cell_addr' cell_phys_addr' key' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitToOtherCellAddr {1} 2; first auto; smt().
match SHPS_Chooser_WaitToOtherCellAddr {2} 3; first auto; smt().
sp.
seq 1 1 :
  (={glob Malicious, trans_addr_opt, cell_addr, key_addr} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   cell_addr' = cell_addr{1} /\ key_addr' = key_addr{1} /\
   choice' = choice{1} /\ gm_invar (glob Memory){1} /\
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' cell_addr' cell_phys_addr' key').
call
  (honest_trans_virt_addr_of_cell_gm_rel_invar_chooser_equiv cell_addr'
   cell_phys_addr' key' choice').
auto; progress [-delta]; smt().
match IPS_Chooser_WaitSimGuess {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice{1} key_addr{2} cell_addr{2} cell_phys_addr' key') /#.
inline Simulator(Malicious).malicious_queue.
wp.
call
  (malicious_party_gm_rel_invar_chooser_to_other cell_addr'
   cell_phys_addr' key' choice' Malicious).
auto; progress [-delta]; first 3 auto; smt().
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
(* ri_chooser_wait_guess_from_other *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_wait_guess_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitFromOtherGuess {1} 2; first auto; smt().
match SHPS_Chooser_WaitFromOtherGuess {2} 3; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
inline Simulator(Malicious).malicious_queue.
wp.
call
  (malicious_party_gm_rel_invar_chooser_to_other cell_addr
   cell_phys_addr key choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_error_to_adv_gm_rel_invar_chooser *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_wait_error_to_adv_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitToAdvError {1} 2; first auto; smt().
match SHPS_Chooser_Final {2} 3; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
inline Simulator(Malicious).malicious_queue.
wp.
call
  (malicious_party_gm_rel_invar_chooser_to_other cell_addr
   cell_phys_addr key choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_final_gm_rel_invar_chooser *)
move =>
  choice key_addr cell_addr cell_phys_addr key
  invar_ri_chooser_final_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice key_addr cell_addr cell_phys_addr key ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_Final {1} 2; first auto; smt().
match SHPS_Chooser_Final {2} 3; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
inline Simulator(Malicious).malicious_queue.
wp.
call
  (malicious_party_gm_rel_invar_chooser_to_other cell_addr
   cell_phys_addr key choice Malicious).
auto; progress [-delta]; first 3 smt().
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice key_addr cell_addr cell_phys_addr key) /#.
(* ri_chooser_wait_key_addr_to_other *)
move => choice' key_addr' guess' invar_ri_chooser_wait_key_addr_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' guess' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitToOtherKeyAddr {1} 2; first auto; smt().
match SHPS_Chooser_WaitToOtherKeyAddr {2} 3; first auto; smt().
sp.
seq 1 1 :
  (={glob Malicious, trans_addr_opt, key_addr} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   key_addr' = key_addr{1} /\ gm_invar (glob Memory){1} /\
   result{1} = (choice' <> guess') /\
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' guess').
call honest_trans_virt_addr_of_cell_gm_invar_chooser_equiv.
auto; smt().
match IPS_Chooser_WaitSimOK {2} 7; first auto; smt().
match SHO_OK {2} 7; first auto.
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result{2}) /#.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
(* ri_chooser_wait_result_to_adv *)
move => result' invar_ri_chooser_wait_result_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitToAdvResult {1} 2; first auto; smt().
match SHPS_Chooser_Final {2} 3; first auto; smt().
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
(* ri_chooser_wait_error_to_adv *)
move => invar_ri_chooser_wait_error_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_WaitToAdvError {1} 2; first auto; smt().
match SHPS_Chooser_Final {2} 3; first auto; smt().
auto; progress [-delta].
rewrite RI_Chooser_WaitErrorToAdv /#.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
(* ri_chooser_final *)
move => invar_ri_chooser_final.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Chooser_Final {1} 2; first auto; smt().
match SHPS_Chooser_Final {2} 3; first auto; smt().
match IPS_Chooser_Final {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_Final.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Chooser_Final /#.
(* ri_guesser_wait_guess_from_adv *)
move => invar_ri_guesser_wait_guess_from_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_WaitFromAdvGuess {1} 2; first auto; smt().
match SHPS_Guesser_WaitFromIPStart {2} 3; first auto; smt().
match IPS_Guesser_WaitFromAdvGuess {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_WaitGuessFromAdv.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Guesser_WaitGuessFromAdv /#.
(* ri_guesser_wait_cell_addr_from_other *)
move => guess' invar_ri_guesser_wait_cell_addr_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_WaitFromOtherCellAddr {1} 2; first auto; smt().
match SHPS_Guesser_WaitFromOtherCellAddr {2} 3; first auto; smt().
match IPS_Guesser_WaitSimChoice {2} 6; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
(* ri_guesser_wait_guess_to_other *)
move =>
  guess' cell_addr' cell_phys_addr' cont' result'
  invar_ri_guesser_wait_guess_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess' cell_addr' cell_phys_addr' cont' result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_WaitToOtherGuess {1} 2; first auto; smt().
match SHPS_Guesser_WaitToOtherGuess {2} 3; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 8; first auto; smt().
auto; progress [-delta]; first smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
inline Simulator(Malicious).malicious_queue.
wp.
call
  (malicious_party_gm_invar_guesser_to_other cell_addr'
   cell_phys_addr' cont' Malicious).
auto; progress [-delta]; first 7 smt().
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
(* ri_guesser_wait_key_addr_from_other *)
move =>
  guess' cell_addr' cell_phys_addr' cont' result'
  invar_ri_guesser_wait_key_addr_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess' cell_addr' cell_phys_addr' cont' result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_WaitFromOtherKeyAddr {1} 2; first auto; smt().
match SHPS_Guesser_WaitFromOtherKeyAddr {2} 3; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
inline Simulator(Malicious).malicious_queue.
wp.
call
  (malicious_party_gm_invar_guesser_to_other cell_addr'
   cell_phys_addr' cont' Malicious).
auto; progress [-delta]; first 7 smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
(* ri_guesser_wait_result_to_adv *)
move => result' invar_ri_guesser_wait_result_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_WaitToAdvResult {1} 2; first auto; smt().
match SHPS_Guesser_Final {2} 3; first auto; smt().
match IPS_Guesser_WaitToAdvResult {2} 6; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
(* ri_guesser_wait_error_to_adv *)
move => invar_ri_guesser_wait_error_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_WaitToAdvError {1} 2; first auto; smt().
match SHPS_Guesser_Final {2} 3; first auto; smt().
match IPS_Guesser_WaitToAdvError {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_WaitErrorToAdv.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Guesser_WaitErrorToAdv /#.
(* ri_guesser_final *)
move => invar_ri_guesser_final.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_other
       Simulator(Malicious).honest_queue
       Simulator(Malicious).H.to_other.
match HPS_Guesser_Final {1} 2; first auto; smt().
match SHPS_Guesser_Final {2} 3; first auto; smt().
match IPS_Guesser_Final {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_Final.
inline Simulator(Malicious).malicious_queue.
wp.
call (malicious_party_gm_invar_to_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite RI_Guesser_Final /#.
qed.

lemma deliver :
  equiv
  [RealProtocol(Honest.Honest, Malicious).deliver ~
   IdealProtocol(Simulator(Malicious)).deliver :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2} ==>
   ={glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2}].
proof.
proc.
exlim Honest.Honest.state{1}, IdealProtocol.state{2},
      Simulator.H.state{2}, (glob Memory){1}, (glob Memory){2} =>
  hon_state ip_state sim_state mem1 mem2.
(* the "!!" is a hack to make the ambient case be a boolean one *)
case @[ambient] (!! rel_invar hon_state ip_state sim_state mem1 mem2) =>
  [/= [] | ?]; last exfalso; smt().
(* ri_chooser_wait_choice_from_adv *)
move => invar_ri_chooser_wait_choice_from_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver.
sp.
match => //.
match IPS_Chooser_WaitFromAdvChoice {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_WaitChoiceFromAdv.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitFromAdvChoice {1} 3; first auto; smt().
match SHPS_Chooser_WaitFromIPStart {2} 4; first auto; smt().
rcondf{1} 4; first auto; smt().
rcondf{2} 5; first auto; smt().
match IPS_Chooser_WaitFromAdvChoice {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_WaitChoiceFromAdv.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
by rewrite RI_Chooser_WaitChoiceFromAdv.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite RI_Chooser_WaitChoiceFromAdv /#.
(* ri_chooser_wait_cell_addr_to_other *)
move => choice' key_addr' cell_addr' cell_phys_addr' key'
        invar_ri_chooser_wait_cell_addr_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' cell_addr' cell_phys_addr' key' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver.
sp.
match => //.
match IPS_Chooser_WaitSimGuess {2} 2; first auto; smt().
match SHO_Nothing {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitToOtherCellAddr {1} 3; first auto; smt().
match SHPS_Chooser_WaitToOtherCellAddr {2} 4; first auto; smt().
rcondf{1} 4; first auto; smt().
rcondf{2} 5; first auto; smt().
match IPS_Chooser_WaitSimGuess {2} 6; first auto; smt().
match SHO_Nothing {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call
  (malicious_party_gm_rel_invar_chooser_from_other cell_addr'
   cell_phys_addr' key' choice' Malicious).
(auto; progress [-delta]; first 3 smt());
  rewrite
    (RI_Chooser_WaitCellAddrToOther _ _ _ _ _
     choice' key_addr' cell_addr' cell_phys_addr' key') /#.
(* ri_chooser_wait_guess_from_other *)
move =>
  choice' key_addr' cell_addr' cell_phys_addr' key'
  invar_ri_chooser_wait_guess_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' cell_addr' cell_phys_addr' key' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_WaitSimGuess {2} 2; first auto; smt().
match SHO_Nothing {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitFromOtherGuess {1} 3; first auto; smt().
match SHPS_Chooser_WaitFromOtherGuess {2} 4; first auto; smt().
sp.
elim* => state_R state_L.
case (get_as_Guess msg{1} <> None).
match Guess {1} 1; first auto; smt().
match Guess {2} 1; first auto; smt().
rcondt{1} 3; first auto; smt().
rcondt{2} 4; first auto; smt().
match IPS_Chooser_WaitSimGuess {2} 6; first auto; smt().
match SHO_Guess {2} 6; first auto; smt().
inline Simulator(Malicious).honest_choice.
match SHPS_Chooser_WaitFromIPChoice {2} 8; first auto; smt().
sp; wp; elim* =>
  to_honest_queue_R sho_r state_R0 sho0R to_honest_queue_L state_L0.
exlim (glob Memory){1} => gm1.
call{2}
  (simulator_modify_cell_gm_rel_invar_chooser gm1 cell_addr' cell_phys_addr'
   key' choice').
auto; progress [-delta].
rewrite /get_as_SHPS_Chooser_WaitFromIPChoice /= /# in H.
smt(). smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice{1} key_addr' guess{2}) /#.
seq 1 1 : (#pre).
auto; smt().
rcondt{1} 2; first auto; smt().
rcondt{2} 2; first auto; smt().
match IPS_Chooser_WaitSimGuess {2} 4; first auto; smt().
match SHO_Error {2} 4; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitGuessFromOther _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call
  (malicious_party_gm_rel_invar_chooser_from_other
   cell_addr' cell_phys_addr' key' choice' Malicious).
(auto; progress [-delta]; first 3 smt());
  rewrite
    (RI_Chooser_WaitGuessFromOther _ _ _ _ _
     choice' key_addr' cell_addr' cell_phys_addr' key') /#.
(* ri_chooser_wait_error_to_adv_gm_rel_invar_chooser *)
move =>
  choice' key_addr' cell_addr' cell_phys_addr' key'
  invar_ri_chooser_wait_error_to_adv_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' cell_addr' cell_phys_addr' key' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitToAdvError {1} 3; first auto; smt().
match SHPS_Chooser_Final {2} 4; first auto; smt().
rcondf{1} 4; first auto; smt().
rcondf{2} 5; first auto; smt().
match IPS_Chooser_WaitToAdvError {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call
  (malicious_party_gm_rel_invar_chooser_from_other
   cell_addr' cell_phys_addr' key' choice' Malicious).
(auto; progress [-delta]; first 3 smt());
  rewrite
    (RI_Chooser_WaitErrorToAdv_GMRelInvarChooser _ _ _ _ _
     choice' key_addr' cell_addr' cell_phys_addr' key') /#.
(* ri_chooser_final_gm_rel_invar_chooser *)
move =>
  choice' key_addr' cell_addr' cell_phys_addr' key'
  invar_ri_chooser_final_gm_rel_invar_chooser.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final_gm_rel_invar_chooser
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' cell_addr' cell_phys_addr' key' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_Final {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_Final {1} 3; first auto; smt().
match SHPS_Chooser_Final {2} 4; first auto; smt().
rcondf{1} 4; first auto; smt().
rcondf{2} 5; first auto; smt().
match IPS_Chooser_Final {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
   choice' key_addr' cell_addr' cell_phys_addr' key') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call
  (malicious_party_gm_rel_invar_chooser_from_other
   cell_addr' cell_phys_addr' key' choice' Malicious).
(auto; progress [-delta]; first 3 smt());
  rewrite
    (RI_Chooser_Final_GMRelInvarChooser _ _ _ _ _
     choice' key_addr' cell_addr' cell_phys_addr' key') /#.
(* ri_chooser_wait_key_addr_to_other *)
move => choice' key_addr' guess' invar_ri_chooser_wait_key_addr_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_key_addr_to_other
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' guess' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitToOtherKeyAddr {1} 3; first auto; smt().
match SHPS_Chooser_WaitToOtherKeyAddr {2} 4; first auto; smt().
rcondf{1} 4; first auto.
rcondf{2} 5; first auto.
match IPS_Chooser_WaitSimOK {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 auto; smt());
  rewrite
    (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
     choice' key_addr' guess') /#.
(* ri_chooser_wait_result_to_adv *)
move => result' invar_ri_chooser_wait_result_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_result_to_adv
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitToAdvResult {1} 3; first auto; smt().
match SHPS_Chooser_Final {2} 4; first auto; smt().
rcondf{1} 4; first auto.
rcondf{2} 5; first auto.
match IPS_Chooser_WaitToAdvResult {2} 6; first auto; smt().
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
auto; progress [-delta]; first 6 auto; smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
(* ri_chooser_wait_error_to_adv *)
move => invar_ri_chooser_wait_error_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_WaitErrorToAdv.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_WaitToAdvError {1} 3; first auto; smt().
match SHPS_Chooser_Final {2} 4; first auto; smt().
rcondf{1} 4; first auto.
rcondf{2} 5; first auto.
match IPS_Chooser_WaitToAdvError {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_WaitErrorToAdv.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
by rewrite RI_Chooser_WaitErrorToAdv.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
auto; progress [-delta]; first 6 smt().
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
(* ri_chooser_final *)
move => invar_ri_chooser_final.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_final Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Chooser_Final {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_Final.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Chooser_Final {1} 3; first auto; smt().
match SHPS_Chooser_Final {2} 4; first auto; smt().
rcondf{1} 4; first auto.
rcondf{2} 5; first auto.
match IPS_Chooser_Final {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Chooser_Final.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
by rewrite RI_Chooser_Final.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite (RI_Chooser_Final _ _ _ _ _) /#.
(* ri_guesser_wait_guess_from_adv *)
move => invar_ri_guesser_wait_guess_from_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_WaitFromAdvGuess {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_WaitGuessFromAdv.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_WaitFromAdvGuess {1} 3; first auto; smt().
match SHPS_Guesser_WaitFromIPStart {2} 4; first auto; smt().
rcondf{1} 4; first auto.
rcondf{2} 5; first auto.
match IPS_Guesser_WaitFromAdvGuess {2} 6; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_WaitGuessFromAdv.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
by rewrite RI_Guesser_WaitGuessFromAdv.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite (RI_Guesser_WaitGuessFromAdv _ _ _ _ _) /#.
(* ri_guesser_wait_cell_addr_from_other *)
move => guess' invar_ri_guesser_wait_cell_addr_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_WaitSimChoice {2} 2; first auto; smt().
auto; progress [-delta].
match SHO_Nothing {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_WaitFromOtherCellAddr {1} 3; first auto; smt().
match SHPS_Guesser_WaitFromOtherCellAddr {2} 4; first auto; smt().
case (get_as_CellAddr msg1 <> None).
match CellAddr {1} 5; first auto; smt().
match CellAddr {2} 7; first auto; smt().
sp; elim* => state_R state_L.
case (cell_addr_good Honest (glob Memory){1} cell_addr{1}).
seq 1 1 :
  (={party, glob Malicious, cell_addr, r} /\ r{1} /\ msgs1 = msgs2 /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   cell_addr_good Honest (glob Memory){1} cell_addr{1} /\
   ri_guesser_wait_cell_addr_from_other
   (Honest.HPS_Guesser_WaitFromOtherCellAddr guess') IdealProtocol.state{2}
   SHPS_Guesser_WaitFromOtherCellAddr
   (glob Memory){1} (glob Memory){2} guess{1} /\
   b0{1} /\
   choice_opt{2} =
   Some ((cell_addr_to_cell Honest (glob Memory){1} cell_addr{1}).`cont)).
exlim (glob Memory){1}, cell_addr{1} => gm cell_addr'.
call (is_cell_read_cell_good gm cell_addr').
auto; smt().
match Some {2} 1; first auto; smt().
rcondt{1} 1; first auto.
rcondt{1} 3; first auto.
rcondt{2} 4; first auto.
match IPS_Guesser_WaitSimChoice {2} 6; first auto; smt().
match SHO_Choice {2} 6; first auto; smt().
inline Simulator(Malicious).honest_guess.
match SHPS_Guesser_WaitFromIPGuess {2} 8; first auto; smt().
auto; progress [-delta].
pose cell := cell_addr_to_cell Honest (glob Memory){1} cell_addr{2}.
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess{1} cell_addr{2}
   (oget (oget Memory.virt_map{1}.[Honest]).[cell_addr{2}])
   cell.`cont (guess{2} = cell.`cont)).
progress; smt(get_some).
seq 1 1 : (#pre /\ ! b0{1} /\ choice_opt{2} = None).
exlim (glob Memory){1}, cell_addr{1} => gm cell_addr'.
call (is_cell_read_cell_bad gm cell_addr').
auto; smt().
rcondf{1} 1; first auto.
match None {2} 1; first auto.
match IPS_Guesser_WaitSimChoice {2} 4; first auto; smt().
match SHO_Error {2} 4; first auto.
auto; progress [-delta].
rewrite RI_Guesser_WaitErrorToAdv /#.
sp 4 6; elim* => state_R state_L.
seq 1 1 : (#pre).
match => //.
move => cell_addr1 cell_addr2.
exfalso; smt().
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
match IPS_Guesser_WaitSimChoice {2} 4; first auto; smt().
match SHO_Error {2} 4; first auto.
auto; progress [-delta].
rewrite RI_Guesser_WaitErrorToAdv /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
(* ri_guesser_wait_guess_to_other *)
move =>
  guess' cell_addr' cell_phys_addr' cont' result'
  invar_ri_guesser_wait_guess_to_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
    guess' cell_addr' cell_phys_addr' cont' result' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_WaitToOtherGuess {1} 3; first auto; smt().
match SHPS_Guesser_WaitToOtherGuess {2} 4; first auto; smt().
rcondf{1} 4; first auto.
rcondf{2} 5; first auto.
match IPS_Guesser_WaitSimOK {2} 6; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call
  (malicious_party_gm_invar_guesser_from_other
   cell_addr' cell_phys_addr' cont' Malicious).
(auto; progress [-delta]; first 7 smt());
  rewrite
    (RI_Guesser_WaitGuessToOther _ _ _ _ _
     guess' cell_addr' cell_phys_addr' cont' result') /#.
(* ri_guesser_wait_key_addr_from_other *)
move =>
  guess' cell_addr' cell_phys_addr' cont' result'
  invar_ri_guesser_wait_key_addr_from_other.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
    guess' cell_addr' cell_phys_addr' cont' result' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_WaitFromOtherKeyAddr {1} 3; first auto; smt().
match SHPS_Guesser_WaitFromOtherKeyAddr {2} 4; first auto; smt().
sp 4 6; elim* => state_r state_L.
case (get_as_KeyAddr msg{1} <> None).
match KeyAddr {1} 1; first auto; smt().
match KeyAddr {2} 1; first auto; smt().
seq 1 1 :
  (={glob Malicious, glob Memory, unlocked_cell_addr_opt, r} /\
   gm_invar (glob Memory){1} /\ msg1 = msg2 /\ msgs1 = msgs2 /\
   RealProtocol.to_honest_queue{1} = msg1 :: msgs1 /\
   Simulator.to_honest_queue{2} = msg2 :: msgs2 /\
   ={to_malicious_queue}(RealProtocol, Simulator) /\
   r{1} /\ sho0{2} = SHO_Error /\ guess{1} = guess' /\
   Honest.Honest.state{1} = Honest.HPS_Guesser_WaitToAdvError /\
   Simulator.H.state{2} = SHPS_Guesser_Final /\
   IdealProtocol.state{2} = IPS_Guesser_WaitSimOK result' /\
   result' = (guess' = cont') /\
   (unlocked_cell_addr_opt{1} <> None =>
    (exists (phys_addr : addr, cell : cell),
     (oget (gm_to_virt_map (glob Memory){1}).[Honest])
        .[oget unlocked_cell_addr_opt{1}] = Some phys_addr /\
    (gm_to_phys_map (glob Memory){1}).[phys_addr] = Some (Cell cell) /\
    cell.`cont = cont' /\ cell.`locked = false))).
call
  (real_simulator_unlock_cell_gm_invar_guesser
   cell_addr' cell_phys_addr' cont').
auto; smt().
case (unlocked_cell_addr_opt{1} = None).
match None {1} 1; first auto.
match None {2} 1; first auto.
match IPS_Guesser_WaitSimOK {2} 4; first auto; smt().
match SHO_Error {2} 4; first auto.
auto; progress [-delta]; last smt().
rewrite RI_Guesser_WaitErrorToAdv /#.
match Some {1} 1; first auto; smt().
match Some {2} 1; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 6; first auto; smt().
match SHO_OK {2} 6; first auto; smt().
wp; exlim (glob Memory){1}, unlocked_cell_addr{1} => gm unlocked_cell_addr'.
call{1}
  (_ :
   cell_addr = unlocked_cell_addr' /\
   glob Memory = gm /\ gm_invar gm /\
   cell_addr_good Honest gm cell_addr /\
   good_cell_addr_unlocked Honest gm cell_addr ==>
   glob Memory = gm /\ gm_invar (glob Memory) /\
   (let cell = cell_addr_to_cell Honest gm unlocked_cell_addr' in
    res = Some cell.`cont)).
conseq (_ : true ==> true) (_ : _ ==> _) => //.
conseq (HonestMemory.party_memory_contents_cell gm unlocked_cell_addr').
apply HonestMemory.party_memory_contents_cell_ll.
(auto; progress [-delta]; first 2 smt());
  rewrite
    (RI_Guesser_WaitResultToAdv _ _ _ _ _ (guess{1} = cell.`cont)) /#.
seq 1 1 : (#pre).
match => //.
move => key_addr1 key_addr2.
exfalso; smt().
match IPS_Guesser_WaitSimOK {2} 4; first auto; smt().
match SHO_Error {2} 4; first auto.
auto; progress [-delta].
rewrite RI_Guesser_WaitErrorToAdv /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call
  (malicious_party_gm_invar_guesser_from_other
   cell_addr' cell_phys_addr' cont' Malicious).
(auto; progress [-delta]; first 7 smt());
  rewrite
    (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
     guess' cell_addr' cell_phys_addr' cont' result') /#.
(* ri_guesser_wait_result_to_adv *)
move => result' invar_ri_guesser_wait_result_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_WaitToAdvResult {1} 3; first auto; smt().
match SHPS_Guesser_Final {2} 4; first auto; smt().
match IPS_Guesser_WaitToAdvResult {2} 7; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
(* ri_guesser_wait_error_to_adv *)
move => invar_ri_guesser_wait_error_to_adv.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_WaitErrorToAdv.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_WaitToAdvError {1} 3; first auto; smt().
match SHPS_Guesser_Final {2} 4; first auto; smt().
match IPS_Guesser_WaitToAdvError {2} 7; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_WaitErrorToAdv.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
by rewrite RI_Guesser_WaitErrorToAdv.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite (RI_Guesser_WaitErrorToAdv _ _ _ _ _) /#.
(* ri_guesser_final *)
move => invar_ri_guesser_final.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
match => //.
inline Simulator(Malicious).honest_deliver; sp.
match => //.
match IPS_Guesser_Final {2} 2; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_Final.
move => msg1 msgs1 msg2 msgs2.
inline RealProtocol(Honest.Honest, Malicious).H.from_other
       Simulator(Malicious).H.from_other.
match HPS_Guesser_Final {1} 3; first auto; smt().
match SHPS_Guesser_Final {2} 4; first auto; smt().
match IPS_Guesser_Final {2} 7; first auto; smt().
auto; progress [-delta].
by rewrite RI_Guesser_Final.
inline Simulator(Malicious).malicious_deliver.
match => //.
auto; progress [-delta].
by rewrite RI_Guesser_Final.
move => msg1 msgs1 msg2 msgs2.
wp.
call (malicious_party_gm_invar_from_other Malicious).
(auto; progress [-delta]; first 6 smt());
  rewrite (RI_Guesser_Final _ _ _ _ _) /#.
qed.

lemma Sec
      (Adv <:
         ADV
         {-RealProtocol, -Honest.Honest, -Malicious,
          -IdealProtocol, -Simulator})
      &m :
  Pr[RealExper(Malicious, Adv).main() @ &m : res] =
  Pr[IdealExper(Malicious, Adv).main() @ &m : res].
proof.
byequiv => //.
proc.
seq 1 1 : (={glob Adv, glob Malicious, chooser});
  first call (_ : true); auto.
seq 1 1 :
  (={glob Adv, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2}).
inline RealProtocol(Honest.Honest, Malicious).init
       IdealProtocol(Simulator(Malicious)).init
       Simulator(Malicious).init.
swap{2} 6 1.
call (_ : true ==> ={glob Memory} /\ gm_invar (glob Memory){1}).
conseq
  (_ : true ==> ={glob Memory})
  (_ : true ==> gm_invar (glob Memory))
  (_ : true ==> true) => //.
by conseq memory_init.
sim.
sp.
match => //; wp.
call (_ : true).
inline*; auto; progress [-delta].
by apply RI_Chooser_WaitChoiceFromAdv.
wp.
call (_ : true).
inline*; auto; progress [-delta].
by apply RI_Guesser_WaitGuessFromAdv.
call
  (_ :
   ={glob Malicious} /\
   RealProtocol.to_malicious_queue{1} = Simulator.to_malicious_queue{2} /\
   RealProtocol.to_honest_queue{1} = Simulator.to_honest_queue{2} /\
   rel_invar Honest.Honest.state{1} IdealProtocol.state{2}
   Simulator.H.state{2} (glob Memory){1} (glob Memory){2}).
by conseq from_adv.
by conseq to_adv.
by conseq queue.
by conseq deliver.
auto.
qed.

end section.

(* we have perfect security: the probability that Adv returns true in
   the real experiment is exactly the same as the probability it
   returns true in the ideal experiment

   assuming we resrict ourselves to Malicious and Adv being
   non-probabilistic, we can conclude that the real experiment results
   in true iff the ideal experiment does *)

lemma Security
      (Malicious <:
         PARTY{-RealProtocol, -Honest.Honest, -IdealProtocol, -Simulator})
      (Adv <:
         ADV
         {-RealProtocol, -Honest.Honest, -Malicious,
          -IdealProtocol, -Simulator})
      &m :
  Pr[RealExper(Malicious, Adv).main() @ &m : res] =
  Pr[IdealExper(Malicious, Adv).main() @ &m : res].
proof.
apply (Sec Malicious Adv).
qed.
