(* Guessing Game Protocols, Adversaries, Experiments, Real Protocol
   and Honest Party

   We have a type of protocol messages, a module type of protocols,
   and a module type of adversaries, which are paramterized by
   (interact with) protocols.

   A protocol has an initialization procedure (which an adversary
   cannot call), plus four procedures that may be called by an
   adversary:

     * one for trying to send a message to a party of the protocol
       (the party may refuse it)

     * one for asking the party for a message to the adversary (the
       party may not be ready to send such a message)

     * one for allowing a party to enqueue a message intended for the
       other party (it may not be ready to send such a message)

     * one for allowing a party to receive a message previously queued
       by the other party (it may not be ready to receive such a
       message)

   An adversary has a procedure for choosing which of the protocol
   parties will be the chooser (with the other party being the
   guesser). It also has a `distinguish` procedure, which after
   interacting with the protocol as long as it likes, returns
   a boolean judgment. It is thus both playing the roles of the
   clients of both protocol parties and issuing a boolean judgment.

   An experiment is parameterized by a protocol and an adversary.  Its
   `main` procedure asks the adversary to choose which party is the
   chooser, initializes the protocol (telling it which party is the
   chooser), and finally calls the adversary's `distinguish`
   procedure, returning whatever boolean it returns.

   A protocol party is parameterized by a protocol memory, its view to
   the physical and party-indexed virtual memories (see Memory). Its
   initialization procedure takes in a boolean indication of whether
   the party is the chooser. And it has procedures for optionally
   accepting a message from the adversary, optionally sending a
   message to the adversary, optionally accepting a message from the
   other party, and optionally sending a message to the other party.

   The real protocol is parameterized by an honest and a (potentially)
   malicious party, each of which is given access to its party
   memory. Its initialization procedure sets the message queues (one
   for messages from honest party to malicious party, and one for
   messages from malicious party to honest party) to be empty, tells
   the two parties their roles, and initializes the memory. Its
   remaining four procedures allow an adversary to interact with the
   honest and malicous parties.
   
   Finally, there is the definition of the honest party, packaged
   as a theory, allowing cloning, for use in the correctness proof.
   Here is how the honest party works:

   When the honest party is the chooser, it learns its choice from the
   adversary. Using its view of the memory, it creates a locked cell
   with a fresh key and whose boolean contents is its choice, and
   translates its virtual address to this cell into a virtual address
   of the malicious party, sending this virtual address to the
   malicous party. It has thus committed to its choice. Once the
   malicious party communicates its guess (normally dictated to it by
   the adversary) to the honest party, the honest party translates its
   virtual address to the cell's key into a virtual address of the
   malicious party, and sends this virtual address to the malicious
   party, allowing it to unlock the cell, producing a new unlocked
   cell with the same contents. It can then learn the honest party's
   choice, and learn whether it has won or lost. The honest party then
   communicates its won/lost result to the adversary.

   When the honest party is the guesser, it learns its guess from the
   adversary. It then expects to receive the virtual address of a cell
   from the malicious party. This cell contains the malicous party's
   choice (possibly dictated to it by the adversary).  Once it
   receives this address, it sends its guess to the malicious party,
   expecting the malicious party to respond with the virtual address
   of the cell's key. If this happens, the honest party is able to
   unlock the cell, producing a new, unlocked cell, which it can then
   read the contents of, recovering the malicious party's choice. The
   honest party can then communicate its won/lost result to the
   adversary.

   When the malicious party does not follow the above expected
   protocol, instead of sending a won/lost result to the adversary,
   the honest party instead sends an error indication.

   By letting the adversary pick the inputs to both parties, and
   consume both of their outputs, we are modeling the idea that the
   client of one of the parties may have some knowledge of what the
   other party's client will choose or guess, or may have some
   influence on behavior of the other party's client. *)

prover ["Z3" "Alt-Ergo"].  (* both must succeed for all smt goals *)

require import AllCore List FMap FSet.

(* physical and party-indexed virtual memories *)

require import Memory.

(* protocol messages *)

type msg = [
  | Result   of bool  (* did sending party win (true) or lose (false)? *)
  | Choice   of bool  (* a choice *)
  | Guess    of bool  (* a guess *)
  | CellAddr of addr  (* the virtual address of a cell *)
  | KeyAddr  of addr  (* the virtual address of a key *)
  | Error             (* an error has occurred *)
  | Int      of int   (* for other adversary/malicious party
                         communication *)
].

(* two-party protocols

   except for init, these procedures are called by the adversary,
   specifying which party it relates to

   in addition to the indicated action, they let the party make whatever
   internal progress it wants

   in practice, protocol parties communicate partly using memories *)

module type PROTOCOL = {
  (* initialize the protocol, saying which party will be the choooser
     (the other party is then the guesser)  *)

  proc init(chooser : party) : unit

  (* ask the party to accept a message from the adversary; the boolean
     says whether it was accepted *)

  proc from_adv(party : party, msg : msg) : bool

  (* ask the party if it wants to send a message to the adversary;
     if None is returned, that means there is no message *)

  proc to_adv(party : party) : msg option

  (* allow the party to optionally enqueue a message intended for the
     other party; the adversary can't tell if this happened *)

  proc queue(party : party) : unit

  (* allow the party to optionally dequeue a message queued for it;
     the adversary can't tell if this happened *)

  proc deliver(party : party) : unit
}.

(* an adversary is parameterized by a protocol

   the protocol may use the memory, but the adversary has no direct
   access to the memory (in the security proof, this is enforced by
   module restrictions)

   the adversary is the distinguisher, but also plays the roles
   of the clients of both the honest and malicious parties *)

module type ADV (Proto : PROTOCOL) = {
  (* initialization and select the party that will be the chooser,
     with the other party being the guesser; this must be done without
     interacting with the protocol *)

  proc chooser() : party { }

  (* experiment with the protocol, returning a boolean judgement;
     may not initialize the protocl *)

  proc distinguish() : bool
         {Proto.from_adv, Proto.to_adv, Proto.queue, Proto.deliver}
}.

(* an experiment, connecting a protocol and adversary, and eventually
   returning the adversary's boolean judgement *)

module Exper (Prot : PROTOCOL, Adv : ADV) = {
  (* connect the protocol to the adversary *)
  module A = Adv(Prot)

  proc main() : bool = {
    var b : bool; var chooser : party;
    (* let the adversary pick who the chooser is *)
    chooser <@ A.chooser();
    (* initialize the protocol, setting who the chooser is *)
    Prot.init(chooser);
    (* let the adversary experiment with protocol, terminating
       with a boolean judgement, which is then returned as
       the result of the experiement *)
    b <@ A.distinguish();
    return b;
  }
}.

(* a party is parameterized by its interface to the memory; module
   restrictions are used in the proof to enforce that it only
   accesses the memory in this way *)

module type PARTY (PM : PARTY_MEMORY) = {
  (* initialization, saying whether the party is the chooser *)

  proc init(chooser : bool) : unit { }  (* can't use PM *)

  (* optionally accept a message from the adversary; boolean says
     whether the message was accepted *)

  proc from_adv(msg : msg) : bool

  (* optionally send a message to the adversary; None means no message *)

  proc to_adv() : msg option

  (* optionally accept a message from the other party; boolean says
     whether message was accepted *)

  proc from_other(msg : msg) : bool

  (* optionally send a message to the other party; None means no message
     was produced *)

  proc to_other() : msg option
}.

(* the real protocol, parameterized by honest and malicious parties

   the second party doesn't have to behave maliciously, though;
   we can instantiate it with a clone of the honest party *)

module RealProtocol (Honest : PARTY, Malicious : PARTY) : PROTOCOL = {
  (* make the honest party's memory from the real memory *)

  (* connect the honest and malicious parties with their interfaces
     to the memory *)

  module H = Honest(HonestMemory.PartyMemory)        (* honest *)
  module M = Malicious(MaliciousMemory.PartyMemory)  (* malicious *)

  (* message queues represented as lists; where new messages are added
     at end

     to_malicious_queue has messages intended for malicious party;
     to_honest_queue has messages intended for honest party *)

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
    Memory.init();  (* M and H can't use memory *)
  }

  proc from_adv(party : party, msg : msg) : bool = {
    var b : bool;
    match party with
    | Honest    => { b <@ H.from_adv(msg); }
    | Malicious => { b <@ M.from_adv(msg); }
    end;
    return b;
  }

  proc to_adv(party : party) : msg option = {
    var msg_opt : msg option;
    match party with
    | Honest    => { msg_opt <@ H.to_adv(); }
    | Malicious => { msg_opt <@ M.to_adv(); }
    end;
    return msg_opt;
  }

  proc queue(party : party) : unit = {
    var msg_opt : msg option;
    match party with
    | Honest    => {
        msg_opt <@ H.to_other();
        match msg_opt with
        | None     => { }
        | Some msg => {
            to_malicious_queue <- to_malicious_queue ++ [msg];
          }
        end;
      }
    | Malicious => {
        msg_opt <@ M.to_other();
        match msg_opt with
        | None     => { }
        | Some msg => {
            to_honest_queue <- to_honest_queue ++ [msg];
          }
        end;
      }
    end;
  }

  proc deliver(party : party) : unit = {
    var b : bool;
    match party with
    | Honest    => {
        match to_honest_queue with
        | []          => { }
        | msg :: msgs => {
            b <@ H.from_other(msg);
            if (b) { to_honest_queue <- msgs; }
          }
        end;
      }
    | Malicious => {
        match to_malicious_queue with
        | []          => { }
        | msg :: msgs => {
            b <@ M.from_other(msg);
            if (b) { to_malicious_queue <- msgs; }
          }
        end;
      }
    end;
  }
}.

(* the honest party *)

theory Honest.

(* the state of the honest party

   results are from the point of view of the honest party:
   true = won, false = lost *)

type honest_party_state = [
  (* chooser *)
  | HPS_Chooser_WaitFromAdvChoice
  | HPS_Chooser_WaitToOtherCellAddr   of bool  (* choice *)
                                       & addr  (* key addr *)
                                       & addr  (* cell addr *)
  | HPS_Chooser_WaitFromOtherGuess    of bool  (* choice *)
                                       & addr  (* key addr *)
  | HPS_Chooser_WaitToOtherKeyAddr    of bool  (* result *)
                                       & addr  (* key addr *)
  | HPS_Chooser_WaitToAdvResult       of bool  (* result *)
  | HPS_Chooser_WaitToAdvError
  | HPS_Chooser_Final
  (* guesser *)
  | HPS_Guesser_WaitFromAdvGuess
  | HPS_Guesser_WaitFromOtherCellAddr of bool  (* guess *)
  | HPS_Guesser_WaitToOtherGuess      of bool  (* guess *)
                                       & addr  (* cell addr *)
  | HPS_Guesser_WaitFromOtherKeyAddr  of bool  (* guess *)
                                       & addr  (* cell addr *)
  | HPS_Guesser_WaitToAdvResult       of bool
  | HPS_Guesser_WaitToAdvError
  | HPS_Guesser_Final
].

(* honest party *)

module (Honest : PARTY) (PM : PARTY_MEMORY) = {
  var state : honest_party_state

  proc init(chooser : bool) : unit = {
    state <-
      if chooser
      then HPS_Chooser_WaitFromAdvChoice
      else HPS_Guesser_WaitFromAdvGuess;
  }

  proc from_adv(msg : msg) : bool = {
    var r : bool <- false;  (* default is to reject *)
    var key_addr; var cell_addr : addr; var cell_addr_opt : addr option;
    match state with
    | HPS_Chooser_WaitFromAdvChoice         => {
        match msg with
        | Result _      => { }
        | Choice choice => {
            key_addr <@ PM.create_key();
            cell_addr_opt <@ PM.create_cell(key_addr, choice);
            cell_addr <- oget cell_addr_opt;
            state <-
              HPS_Chooser_WaitToOtherCellAddr choice key_addr cell_addr;
            r <- true;
          }
        | Guess _       => { }
        | CellAddr _    => { }
        | KeyAddr  _    => { }
        | Error         => { }
        | Int _         => { }
        end;
      }
    | HPS_Chooser_WaitToOtherCellAddr _ _ _ => { }
    | HPS_Chooser_WaitFromOtherGuess _ _    => { }
    | HPS_Chooser_WaitToOtherKeyAddr _ _    => { }
    | HPS_Chooser_WaitToAdvResult _         => { }
    | HPS_Chooser_WaitToAdvError            => { }
    | HPS_Chooser_Final                     => { }
    | HPS_Guesser_WaitFromAdvGuess          => {
        match msg with
        | Result _    => { }
        | Choice _    => { }
        | Guess guess => {
            state <- HPS_Guesser_WaitFromOtherCellAddr guess;
            r <- true;
          }
        | CellAddr _  => { }
        | KeyAddr  _  => { }
        | Error       => { }
        | Int _       => { }
        end;
      }
    | HPS_Guesser_WaitFromOtherCellAddr _   => { }
    | HPS_Guesser_WaitToOtherGuess _ _      => { }
    | HPS_Guesser_WaitFromOtherKeyAddr _ _  => { }
    | HPS_Guesser_WaitToAdvResult _         => { }
    | HPS_Guesser_WaitToAdvError            => { }
    | HPS_Guesser_Final                     => { }
    end;
    return r;
  }

  proc to_adv() : msg option = {
    var r : msg option <- None;  (* default is no message *)
    match state with
    | HPS_Chooser_WaitFromAdvChoice         => { }
    | HPS_Chooser_WaitToOtherCellAddr _ _ _ => { }
    | HPS_Chooser_WaitFromOtherGuess _ _    => { }
    | HPS_Chooser_WaitToOtherKeyAddr _ _    => { }
    | HPS_Chooser_WaitToAdvResult result    => {
        r <- Some (Result result); state <- HPS_Chooser_Final;
      }
    | HPS_Chooser_WaitToAdvError            => {
        r <- Some Error; state <- HPS_Chooser_Final;
      }
    | HPS_Chooser_Final                     => { }
    | HPS_Guesser_WaitFromAdvGuess          => { }
    | HPS_Guesser_WaitFromOtherCellAddr _   => { }
    | HPS_Guesser_WaitToOtherGuess _ _      => { }
    | HPS_Guesser_WaitFromOtherKeyAddr _ _  => { }
    | HPS_Guesser_WaitToAdvResult result    => {
        r <- Some (Result result); state <- HPS_Guesser_Final;
      }
    | HPS_Guesser_WaitToAdvError            => {
        r <- Some Error; state <- HPS_Guesser_Final;
      }
    | HPS_Guesser_Final                     => { }
    end;
    return r;
  }

  proc from_other(msg : msg) : bool = {
    var r : bool <- false;  (* default is reject *)
    var b : bool; var b_opt : bool option;
    var unlocked_cell_addr_opt : addr option;
    match state with
    | HPS_Chooser_WaitFromAdvChoice                    => { }
    | HPS_Chooser_WaitToOtherCellAddr _ _ _            => { }
    | HPS_Chooser_WaitFromOtherGuess choice key_addr   => {
        (* default is accept, but consider error *)
        r <- true; state <- HPS_Chooser_WaitToAdvError;
        match msg with
        | Result _    => { }
        | Choice _    => { }
        | Guess guess => {
            (* if the guesser's guess is not equal to choice, the
               choosing party wins *)
            state <-
              HPS_Chooser_WaitToOtherKeyAddr (guess <> choice) key_addr;
          }
        | CellAddr _  => { }
        | KeyAddr  _  => { }
        | Error       => { }
        | Int _       => { }
        end;
      }
    | HPS_Chooser_WaitToOtherKeyAddr _ _               => { }
    | HPS_Chooser_WaitToAdvResult _                    => { }
    | HPS_Chooser_WaitToAdvError                       => { }
    | HPS_Chooser_Final                                => { }
    | HPS_Guesser_WaitFromAdvGuess                     => { }
    | HPS_Guesser_WaitFromOtherCellAddr guess          => {
        r <- true; state <- HPS_Guesser_WaitToAdvError;
        match msg with
        | Result _            => { }
        | Choice _            => { }
        | Guess _             => { }
        | CellAddr cell_addr  => {
            b <@ PM.is_cell(cell_addr);
            if (b) {
              state <- HPS_Guesser_WaitToOtherGuess guess cell_addr;
            }
          }
        | KeyAddr  _          => { }
        | Error               => { }
        | Int _               => { }
        end;
      }
    | HPS_Guesser_WaitToOtherGuess _ _                 => { }
    | HPS_Guesser_WaitFromOtherKeyAddr guess cell_addr => {
        r <- true; state <- HPS_Guesser_WaitToAdvError;
        match msg with
        | Result _         => { }
        | Choice _         => { }
        | Guess _          => { }
        | CellAddr _       => { }
        | KeyAddr key_addr => {
            unlocked_cell_addr_opt <@ PM.unlock_cell(cell_addr, key_addr);
            match unlocked_cell_addr_opt with
            | None                    => { }
            | Some unlocked_cell_addr => {
                b_opt <@ PM.contents_cell(unlocked_cell_addr);
                (* if guess is equal to the choosing party's choice,
                   the guesser wins *)
                state <- HPS_Guesser_WaitToAdvResult (guess = oget b_opt);
              }
            end;
          }
        | Error            => { }
        | Int _            => { }
        end;
      }
    | HPS_Guesser_WaitToAdvResult _                    => { }
    | HPS_Guesser_WaitToAdvError                       => { }
    | HPS_Guesser_Final                                => { }
    end;
    return r;
  }

  proc to_other() : msg option = {
    var r : msg option <- None;  (* default is no message *)
    var trans_addr_opt : addr option;
    match state with
    | HPS_Chooser_WaitFromAdvChoice                             => { }
    | HPS_Chooser_WaitToOtherCellAddr choice key_addr cell_addr => {
        trans_addr_opt <@ PM.trans_virt_addr(cell_addr);
        r <- Some (CellAddr (oget trans_addr_opt));
        state <- HPS_Chooser_WaitFromOtherGuess choice key_addr;
      }
    | HPS_Chooser_WaitFromOtherGuess _ _                        => { }
    | HPS_Chooser_WaitToOtherKeyAddr result key_addr            => {
        trans_addr_opt <@ PM.trans_virt_addr(key_addr);
        r <- Some (KeyAddr (oget trans_addr_opt));
        state <- HPS_Chooser_WaitToAdvResult result;
      }
    | HPS_Chooser_WaitToAdvResult _                             => { }
    | HPS_Chooser_WaitToAdvError                                => { }
    | HPS_Chooser_Final                                         => { }
    | HPS_Guesser_WaitFromAdvGuess                              => { }
    | HPS_Guesser_WaitFromOtherCellAddr _                       => { }
    | HPS_Guesser_WaitToOtherGuess guess cell_addr              => {
        r <- Some (Guess guess);
        state <- HPS_Guesser_WaitFromOtherKeyAddr guess cell_addr;
      }
    | HPS_Guesser_WaitFromOtherKeyAddr _ _                      => { }
    | HPS_Guesser_WaitToAdvResult _                             => { }
    | HPS_Guesser_WaitToAdvError                                => { }
    | HPS_Guesser_Final                                         => { }
    end;
    return r;
  }
}.

end Honest.
