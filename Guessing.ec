(* Boolean Guessing Game Security, Expressed in a Real/ideal Style

   We have a two-party protocol, where each party is assigned to be
   either the chooser or guesser of a boolean. The guesser wins
   when it guesses correctly; the chooser wins with the guesser
   is incorrect.

   In the real protocol, the parties communicate via messages, and
   also rely on trusted infrastructure, involving a physical memory
   storing immutable objects, where each party has a virtual memory
   giving them access to certain physical addresses.

   As usual, the ideal protocol is secure by construction, and
   security means that an adversary is unable to distinguish
   the real and ideal games. Thus we can conclude that the real
   protocol is secure as well. *)

prover ["Z3" "Alt-Ergo"].  (* both must succeed for all smt goals *)
timeout 2.  (* can be increased *)

require import AllCore List FMap FSet.

(* party names

   the malicious party isn't necessarily dishonest *)

type party = [
  | Honest
  | Malicious
].

op other (pty : party) : party =
  match pty with
  | Honest    => Malicious
  | Malicious => Honest
  end.

(* physical and virtual memories, indexed by addresses

   immutable objects (keys and cells) are stored in the physical
   memory

   each of the honest and malicious parties has a virtual
   memory mapping virtual addresses to physical ones

   there is a way for a party to translate one of its virtual
   addresses into a virtual address of the other party, which is
   added to the other party's virtual address table, and points to
   the same physical address

   operations are non-destructive, and so create new objects

   keys are represented as unique integers

   cells are records consisting of a key (needed to unlock it),
   a boolean contents and a locked status

   unlocking creates a new, unlocked cell; the contents of
   an unlocked cell can be retieved without a key *)

type addr = int.

module type MEMORY = {
  (* initialize the memory: no objects and no virtual or physical
     addresses *)

  proc init() : unit

  (* if addr is a virtual address for party pty, return Some of a new
     virtual address for the other party that points to the same
     physical address; otherwise, return None *)

  proc trans_virt_addr(pty : party, addr : addr) : addr option

  (* create a new object Key key, where key is different from all
     previously allocated keys, returning a virtual address for party
     pty that points to the physical address of that key *)

  proc create_key(pty : party) : addr

  (* test whether key_addr is a virtual address for party pty
     that points to the physical address of a key object *)

  proc is_key(pty : party, key_addr : addr) : bool

  (* if key_addr is a virtual address for party pty pointing to a
     physical address of object Key key, create a new locked cell with
     contents b and key key, and return Some of a virtual address for
     pty pointing to the physical address of that cell; otherwise,
     return None *)

  proc create_cell(pty : party, key_addr : addr, b : bool) : addr option

  (* test whether cell_addr is a virtual address for party pty
     that points to the physical address of a cell *)

  proc is_cell(pty : party, cell_addr : addr) : bool

  (* if cell_addr and key_addr are virtual addresses for party pty
     pointing to physical addresses pointing to objects
     Cell cell and Key key, and where the key of cell is key,
     then allocate a new unlocked cell that is otherwise identical
     to cell, and return Some of a virtual address for pty
     that points to the physical address of that new cell *)

  proc unlock_cell(pty : party, cell_addr : addr, key_addr : addr)
         : addr option

  (* if cell_addr is a virtual address for pty that points to
     a physical address of an unlocked cell object, return Some of
     the cell's contents; otherwise return None *)

  proc contents_cell(pty : party, cell_addr : addr) : bool option
}.

type key = int.

type cell = {
  key    : key;
  cont   : bool;  (* contents *)
  locked : bool
}.

type object = [
  | Key  of key
  | Cell of cell
].

op is_key (o : object) : bool =
  match o with
  | Key _  => true
  | Cell _ => false
  end.

lemma is_key (o : object) :
  is_key o => exists (k : key), o = Key k.
proof.
case o => [k _ | //]; by exists k.
qed.

op is_cell (o : object) : bool =
  match o with
  | Key _  => false
  | Cell _ => true
  end.

lemma is_cell (o : object) :
  is_cell o => exists (c : cell), o = Cell c.
proof.
case o => [// | c _]; by exists c.
qed.

module Memory : MEMORY = {
  var next_key : key

  var next_phys_addr : addr
  var phys_map : (addr, object) fmap

  var honest_next_virt_addr : addr
  var honest_virt_map    : (addr, addr) fmap

  var malicious_next_virt_addr : addr
  var malicious_virt_map : (addr, addr) fmap  

  proc init() : unit = {
    next_key                 <- 0;
    next_phys_addr           <- 0;
    phys_map                 <- empty;
    honest_next_virt_addr    <- 0;
    honest_virt_map          <- empty;
    malicious_next_virt_addr <- 0;
    malicious_virt_map       <- empty;
  }

  proc phys_alloc(obj : object) : addr = {
    var r : addr;
    phys_map.[next_phys_addr] <- obj;
    r <- next_phys_addr;
    next_phys_addr <- next_phys_addr + 1;
    return r;
  }

  proc honest_virt_alloc(phys_addr : addr) : addr = {
    var r : addr;
    honest_virt_map.[honest_next_virt_addr] <- phys_addr;
    r <- honest_next_virt_addr;
    honest_next_virt_addr <- honest_next_virt_addr + 1;
    return r;
  }

  proc malicious_virt_alloc(phys_addr : addr) : addr = {
    var r : addr;
    malicious_virt_map.[malicious_next_virt_addr] <- phys_addr;
    r <- malicious_next_virt_addr;
    malicious_next_virt_addr <- malicious_next_virt_addr + 1;
    return r;
  }

  proc trans_virt_addr(pty : party, addr : addr) : addr option = {
    var r : addr option;
    var phys_addr, other_virt_addr : addr;
    if (pty = Honest) {
      if (addr \in honest_virt_map) {
        phys_addr <- oget honest_virt_map.[addr];
        other_virt_addr <@ malicious_virt_alloc(phys_addr);
        r <- Some other_virt_addr;
      }
      else { r <- None; }
    }
    else {
      if (addr \in malicious_virt_map) {
        phys_addr <- oget malicious_virt_map.[addr];
        other_virt_addr <@ honest_virt_alloc(phys_addr);
        r <- Some other_virt_addr;
      }
      else { r <- None; }
    }
    return r;
  }

  proc create_key(pty : party) : addr = {
    var key : key <- next_key;
    var phys_addr, virt_addr : addr;
    next_key <- next_key + 1;
    phys_addr <@ phys_alloc(Key key);
    if (pty = Honest) {
      virt_addr <@ honest_virt_alloc(phys_addr);
    }
    else {
      virt_addr <@ malicious_virt_alloc(phys_addr);
    }
    return virt_addr;
  }

  proc is_key(pty : party, key_addr : addr) : bool = {
    var r : bool;
    if (pty = Honest) {
      if (key_addr \in honest_virt_map) {
        r <- is_key (oget phys_map.[oget honest_virt_map.[key_addr]]);
      }
      else { r <- false; }
    }
    else {
      if (key_addr \in malicious_virt_map) {
        r <- is_key (oget phys_map.[oget malicious_virt_map.[key_addr]]);
      }
      else { r <- false; }
    }
    return r;
  }

  proc create_cell(pty : party, key_addr : addr, b : bool) : addr option = {
    var r : addr option;
    var phys_addr, virt_addr : addr;
    if (pty = Honest) {
      if (key_addr \in honest_virt_map) {
        match oget phys_map.[oget honest_virt_map.[key_addr]] with
        | Key key => {
            phys_addr <@
              phys_alloc(Cell {|key = key; cont = b; locked = true|});
            virt_addr <@ honest_virt_alloc(phys_addr);
            r <- Some virt_addr;
          }
        | Cell _  => { r <- None; }
        end;
      }
      else { r <- None; }
    }
    else {
      if (key_addr \in malicious_virt_map) {
        match oget phys_map.[oget malicious_virt_map.[key_addr]] with
        | Key key => {
            phys_addr <@
              phys_alloc(Cell {|key = key; cont = b; locked = true|});
            virt_addr <@ malicious_virt_alloc(phys_addr);
            r <- Some virt_addr;
          }
        | Cell _  => { r <- None; }
        end;
      }
      else { r <- None; }
    }
    return r;
  }

  proc is_cell(pty : party, cell_addr : addr) : bool = {
    var r : bool;
    if (pty = Honest) {
      if (cell_addr \in honest_virt_map) {
        r <- is_cell (oget phys_map.[oget honest_virt_map.[cell_addr]]);
      }
      else { r <- false; }
    }
    else {
      if (cell_addr \in malicious_virt_map) {
        r <- is_cell (oget phys_map.[oget malicious_virt_map.[cell_addr]]);
      }
      else { r <- false; }
    }
    return r;
  }

  proc unlock_cell(pty : party, cell_addr : addr, key_addr : addr)
         : addr option = {
    var r : addr option;
    var phys_addr, virt_addr : addr;
    var obj_cell, obj_key : object;
    var cell : cell; var key : key;
    if (pty = Honest) {
      if (cell_addr \in honest_virt_map /\
          key_addr  \in honest_virt_map) {
        obj_cell <- oget phys_map.[oget honest_virt_map.[cell_addr]];
        obj_key  <- oget phys_map.[oget honest_virt_map.[key_addr]];
        if (is_cell obj_cell /\ is_key obj_key) {
          cell <- oget (get_as_Cell obj_cell);
          key  <- oget (get_as_Key obj_key);
          if (cell.`key = key) {
            cell <- {|cell with locked = false|};
            phys_addr <@ phys_alloc(Cell cell);
            virt_addr <@ honest_virt_alloc(phys_addr);
            r <- Some virt_addr;
          }
          else { r <- None; }
        }
        else { r <- None; }
      }
      else { r <- None; }
    }
    else {
      if (cell_addr \in malicious_virt_map /\
          key_addr  \in malicious_virt_map) {
        obj_cell <- oget phys_map.[oget malicious_virt_map.[cell_addr]];
        obj_key  <- oget phys_map.[oget malicious_virt_map.[key_addr]];
        if (is_cell obj_cell /\ is_key obj_key) {
          cell <- oget (get_as_Cell obj_cell);
          key  <- oget (get_as_Key obj_key);
          if (cell.`key = key) {
            cell <- {|cell with locked = false|};
            phys_addr <@ phys_alloc(Cell cell);
            virt_addr <@ malicious_virt_alloc(phys_addr);
            r <- Some virt_addr;
          }
          else { r <- None; }
        }
        else { r <- None; }
      }
      else { r <- None; }
    }
    return r;
  }

  proc contents_cell(pty : party, cell_addr : addr) : bool option = {
    var r : bool option;
    if (pty = Honest) {
      if (cell_addr \in honest_virt_map) {
        match oget phys_map.[oget honest_virt_map.[cell_addr]] with
        | Key _     => { r <- None; }
        | Cell cell => {
            if (! cell.`locked) { r <- Some cell.`cont; }
            else { r <- None; }
          }
        end;
      }
      else { r <- None; }
    }
    else {
      if (cell_addr \in malicious_virt_map) {
        match oget phys_map.[oget malicious_virt_map.[cell_addr]] with
        | Key _     => { r <- None; }
        | Cell cell => {
            if (! cell.`locked) { r <- Some cell.`cont; }
            else { r <- None; }
          }
        end;
      }
      else { r <- None; }
    }
    return r;
  }
}.

(* glob Memory is the tuple type with the global variables of Memory
   in alphabetical; this is planned by the EasyCrypt developers to
   be turned into a more usable record type *)

type gm = glob Memory.

op gm_to_next_key                  (gm : gm)  : key                 = gm.`5.
op gm_to_next_phys_addr            (gm : gm)  : addr                = gm.`6.
op gm_to_phys_map                  (gm : gm)  : (addr, object) fmap = gm.`7.
op gm_to_honest_next_virt_addr     (gm : gm)  : addr                = gm.`1.
op gm_to_honest_virt_map           (gm : gm)  : (addr, addr) fmap   = gm.`2.
op gm_to_malicious_next_virt_addr  (gm : gm)  : addr                = gm.`3.
op gm_to_malicious_virt_map        (gm : gm)  : (addr, addr) fmap   = gm.`4.

lemma gm_eqP (gm1 gm2 : gm) :
  gm_to_next_key gm1 = gm_to_next_key gm2 =>
  gm_to_next_phys_addr gm1 = gm_to_next_phys_addr gm2 =>
  gm_to_phys_map gm1 = gm_to_phys_map gm2 =>
  gm_to_honest_next_virt_addr gm1 = gm_to_honest_next_virt_addr gm2 =>
  gm_to_honest_virt_map gm1 = gm_to_honest_virt_map gm2 =>
  gm_to_malicious_next_virt_addr gm1 = gm_to_malicious_next_virt_addr gm2 =>
  gm_to_malicious_virt_map gm1 = gm_to_malicious_virt_map gm2 =>
  gm1 = gm2.
proof. smt(). qed.

(* invariant respected by the procedures of Memory *)

op gm_invar_pre (gm : gm) : bool =
  0 <= gm_to_next_key gm /\
  0 <= gm_to_next_phys_addr gm /\
  0 <= gm_to_honest_next_virt_addr gm /\
  0 <= gm_to_malicious_next_virt_addr gm /\
  (forall (addr : addr),
   addr \in gm_to_phys_map gm =>
   0 <= addr < gm_to_next_phys_addr gm) /\
  (forall (addr : addr),
   addr \in gm_to_honest_virt_map gm =>
   0 <= addr < gm_to_honest_next_virt_addr gm) /\
  (forall (addr : addr),
   addr \in gm_to_malicious_virt_map gm =>
   0 <= addr < gm_to_malicious_next_virt_addr gm) /\
  (forall (addr : addr),
   rng (gm_to_honest_virt_map gm) addr =>
   addr \in gm_to_phys_map gm) /\
  (forall (addr : addr),
   rng (gm_to_malicious_virt_map gm) addr =>
   addr \in gm_to_phys_map gm) /\
  (forall (addr1 addr2 : addr, key : key),
   (gm_to_phys_map gm).[addr1] = Some (Key key) =>
   (gm_to_phys_map gm).[addr2] = Some (Key key) =>
   addr1 = addr2) /\
  (forall (addr : addr, cell : cell),
   (gm_to_phys_map gm).[addr] = Some (Cell cell) =>
   exists (addr' : addr),
   (gm_to_phys_map gm).[addr'] = Some (Key cell.`key)).

op gm_invar (gm : gm) : bool =
  gm_invar_pre gm /\
  (forall (addr : addr, key : key),
   (gm_to_phys_map gm).[addr] = Some (Key key) =>
   0 <= key < gm_to_next_key gm).

lemma gm_invar_old_mal_virt_addr_does_not_give_new_key
      (gm : gm, mal_virt_addr : addr) :
  gm_invar gm => mal_virt_addr \in gm_to_malicious_virt_map gm =>
  let key = gm_to_next_key gm in
  let phys_addr = oget (gm_to_malicious_virt_map gm).[mal_virt_addr] in
  oget (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Key key].[phys_addr] <>
  Key key.
proof.
move => gm_invar_gm mal_virt_addr_in_dom_malicious_virt_map_of_gm /=.
have H1 :
  oget (gm_to_malicious_virt_map gm).[mal_virt_addr] \in
  gm_to_phys_map gm by smt().
have H2 :
  oget (gm_to_malicious_virt_map gm).[mal_virt_addr] <>
  gm_to_next_phys_addr gm by smt().
rewrite get_setE H2 /= /#.
qed.

lemma rng_set_new (mp : ('a, 'b) fmap, x : 'a, y y' : 'b) :
  x \notin mp =>
  rng mp.[x <- y] y' <=> rng mp y' \/ y = y'.
proof. smt(get_setE). qed.

lemma memory_init_ll : islossless Memory.init.
proof. islossless. qed.

lemma memory_init :
  hoare
  [Memory.init :
   true ==>
   gm_invar (glob Memory)                  /\
   Memory.next_key                 = 0     /\
   Memory.next_phys_addr           = 0     /\
   Memory.phys_map                 = empty /\
   Memory.honest_next_virt_addr    = 0     /\
   Memory.honest_virt_map          = empty /\
   Memory.malicious_next_virt_addr = 0     /\
   Memory.malicious_virt_map       = empty].
proof.
proc; auto; smt(mem_empty mem_rng_empty).
qed.

lemma memory_phys_alloc_key (gm : gm, key : key) :
  hoare
  [Memory.phys_alloc :
   glob Memory = gm /\ gm_invar_pre gm /\
   (forall (addr : addr, key : key),
    (gm_to_phys_map gm).[addr] = Some (Key key) =>
    0 <= key < gm_to_next_key gm - 1) /\
   obj = Key key /\ 0 <= key /\ key = gm_to_next_key gm - 1 ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
   (* changed *)
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map = (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Key key] /\
   res = gm_to_next_phys_addr gm].
proof.
proc; auto; smt(get_setE).
qed.

lemma memory_phys_alloc_cell (gm : gm, cell : cell) :
  hoare
  [Memory.phys_alloc :
   obj = Cell cell /\ 0 <= cell.`key < Memory.next_key /\
   (exists (addr : addr), Memory.phys_map.[addr] = Some (Key cell.`key)) /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
   (* changed *)
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map = (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Cell cell] /\
   res = gm_to_next_phys_addr gm].
proof.
proc; auto; smt(get_setE).
qed.

lemma memory_honest_virt_alloc (gm : gm, phys_addr' : addr) :
  hoare
  [Memory.honest_virt_alloc :
   phys_addr = phys_addr' /\ phys_addr' \in Memory.phys_map /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
   (* changed *)
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm + 1 /\
   Memory.honest_virt_map =
   (gm_to_honest_virt_map gm).[gm_to_honest_next_virt_addr gm <- phys_addr'] /\
   res = gm_to_honest_next_virt_addr gm].
proof.
proc; auto; smt(mem_set rng_set_new).
qed.

lemma memory_malicious_virt_alloc (gm : gm, phys_addr' : addr) :
  hoare
  [Memory.malicious_virt_alloc :
   phys_addr = phys_addr' /\ phys_addr' \in Memory.phys_map /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   (* changed *)
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm + 1 /\
   Memory.malicious_virt_map =
   (gm_to_malicious_virt_map gm).[gm_to_malicious_next_virt_addr gm <-
                                  phys_addr'] /\
   res = gm_to_malicious_next_virt_addr gm].
proof.
proc; auto; smt(mem_set rng_set_new).
qed.

lemma memory_trans_virt_addr_ll :
  islossless Memory.trans_virt_addr.
proof. islossless. qed.

lemma memory_trans_virt_addr_gm_invar :
  hoare
  [Memory.trans_virt_addr :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; inline*; auto; smt(mem_set rng_set_new).
qed.

lemma memory_trans_virt_addr (gm : gm, pty' : party, addr' : addr) :
  hoare
  [Memory.trans_virt_addr :
   pty = pty' /\ addr = addr' /\
   (if pty = Honest
    then addr \in Memory.honest_virt_map
    else addr \in Memory.malicious_virt_map) /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   (* changed *)
   if pty' = Honest
   then (let phys_addr = oget (Memory.honest_virt_map.[addr']) in
         let virt_addr_malic = gm_to_malicious_next_virt_addr gm in
         Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
         Memory.honest_virt_map = gm_to_honest_virt_map gm /\
         Memory.malicious_next_virt_addr = virt_addr_malic + 1 /\
         Memory.malicious_virt_map =
         (gm_to_malicious_virt_map gm).[virt_addr_malic <- phys_addr] /\
         res = Some virt_addr_malic)
   else (let phys_addr = oget (Memory.malicious_virt_map.[addr']) in
         let virt_addr_honest = gm_to_honest_next_virt_addr gm in
         Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
         Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
         Memory.honest_next_virt_addr = virt_addr_honest + 1 /\
         Memory.honest_virt_map =
         (gm_to_honest_virt_map gm).[virt_addr_honest <- phys_addr] /\
         res = Some virt_addr_honest)].
proof.
proc.
if.
rcondt 1; first auto.
sp.
exlim phys_addr => pa'.
exlim (glob Memory) => gm'.
wp.
call (memory_malicious_virt_alloc gm' pa').
auto; smt().
rcondt 1; first auto; smt().
sp.
exlim phys_addr => pa'.
exlim (glob Memory) => gm'.
wp.
call (memory_honest_virt_alloc gm' pa').
auto; smt().
qed.

lemma memory_trans_virt_addr_bad (gm : gm) :
  hoare
  [Memory.trans_virt_addr :
   (if pty = Honest
    then addr \notin Memory.honest_virt_map
    else addr \notin Memory.malicious_virt_map) /\
   glob Memory = gm /\ gm_invar gm ==>
   glob Memory = gm /\ gm_invar (glob Memory)].
proof.
proc; if; [rcondf 1; auto | rcondf 1; auto; smt()].
qed.

lemma memory_create_key_ll : islossless Memory.create_key.
proof. islossless. qed.

lemma memory_create_key_gm_invar :
  hoare
  [Memory.create_key :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; inline*; auto; smt(mem_set get_setE).
qed.

lemma memory_create_key (gm : gm, pty' : party) :
  hoare
  [Memory.create_key :
   pty = pty' /\ glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm + 1 /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <- Key (gm_to_next_key gm)] /\
   (if pty' = Honest
    then (Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
            .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = gm_to_honest_next_virt_addr gm /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
            .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = gm_to_malicious_next_virt_addr gm /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))].
proof.
proc.
sp.
seq 1 :
  (gm_invar gm /\ Memory.next_key = key + 1 /\ pty = pty' /\
   phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm + 1 /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Key key] /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm) => //.
auto.
exlim (glob Memory) => gm'.
exlim key => key'.
call (memory_phys_alloc_key gm' key').
auto; smt().
if.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_honest_virt_alloc gm' phys_addr').
auto; progress; smt(mem_set get_setE).
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_malicious_virt_alloc gm' phys_addr').
auto; progress; smt(mem_set get_setE).
qed.

op key_addr_good (pty : party, gm : gm, key_addr : addr) : bool =
  if pty = Honest
  then (key_addr \in (gm_to_honest_virt_map gm) /\
        is_key
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_honest_virt_map gm).[key_addr])])))
  else (key_addr \in (gm_to_malicious_virt_map gm) /\
        is_key
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_malicious_virt_map gm).[key_addr])]))).

op key_addr_to_key (pty : party, gm : gm, key_addr : addr) : key =
  if pty = Honest
  then oget
       (get_as_Key
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_honest_virt_map gm).[key_addr])])))
  else oget
       (get_as_Key
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_malicious_virt_map gm).[key_addr])]))).

lemma memory_is_key_ll : islossless Memory.is_key.
proof. islossless. qed.

lemma memory_is_key_gm_invar :
  hoare
  [Memory.is_key : gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; auto.
qed.

lemma memory_is_key_true (gm : gm) :
  hoare
  [Memory.is_key :
   glob Memory = gm /\ gm_invar gm /\ key_addr_good pty gm key_addr ==>
   glob Memory = gm /\ res].
proof.
proc; auto; smt().
qed.

lemma memory_is_key_false (gm : gm) :
  hoare
  [Memory.is_key :
   glob Memory = gm /\ gm_invar gm /\ ! key_addr_good pty gm key_addr ==>
   glob Memory = gm /\ ! res].
proof.
proc; auto; smt().
qed.

lemma memory_create_cell_ll : islossless Memory.create_cell.
proof.
islossless.
match; islossless.
match; islossless.
qed.

lemma memory_create_cell_gm_invar :
  hoare
  [Memory.create_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; if; if.
match.
inline*; auto; progress; smt(mem_set get_setE).
auto.
auto.
match.
inline*; auto; progress; smt(mem_set get_setE).
auto.
auto.
qed.

lemma memory_create_cell
      (gm : gm, pty' : party, key_addr' : addr, b' : bool) :
  hoare
  [Memory.create_cell :
   pty = pty' /\ key_addr = key_addr' /\ b = b' /\
   glob Memory = gm /\ gm_invar gm /\ key_addr_good pty gm key_addr ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   (if pty' = Honest
    then (let key = key_addr_to_key Honest gm key_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|key = key; cont = b'; locked = true|}] /\
          Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
             .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_honest_next_virt_addr gm) /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (let key = key_addr_to_key Malicious gm key_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|key = key; cont = b'; locked = true|}] /\
          Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
             .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_malicious_next_virt_addr gm) /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))].
proof.
proc.
if.
rcondt 1; first auto; smt().
match Key 1; first auto; smt().
exlim key => key'.
seq 1 :
  (pty = pty' /\ pty' = Honest /\ key_addr' \in gm_to_honest_virt_map gm /\
   key_addr_good Honest gm key_addr' /\
   key' = key_addr_to_key Honest gm key_addr' /\
   gm_invar gm /\ phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell {|key = key'; cont = b'; locked = true|}] /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm) => //.
call (memory_phys_alloc_cell gm {|key = key'; cont = b'; locked = true|}).
auto; progress; smt().
wp.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_honest_virt_alloc gm' phys_addr').
auto => /> /= ; progress; smt(mem_set get_setE).
rcondt 1; first auto; smt().
match Key 1; first auto; smt().
exlim key => key'.
seq 1 :
  (pty = pty' /\ pty' = Malicious /\ key_addr' \in gm_to_malicious_virt_map gm /\
   key_addr_good Malicious gm key_addr' /\
   key' = key_addr_to_key Malicious gm key_addr' /\
   gm_invar gm /\ phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell {|key = key'; cont = b'; locked = true|}] /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm) => //.
call (memory_phys_alloc_cell gm {|key = key'; cont = b'; locked = true|}).
auto; progress; smt().
wp.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_malicious_virt_alloc gm' phys_addr').
auto => /> /=; progress; smt(mem_set get_setE).
qed.

lemma memory_create_cell_bad (gm : gm) :
  hoare
  [Memory.create_cell :
   glob Memory = gm /\ gm_invar gm /\ ! key_addr_good pty gm key_addr ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
   res = None].
proof.
proc; if; (if; [match Cell 1; [auto; smt() | auto] | auto]).
qed.

op cell_addr_good (pty : party, gm : gm, cell_addr : addr) : bool =
  if pty = Honest
  then (cell_addr \in (gm_to_honest_virt_map gm) /\
        is_cell
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_honest_virt_map gm).[cell_addr])])))
  else (cell_addr \in (gm_to_malicious_virt_map gm) /\
        is_cell
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_malicious_virt_map gm).[cell_addr])]))).

op cell_addr_to_cell (pty : party, gm : gm, cell_addr : addr) : cell =
  if pty = Honest
  then oget
       (get_as_Cell
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_honest_virt_map gm).[cell_addr])])))
  else oget
       (get_as_Cell
        (oget
         ((gm_to_phys_map gm)
            .[oget ((gm_to_malicious_virt_map gm).[cell_addr])]))).

lemma good_cell_addr_key_in_mem (pty : party, gm : gm, cell_addr : addr) :
  gm_invar gm => cell_addr_good pty gm cell_addr =>
  exists (key_addr : addr),
  (gm_to_phys_map gm).[key_addr] =
  Some (Key (cell_addr_to_cell pty gm cell_addr).`key).
proof.
move => gmi_gm.
rewrite /cell_addr_good /cell_addr_to_cell.
case pty => /=.
move => [H1 H2].
have [cell H3] : 
  exists cell,
  oget (gm_to_phys_map gm)
         .[oget (gm_to_honest_virt_map gm).[cell_addr]] =
  Cell cell by smt().
rewrite /get_as_Cell H3 /= /#.
move => [H1 H2].
have [cell H3] : 
  exists cell,
  oget (gm_to_phys_map gm)
         .[oget (gm_to_malicious_virt_map gm).[cell_addr]] =
  Cell cell by smt().
rewrite /get_as_Cell H3 /= /#.
qed.

op good_cell_addr_unlocked_by_good_key_addr
   (pty : party, gm : gm, cell_addr key_addr : addr) : bool =
  let cell = cell_addr_to_cell pty gm cell_addr in
  let key = key_addr_to_key pty gm key_addr in
  cell.`key = key.

op good_cell_addr_unlocked (pty : party, gm : gm, cell_addr) : bool =
  let cell = cell_addr_to_cell pty gm cell_addr in
  ! cell.`locked.

lemma memory_is_cell_ll : islossless Memory.is_cell.
proof. islossless. qed.

lemma memory_is_cell_gm_invar :
  hoare
  [Memory.is_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; auto; smt().
qed.

lemma memory_is_cell_true (gm : gm) :
  hoare
  [Memory.is_cell :
   glob Memory = gm /\ gm_invar gm /\ cell_addr_good pty gm cell_addr ==>
   glob Memory = gm /\ res].
proof.
proc; auto; smt().
qed.

lemma memory_is_cell_false (gm : gm) :
  hoare
  [Memory.is_cell :
   glob Memory = gm /\ gm_invar gm /\ ! cell_addr_good pty gm cell_addr ==>
   glob Memory = gm /\ ! res].
proof.
proc; auto; smt().
qed.

lemma memory_unlock_cell_ll : islossless Memory.unlock_cell.
proof. islossless. qed.

lemma memory_unlock_cell_gm_invar :
  hoare
  [Memory.unlock_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; if; if; sp.
if.
sp.
if.
sp; wp; elim* => cell0; inline*.
(auto; progress; first 4 smt()); first 6 smt(get_setE).
smt(get_setE rng_set_new). smt(get_setE). smt(get_setE).
rewrite /gm_to_phys_map /= in H5. rewrite /gm_to_phys_map /=.
case (addr = Memory.next_phys_addr{hr}) => [eq_addr_npa | neq_addr_npa].
move : H5.
rewrite get_setE eq_addr_npa /=.
move => <- /=.
pose cell1 := 
  oget
  (get_as_Cell
   (oget
    Memory.phys_map{hr}
      .[oget Memory.honest_virt_map{hr}.[cell_addr{hr}]])).
have [addr'] eq_pm_addr'_cell1_key :
  exists addr',
  Memory.phys_map{hr}.[addr'] = Some (Key cell1.`key) by smt().
exists addr'.
have ne_addr'_npa : addr' <> Memory.next_phys_addr{hr} by smt(domE).
by rewrite get_setE ne_addr'_npa /=.
move : H5 => H5.
rewrite get_setE neq_addr_npa /= in H5.
have [addr' eq_pm_addr'_cell0_key] :
  exists addr',
  Memory.phys_map{hr}.[addr'] = Some (Key cell0.`key)
    by smt().
exists addr'.
have neq_addr'_npa : addr' <> Memory.next_phys_addr{hr} by smt(domE).
by rewrite get_setE neq_addr'_npa /=.
smt(get_setE). smt(get_setE).
auto.
auto.
auto.
if.
sp.
if.
sp; wp; elim* => cell0; inline*.
(auto; progress; first 4 smt()); first 6 smt(get_setE).
smt(get_setE rng_set_new). smt(mem_set get_setE).
smt(get_setE).
rewrite /gm_to_phys_map /= in H6. rewrite /gm_to_phys_map /=.
case (addr = Memory.next_phys_addr{hr}) => [eq_addr_npa | neq_addr_npa].
move : H6.
rewrite get_setE eq_addr_npa /=.
move => <- /=.
pose cell1 := 
  oget
  (get_as_Cell
   (oget
    Memory.phys_map{hr}
      .[oget Memory.malicious_virt_map{hr}.[cell_addr{hr}]])).
have [addr'] eq_pm_addr'_cell1_key :
  exists addr',
  Memory.phys_map{hr}.[addr'] = Some (Key cell1.`key) by smt().
exists addr'.
have ne_addr'_npa : addr' <> Memory.next_phys_addr{hr} by smt(domE).
by rewrite get_setE ne_addr'_npa /=.
move : H6 => H6.
rewrite get_setE neq_addr_npa /= in H6.
have [addr' eq_pm_addr'_cell0_key] :
  exists addr',
  Memory.phys_map{hr}.[addr'] = Some (Key cell0.`key)
    by smt().
exists addr'.
have neq_addr'_npa : addr' <> Memory.next_phys_addr{hr} by smt(domE).
by rewrite get_setE neq_addr'_npa /=.
smt(get_setE). smt(get_setE).
auto.
auto.
auto.
qed.

lemma memory_unlock_cell (gm : gm , pty' : party, cell_addr' key_addr' : addr) :
  hoare
  [Memory.unlock_cell :
   pty = pty' /\ cell_addr = cell_addr' /\ key_addr = key_addr' /\
   glob Memory = gm /\ gm_invar gm /\
   cell_addr_good pty gm cell_addr /\ key_addr_good pty gm key_addr /\
   good_cell_addr_unlocked_by_good_key_addr pty gm cell_addr key_addr ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   (if pty' = Honest
    then (let cell = cell_addr_to_cell Honest gm cell_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|cell with locked = false|}] /\
          Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
             .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_honest_next_virt_addr gm) /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (let cell = cell_addr_to_cell Malicious gm cell_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|cell with locked = false|}] /\
          Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
             .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_malicious_next_virt_addr gm) /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))].
proof.
proc.
if.
rcondt 1; first auto; smt().
sp 2.
rcondt 1; first auto; smt().
sp 2.
rcondt 1; first auto; smt().
sp 1.
elim* => cell'.
rewrite /=.
seq 1 :
  (pty = pty' /\ pty' = Honest /\ gm_invar gm /\
   cell' = cell_addr_to_cell pty gm cell_addr' /\
   cell_addr_good Honest gm cell_addr' /\
   phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell {|cell' with locked = false|}] /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm) => //.
call (memory_phys_alloc_cell gm {|cell' with locked = false|}).
auto; smt().
wp => /=.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_honest_virt_alloc gm' phys_addr').
auto; progress; smt(mem_set rng_set_new get_setE good_cell_addr_key_in_mem).
rcondt 1; first auto; smt().
sp 2.
rcondt 1; first auto; smt().
sp 2.
rcondt 1; first auto; smt().
sp 1.
elim* => cell'.
rewrite /=.
seq 1 :
  (pty = pty' /\ pty' = Malicious /\ gm_invar gm /\
   cell' = cell_addr_to_cell pty gm cell_addr' /\
   cell_addr_good Malicious gm cell_addr' /\
   phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell {|cell' with locked = false|}] /\
   Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
   Memory.honest_virt_map = gm_to_honest_virt_map gm /\
   Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map = gm_to_malicious_virt_map gm) => //.
call (memory_phys_alloc_cell gm {|cell' with locked = false|}).
auto; progress; smt().
wp => /=.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_malicious_virt_alloc gm' phys_addr').
auto; progress; smt(mem_set rng_set_new get_setE good_cell_addr_key_in_mem).
qed.

lemma memory_unlock_cell_bad
      (gm : gm , pty' : party, cell_addr' key_addr' : addr) :
  hoare
  [Memory.unlock_cell :
   glob Memory = gm /\ gm_invar gm /\
   (! cell_addr_good pty gm cell_addr \/
    ! key_addr_good pty gm key_addr \/
    ! good_cell_addr_unlocked_by_good_key_addr pty gm cell_addr key_addr) ==>
   glob Memory = gm /\ gm_invar (glob Memory) /\ res = None].
proof.
proc.
if; (if; [sp; if; [sp; if; [exfalso; smt() | auto] | auto] | auto]).
qed.

lemma memory_contents_cell_ll : islossless Memory.contents_cell.
proof.
islossless.
match; islossless.
match; islossless.
qed.

lemma memory_contents_cell_gm_invar :
  hoare
  [Memory.contents_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; auto; smt().
qed.

lemma memory_contents_cell (gm : gm , pty' : party, cell_addr' : addr) :
  hoare
  [Memory.contents_cell :
   pty = pty' /\ cell_addr = cell_addr' /\
   glob Memory = gm /\ gm_invar gm /\
   cell_addr_good pty gm cell_addr /\
   good_cell_addr_unlocked pty gm cell_addr ==>
   glob Memory = gm /\ gm_invar (glob Memory) /\
   (let cell = cell_addr_to_cell pty' gm cell_addr' in
    res = Some cell.`cont)].
proof.
proc.
if.
rcondt 1; first auto; smt().
match Cell 1; first auto; smt().
rcondt 1; first auto; smt().
auto; smt().
rcondt 1; first auto; smt().
match Cell 1; first auto; smt().
rcondt 1; first auto; smt().
auto; smt().
qed.

lemma memory_contents_cell_bad (gm : gm , pty' : party, cell_addr' : addr) :
  hoare
  [Memory.contents_cell :
   pty = pty' /\ cell_addr = cell_addr' /\
   glob Memory = gm /\ gm_invar gm /\
   (! cell_addr_good pty gm cell_addr \/
    ! good_cell_addr_unlocked pty gm cell_addr) ==>
   glob Memory = gm /\ gm_invar (glob Memory) /\
   res = None].
proof.
proc.
if.
if.
case
  (exists (key : key),
   oget Memory.phys_map.[oget Memory.honest_virt_map.[cell_addr]] =
   Key key).
match Key 1; auto.
match Cell 1; first auto; smt().
rcondf 1; auto; smt().
auto.
if.
case
  (exists (key : key),
   oget Memory.phys_map.[oget Memory.malicious_virt_map.[cell_addr]] =
   Key key).
match Key 1; auto.
match Cell 1; first auto; smt().
rcondf 1; auto; smt().
auto.
qed.

(* messages *)

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
   of the clients of both the honest and malicious parties

   thus it "knows" both the choice and guess, giving us a strong
   notion of security modeling the idea that one client may have
   an idea what the other will choose or guess, or may have some
   influence on the other party *)

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

(* a party's interface to the memory; like the corresponding
   functions of MEMORY, but where the party is implicit,
   and initialization is not possible *)

module type PARTY_MEMORY = {
  proc trans_virt_addr(addr : addr) : addr option

  proc create_key() : addr

  proc is_key(key_addr : addr) : bool

  proc create_cell(key_addr : addr, b : bool) : addr option

  proc is_cell(cell_addr : addr) : bool

  proc unlock_cell(cell_addr : addr, key_addr : addr) : addr option

  proc contents_cell(cell_addr : addr) : bool option
}.

theory PartyMemory.

(* begin theory parameters *)

op party : party.

(* end theory parameters *)

module PartyMemory : PARTY_MEMORY = {
  proc trans_virt_addr(addr : addr) : addr option = {
    var r : addr option;
    r <@ Memory.trans_virt_addr(party, addr);
    return r;
  }

  proc create_key() : addr = {
    var r : addr;
    r <@ Memory.create_key(party);
    return r;
  }

  proc is_key(key_addr : addr) : bool = {
    var r : bool;
    r <@ Memory.is_key(party, key_addr);
    return r;
  }

  proc create_cell(key_addr : addr, b : bool) : addr option = {
    var r : addr option;
    r <@ Memory.create_cell(party, key_addr, b);
    return r;
  }

  proc is_cell(cell_addr : addr) : bool = {
    var r : bool;
    r <@ Memory.is_cell(party, cell_addr);
    return r;
  }

  proc unlock_cell(cell_addr : addr, key_addr : addr) : addr option = {
    var r : addr option;
    r <@ Memory.unlock_cell(party, cell_addr, key_addr);
    return r;
  }

  proc contents_cell(cell_addr : addr) : bool option = {
    var r : bool option;
    r <@ Memory.contents_cell(party, cell_addr);
    return r;
  }
}.

lemma party_memory_trans_virt_addr_ll :
  islossless PartyMemory.trans_virt_addr.
proof. islossless. qed.

lemma party_memory_trans_virt_addr_gm_invar :
  hoare
  [PartyMemory.trans_virt_addr :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_trans_virt_addr_gm_invar; auto.
qed.

lemma party_memory_trans_virt_addr (gm : gm, addr' : addr) :
  hoare
  [PartyMemory.trans_virt_addr :
   addr = addr' /\
   (if party = Honest
    then addr \in Memory.honest_virt_map
    else addr \in Memory.malicious_virt_map) /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   (* changed *)
   if party = Honest
   then (let phys_addr = oget (Memory.honest_virt_map.[addr']) in
         let virt_addr_malic = gm_to_malicious_next_virt_addr gm in
         Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
         Memory.honest_virt_map = gm_to_honest_virt_map gm /\
         Memory.malicious_next_virt_addr = virt_addr_malic + 1 /\
         Memory.malicious_virt_map =
         (gm_to_malicious_virt_map gm).[virt_addr_malic <- phys_addr] /\
         res = Some virt_addr_malic)
   else (let phys_addr = oget (Memory.malicious_virt_map.[addr']) in
         let virt_addr_honest = gm_to_honest_next_virt_addr gm in
         Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
         Memory.malicious_virt_map = gm_to_malicious_virt_map gm /\
         Memory.honest_next_virt_addr = virt_addr_honest + 1 /\
         Memory.honest_virt_map =
         (gm_to_honest_virt_map gm).[virt_addr_honest <- phys_addr] /\
         res = Some virt_addr_honest)].
proof.
proc.
call (memory_trans_virt_addr gm party addr').
auto.
qed.

lemma party_memory_create_key_ll :
  islossless PartyMemory.create_key.
proof. islossless. qed.

lemma party_memory_create_key_gm_invar :
  hoare
  [PartyMemory.create_key :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_create_key_gm_invar; auto.
qed.

lemma party_memory_create_key (gm : gm) :
  hoare
  [PartyMemory.create_key :
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm + 1 /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <- Key (gm_to_next_key gm)] /\
   (if party = Honest
    then (Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
            .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = gm_to_honest_next_virt_addr gm /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
            .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = gm_to_malicious_next_virt_addr gm /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))].
proof.
proc.
call (memory_create_key gm party).
auto.
qed.

(* probabilistic lemmas are always with probability 1 *)

lemma party_memory_create_key_phl (gm : gm) :
  phoare
  [PartyMemory.create_key :
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm + 1 /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <- Key (gm_to_next_key gm)] /\
   (if party = Honest
    then (Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
            .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = gm_to_honest_next_virt_addr gm /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
            .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = gm_to_malicious_next_virt_addr gm /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))] = 1%r.
proof.
conseq (_ : true ==> true) (_ : _ ==> _) => //.
apply (party_memory_create_key gm).
apply party_memory_create_key_ll.
qed.

lemma party_memory_is_key_ll : islossless PartyMemory.is_key.
proof. islossless. qed.

lemma party_memory_is_key_gm_invar :
  hoare
  [PartyMemory.is_key :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_is_key_gm_invar; auto.
qed.

lemma party_memory_is_key_true (gm : gm) :
  hoare
  [PartyMemory.is_key :
   glob Memory = gm /\ gm_invar gm /\ key_addr_good party gm key_addr ==>
   glob Memory = gm /\ res].
proof.
proc.
call (memory_is_key_true gm).
auto.
qed.

lemma party_memory_is_key_false (gm : gm) :
  hoare
  [PartyMemory.is_key :
   glob Memory = gm /\ gm_invar gm /\ ! key_addr_good party gm key_addr ==>
   glob Memory = gm /\ ! res].
proof.
proc.
call (memory_is_key_false gm).
auto.
qed.

lemma party_memory_create_cell_ll :
  islossless PartyMemory.create_cell.
proof.
proc.
call memory_create_cell_ll.
auto.
qed.

lemma party_memory_create_cell_gm_invar :
  hoare
  [PartyMemory.create_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_create_cell_gm_invar; auto.
qed.

lemma party_memory_create_cell (gm : gm, key_addr' : addr, b' : bool) :
  hoare
  [PartyMemory.create_cell :
   key_addr = key_addr' /\ b = b' /\
   glob Memory = gm /\ gm_invar gm /\ key_addr_good party gm key_addr ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   (if party = Honest
    then (let key = key_addr_to_key Honest gm key_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|key = key; cont = b'; locked = true|}] /\
          Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
             .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_honest_next_virt_addr gm) /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (let key = key_addr_to_key Malicious gm key_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|key = key; cont = b'; locked = true|}] /\
          Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
             .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_malicious_next_virt_addr gm) /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))].
proof.
proc.
call (memory_create_cell gm party key_addr' b').
auto.
qed.

lemma party_memory_create_cell_phl (gm : gm, key_addr' : addr, b' : bool) :
  phoare
  [PartyMemory.create_cell :
   key_addr = key_addr' /\ b = b' /\
   glob Memory = gm /\ gm_invar gm /\ key_addr_good party gm key_addr ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   (if party = Honest
    then (let key = key_addr_to_key Honest gm key_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|key = key; cont = b'; locked = true|}] /\
          Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
             .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_honest_next_virt_addr gm) /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (let key = key_addr_to_key Malicious gm key_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|key = key; cont = b'; locked = true|}] /\
          Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
             .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_malicious_next_virt_addr gm) /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))] = 1%r.
proof.
conseq (_ : true ==> true) (_ : _ ==> _) => //.
apply (party_memory_create_cell gm key_addr' b').
apply party_memory_create_cell_ll.
qed.

lemma party_memory_is_cell_ll : islossless PartyMemory.is_cell.
proof. islossless. qed.

lemma party_memory_is_cell_gm_invar :
  hoare
  [PartyMemory.is_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_is_cell_gm_invar; auto.
qed.

lemma party_memory_is_cell_true (gm : gm) :
  hoare
  [PartyMemory.is_cell :
   glob Memory = gm /\ gm_invar gm /\ cell_addr_good party gm cell_addr ==>
   glob Memory = gm /\ res].
proof.
proc.
call (memory_is_cell_true gm).
auto.
qed.

lemma party_memory_is_cell_false (gm : gm) :
  hoare
  [PartyMemory.is_cell :
   glob Memory = gm /\ gm_invar gm /\ ! cell_addr_good party gm cell_addr ==>
   glob Memory = gm /\ ! res].
proof.
proc.
call (memory_is_cell_false gm).
auto.
qed.

lemma party_memory_unlock_cell_ll :
  islossless PartyMemory.unlock_cell.
proof.
proc.
call memory_unlock_cell_ll.
auto.
qed.

lemma party_memory_unlock_cell_gm_invar :
  hoare
  [PartyMemory.unlock_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_unlock_cell_gm_invar; auto.
qed.

lemma party_memory_unlock_cell (gm : gm , cell_addr' key_addr' : addr) :
  hoare
  [PartyMemory.unlock_cell :
   cell_addr = cell_addr' /\ key_addr = key_addr' /\
   glob Memory = gm /\ gm_invar gm /\
   cell_addr_good party gm cell_addr /\ key_addr_good party gm key_addr /\
   good_cell_addr_unlocked_by_good_key_addr party gm cell_addr key_addr ==>
   gm_invar (glob Memory) /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   (if party = Honest
    then (let cell = cell_addr_to_cell Honest gm cell_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|cell with locked = false|}] /\
          Memory.honest_next_virt_addr =
          gm_to_honest_next_virt_addr gm + 1 /\
          Memory.honest_virt_map =
          (gm_to_honest_virt_map gm)
             .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_honest_next_virt_addr gm) /\
          Memory.malicious_next_virt_addr = gm_to_malicious_next_virt_addr gm /\
          Memory.malicious_virt_map = gm_to_malicious_virt_map gm)
    else (let cell = cell_addr_to_cell Malicious gm cell_addr' in
          Memory.phys_map =
          (gm_to_phys_map gm)
             .[gm_to_next_phys_addr gm <-
               Cell {|cell with locked = false|}] /\
          Memory.malicious_next_virt_addr =
          gm_to_malicious_next_virt_addr gm + 1 /\
          Memory.malicious_virt_map =
          (gm_to_malicious_virt_map gm)
             .[gm_to_malicious_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
          res = Some (gm_to_malicious_next_virt_addr gm) /\
          Memory.honest_next_virt_addr = gm_to_honest_next_virt_addr gm /\
          Memory.honest_virt_map = gm_to_honest_virt_map gm))].
proof.
proc.
call (memory_unlock_cell gm party cell_addr' key_addr').
auto.
qed.

lemma party_memory_contents_cell_ll :
  islossless PartyMemory.contents_cell.
proof.
proc.
call memory_contents_cell_ll.
auto.
qed.

lemma party_memory_contents_cell_gm_invar :
  hoare
  [PartyMemory.contents_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; call memory_contents_cell_gm_invar; auto.
qed.

lemma party_memory_contents_cell (gm : gm , cell_addr' : addr) :
  hoare
  [PartyMemory.contents_cell :
   cell_addr = cell_addr' /\
   glob Memory = gm /\ gm_invar gm /\
   cell_addr_good party gm cell_addr /\
   good_cell_addr_unlocked party gm cell_addr ==>
   glob Memory = gm /\ gm_invar (glob Memory) /\
   (let cell = cell_addr_to_cell party gm cell_addr' in
    res = Some cell.`cont)].
proof.
proc.
call (memory_contents_cell gm party cell_addr').
auto.
qed.

end PartyMemory.

(* we clone PartyMemory twice: *)

clone PartyMemory as HonestMemory with
  op party <- Honest
proof *.

clone PartyMemory as MaliciousMemory with
  op party <- Malicious
proof *.

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

(* we have two instances of Honest:

   Honest.Honest      : PARTY
   OtherHonest.Honest : PARTY
*)

clone Honest as OtherHonest.

(********************************* Correctness ********************************)

(* For correctness, we let both parties be Honest, and show that no
   matter which roles we assign then (chooser/guesser) and whatever
   choices/guesses we tell them to use (using from_adv), there is a
   sequence of calls to the queue and deliver procedures such that
   when to_adv is called for the chooser/guesser, the results
   correctly say who won/lost. *)

module type INPUTS = {
  proc chooser() : party  (* decide which party will be the chooser *)

  proc choice_and_guess() : bool  (* the chooser's choice *)
                          * bool  (* the guesser's guess *)
}.

(* turn an INPUTS module into an adversary *)

module CorrectAdv (Inputs : INPUTS, Proto : PROTOCOL) = {
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
   Memory.next_key = 0 /\
   Memory.next_phys_addr = 0 /\
   Memory.phys_map = empty /\
   Memory.honest_next_virt_addr = 0 /\
   Memory.honest_virt_map = empty /\
   Memory.malicious_next_virt_addr = 0 /\
   Memory.malicious_virt_map = empty ==>
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
   then (Memory.honest_next_virt_addr = 2 /\
         Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
         Memory.malicious_next_virt_addr = 0 /\
         Memory.malicious_virt_map = empty)
   else (Memory.malicious_next_virt_addr = 2 /\
         Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
         Memory.honest_next_virt_addr = 0 /\
         Memory.honest_virt_map = empty))).
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
   Memory.honest_next_virt_addr = 1 /\
   Memory.honest_virt_map = (empty.[0 <- 0]) /\
   Memory.malicious_next_virt_addr = 0 /\
   Memory.malicious_virt_map = empty).
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_create_key gm); first auto.
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
   Memory.malicious_next_virt_addr = 1 /\
   Memory.malicious_virt_map = (empty.[0 <- 0]) /\
   Memory.honest_next_virt_addr = 0 /\
   Memory.honest_virt_map = empty).
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_create_key gm); first auto.
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 0 /\
          Memory.malicious_virt_map = empty)
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 0 /\
          Memory.honest_virt_map = empty))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 1 /\
          Memory.malicious_virt_map = empty.[0 <- 1])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 1 /\
          Memory.honest_virt_map = empty.[0 <- 1]))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 1 /\
          Memory.malicious_virt_map = empty.[0 <- 1])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 1 /\
          Memory.honest_virt_map = empty.[0 <- 1]))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 1 /\
          Memory.malicious_virt_map = empty.[0 <- 1])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 1 /\
          Memory.honest_virt_map = empty.[0 <- 1]))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 1 /\
          Memory.malicious_virt_map = empty.[0 <- 1])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 1 /\
          Memory.honest_virt_map = empty.[0 <- 1]))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = empty.[0 <- 1].[1 <- 0])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = empty.[0 <- 1].[1 <- 0]))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 3 /\
          Memory.malicious_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 3 /\
          Memory.honest_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2]))).
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
    (Memory.malicious_next_virt_addr = 2 /\
     Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
     Memory.honest_next_virt_addr = 3 /\
     Memory.honest_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2])).
exlim (glob Memory) => gm.
call (HonestMemory.party_memory_unlock_cell gm 0 1).
auto; smt(mem_set get_setE).
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
    (Memory.honest_next_virt_addr = 2 /\
     Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
     Memory.malicious_next_virt_addr = 3 /\
     Memory.malicious_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2])).
exlim (glob Memory) => gm.
call (MaliciousMemory.party_memory_unlock_cell gm 0 1).
auto; smt(mem_set get_setE).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 3 /\
          Memory.malicious_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 3 /\
          Memory.honest_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2]))).
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
    then (Memory.honest_next_virt_addr = 2 /\
          Memory.honest_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.malicious_next_virt_addr = 3 /\
          Memory.malicious_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2])
    else (Memory.malicious_next_virt_addr = 2 /\
          Memory.malicious_virt_map = (empty.[0 <- 0]).[1 <- 1] /\
          Memory.honest_next_virt_addr = 3 /\
          Memory.honest_virt_map = empty.[0 <- 1].[1 <- 0].[2 <- 2]))).
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
   Memory.next_key                 = 0 /\
   Memory.next_phys_addr           = 0 /\
   Memory.phys_map                 = empty /\
   Memory.honest_next_virt_addr    = 0 /\
   Memory.honest_virt_map          = empty /\
   Memory.malicious_next_virt_addr = 0 /\
   Memory.malicious_virt_map       = empty).
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
  (gm_to_honest_virt_map gm).[cell_hon_virt_addr] = Some cell_phys_addr /\
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
rcondf 1; first auto.
if.
auto; progress.
rewrite /gm_invar_guesser /gm_to_honest_virt_map /gm_to_phys_map /=.
rewrite /gm_invar_guesser in H0.
elim H0 => key locked H0.
exists key locked.
smt(get_setE).
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
  gm_to_next_key gm1                 = gm_to_next_key gm2                 /\
  gm_to_next_phys_addr gm1           = gm_to_next_phys_addr gm2           /\
  gm_to_honest_next_virt_addr gm1    = gm_to_honest_next_virt_addr gm2    /\
  gm_to_honest_virt_map gm1          = gm_to_honest_virt_map gm2          /\
  gm_to_malicious_next_virt_addr gm1 = gm_to_malicious_next_virt_addr gm2 /\
  gm_to_malicious_virt_map gm1       = gm_to_malicious_virt_map gm2       /\
  (* *)
  fdom (gm_to_phys_map gm1) = fdom (gm_to_phys_map gm2)                   /\
  (gm_to_honest_virt_map gm1).[cell_hon_virt_addr] = Some cell_phys_addr  /\
  (gm_to_phys_map gm1).[cell_phys_addr] =
  Some (Cell {|key = key; cont = cont; locked = true|})                   /\
  (gm_to_phys_map gm2).[cell_phys_addr] =
  Some (Cell {|key = key; cont = true; locked = true|})                   /\
  (* *)
  (forall (phys_addr' : addr),
   phys_addr' \in gm_to_phys_map gm1 => phys_addr' <> cell_phys_addr =>
   (gm_to_phys_map gm1).[phys_addr'] =
   (gm_to_phys_map gm2).[phys_addr'])                                     /\
  (forall (mal_virt_addr : addr),
   mal_virt_addr \in gm_to_malicious_virt_map gm1 =>
   let phys_addr' = 
     oget (gm_to_malicious_virt_map gm1).[mal_virt_addr] in
   oget (gm_to_phys_map gm1).[phys_addr'] <> Key key).

lemma gm_rel_invar_chooser_malic_key_not_accessible_gm2
      (gm1 gm2 : gm, cell_hon_virt_addr cell_phys_addr : addr, key : key,
       cont : bool) :
  gm_invar gm1 =>
  gm_rel_invar_chooser gm1 gm2 cell_hon_virt_addr cell_phys_addr key cont =>
  (forall (mal_virt_addr : addr),
   mal_virt_addr \in gm_to_malicious_virt_map gm2 =>
   let phys_addr' = 
     oget (gm_to_malicious_virt_map gm2).[mal_virt_addr] in
   oget (gm_to_phys_map gm2).[phys_addr'] <> Key key).
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
if => //.
auto.
if => //.
auto; progress; smt(get_setE).
auto; progress; smt(get_setE).
auto.
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
proc; inline*; auto; smt().
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
if => //.
if => //.
auto.
auto.
if; first smt().
match; first 2 smt().
move => key1 key2.
auto; smt(get_setE fdom_set).
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
proc; inline*; auto; smt().
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
if => //.
auto.
if; first smt().
sp 2 2.
if; first smt().
sp 2 2.
if; first smt().
auto; progress; first 7 smt().
smt(get_setE fdom_set).
smt().
smt(get_setE fdom_set).
smt(get_setE fdom_set).
rewrite /gm_to_phys_map /=.
case (phys_addr' = Memory.next_phys_addr{1}) => [eq_pa'_npa | neq_pa'_npa].
rewrite 2!get_setE eq_pa'_npa.
have -> // : Memory.next_phys_addr{2} = Memory.next_phys_addr{1}.
smt(). smt().
rewrite 2!get_setE.
have -> /= : Memory.next_phys_addr{2} = Memory.next_phys_addr{1}.
smt().
rewrite neq_pa'_npa /=; smt(fdomP).
smt(get_setE).
auto.
auto.
auto.
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
proc; inline*; auto; smt().
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

(* lemmas regarding the honest part of the simulator and its
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
if; first smt().
auto; smt(get_setE).
auto.
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
    if (cell_addr \in Memory.honest_virt_map) {
      phys_addr <- oget Memory.honest_virt_map.[cell_addr];
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
    if (cell_addr \in Memory.honest_virt_map) {
      phys_addr <- oget Memory.honest_virt_map.[cell_addr];
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
auto; progress; (apply gm_eqP; first 2 smt()); last 4 smt().
rewrite /gm_to_phys_map /=.
have -> :
  oget Memory.honest_virt_map{hr}.[cell_addr{hr}] =
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
rcondt{1} 1; first auto.
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
rcondt{1} 1; first auto.
if => //; auto; smt().
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
    (gm_to_honest_virt_map (glob Memory){1}).[oget res{1}] = Some phys_addr /\
    (gm_to_phys_map (glob Memory){1}).[phys_addr] = Some (Cell cell) /\
    cell.`cont = cont /\ cell.`locked = false))].
proof.
conseq
  (_ :
   _ ==>
   ={res, glob Memory} /\
   (res{1} <> None =>
    (exists (phys_addr : addr, cell : cell),
    (gm_to_honest_virt_map (glob Memory){1}).[oget res{1}] = Some phys_addr /\
    (gm_to_phys_map (glob Memory){1}).[phys_addr] = Some (Cell cell) /\
    cell.`cont = cont /\ cell.`locked = false)))
  (_ : gm_invar (glob Memory) ==> gm_invar (glob Memory))
  (_ : _ ==> _) => //.
apply HonestMemory.party_memory_unlock_cell_gm_invar.
proc; inline *; sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
if => //.
sp 2 2.
if => //.
sp 2 2.
if => //.
auto => &1 &2 |>.
rewrite /gm_to_honest_virt_map /gm_to_phys_map /= get_set_sameE.
smt(get_setE).
auto.
auto.
auto.
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
case
  (ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
   Memory.honest_next_virt_addr{1} =
   gm_to_honest_next_virt_addr gm + 1 /\
   Memory.honest_virt_map{1} =
   (gm_to_honest_virt_map gm)
      .[gm_to_honest_next_virt_addr gm <- gm_to_next_phys_addr gm] /\
   key_addr{1} = gm_to_honest_next_virt_addr gm /\
   Memory.malicious_next_virt_addr{1} = gm_to_malicious_next_virt_addr gm /\
   Memory.malicious_virt_map{1} = gm_to_malicious_virt_map gm /\
   (forall (mal_virt_addr : addr),
    mal_virt_addr \in gm_to_malicious_virt_map gm =>
    let phys_addr' = 
      oget (gm_to_malicious_virt_map gm).[mal_virt_addr] in
    oget Memory.phys_map{1}.[phys_addr'] <> Key (gm_to_next_key gm))).
call{1} (HonestMemory.party_memory_create_key_phl gm).
call{2} (HonestMemory.party_memory_create_key_phl gm).
auto; smt(gm_invar_old_mal_virt_addr_does_not_give_new_key).
exlim (glob Memory){1}, key_addr{1}, choice{1} => gm' key_addr' choice'.
call{1} (HonestMemory.party_memory_create_cell_phl gm' key_addr' choice').
call{2} (HonestMemory.party_memory_create_cell_phl gm' key_addr' true).
auto; progress [-delta].
smt(get_setE).
apply
  (RI_Chooser_WaitCellAddrToOther _ _ _ _ _ choice{2}
   (gm_to_honest_next_virt_addr gm) (gm_to_honest_next_virt_addr gm + 1)
   (gm_to_next_phys_addr gm + 1) (gm_to_next_key gm)).
smt(fdom_set get_setE).
wp.
((match => //; first auto; smt(RI_Chooser_WaitChoiceFromAdv));
  first auto; exfalso; smt());
  auto; smt(RI_Chooser_WaitChoiceFromAdv).
call (malicious_party_gm_invar_from_adv Malicious).
auto; smt(RI_Chooser_WaitChoiceFromAdv).
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_final_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr guess,
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr guess).
elim* => choice' key_addr' guess'.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   choice' key_addr' guess' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitToOtherKeyAddr {1} 3; first auto; smt().
match IPS_Chooser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
case
  (exists (result: bool),
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
match HPS_Chooser_WaitToAdvResult {1} 3; first auto; smt().
match IPS_Chooser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_chooser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Chooser_WaitErrorToAdv /#.
case
  (ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Chooser_Final /#.
case
  (ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}) => /=.
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitGuessFromAdv _ _ _ _ _) /#.
case
  (exists (guess : bool),
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess).
elim* => guess'.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitFromOtherCellAddr {1} 1; first auto; smt().
match IPS_Guesser_WaitSimChoice {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess' cell_addr' cell_phys_addr' cont' result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitToOtherGuess {1} 1; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 1; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
call
  (malicious_party_gm_invar_guesser_from_adv
   cell_addr' cell_phys_addr' cont' Malicious).
auto; progress [-delta]; first 9 smt().
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess' cell_addr' cell_phys_addr' cont' result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitFromOtherKeyAddr {1} 1; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 1; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
call
  (malicious_party_gm_invar_guesser_from_adv
   cell_addr' cell_phys_addr' cont' Malicious).
auto; progress [-delta]; first 9 smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (result : bool),
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
conseq
  (_ :
   ={party, msg, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.from_adv.
sp.
match HPS_Guesser_WaitToAdvResult {1} 1; first auto; smt().
match IPS_Guesser_WaitToAdvResult {2} 1; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
call (malicious_party_gm_invar_from_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitErrorToAdv _ _ _ _ _) /#.
case
  (ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_Final _ _ _ _ _) /#.
exfalso => &1 &2 [#] _ _ _ _ _ [] /#.
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
case
  (ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Chooser_WaitChoiceFromAdv /#.
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_final_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr guess,
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr guess).
elim* => choice' key_addr' guess'.
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
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToOtherKeyAddr {1} 2; first auto; smt().
match IPS_Chooser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
case
  (exists (result: bool),
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_result_to_adv
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToAdvResult {1} 2; first auto; smt().
match IPS_Chooser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta]; first smt().
rewrite RI_Chooser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_chooser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
match => //.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_chooser_wait_error_to_adv
   Honest.Honest.state{1} IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} ==>
   _) => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Chooser_WaitToAdvError {1} 2; first auto; smt().
match IPS_Chooser_WaitToAdvError {2} 2; first auto; smt().
auto; progress [-delta].
rewrite RI_Chooser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
case
  (ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Chooser_Final /#.
case
  (ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}) => /=.
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Guesser_WaitGuessFromAdv /#.
case
  (exists (guess : bool),
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess).
elim* => guess'.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitFromOtherCellAddr {1} 2; first auto; smt().
match IPS_Guesser_WaitSimChoice {2} 2; first auto; smt().
auto; progress [-delta].
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
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
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitToOtherGuess {1} 2; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
call
  (malicious_party_gm_invar_guesser_to_adv
   cell_addr' cell_phys_addr' cont' Malicious).
auto; progress [-delta]; first 9 smt().
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
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
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitFromOtherKeyAddr {1} 2; first auto; smt().
match IPS_Guesser_WaitSimOK {2} 2; first auto; smt().
auto; progress [-delta].
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
call
  (malicious_party_gm_invar_guesser_to_adv
   cell_addr' cell_phys_addr' cont' Malicious).
auto; progress [-delta]; first 9 smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (result : bool),
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
conseq
  (_ :
   ={party, glob Malicious} /\
   ={to_malicious_queue, to_honest_queue}(RealProtocol, Simulator) /\
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result' ==>
   _) => //.
match => //.
inline RealProtocol(Honest.Honest, Malicious).H.to_adv.
match HPS_Guesser_WaitToAdvResult {1} 2; first auto; smt().
match IPS_Guesser_WaitToAdvResult {2} 2; first auto; smt().
auto; progress [-delta]; first smt().
rewrite RI_Guesser_Final /#.
call (malicious_party_gm_invar_to_adv Malicious).
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Guesser_WaitErrorToAdv /#.
case
  (ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Guesser_Final /#.
exfalso => &1 &2 [#] _ _ _ _ [] /#.
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
case
  (ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Chooser_WaitChoiceFromAdv /#.
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice' key_addr' cell_addr' cell_phys_addr' key'.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_final_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice key_addr cell_addr cell_phys_addr key.
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
case
  (exists choice key_addr guess,
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr guess).
elim* => choice' key_addr' guess'.
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
auto; progress [-delta]; first 8 smt().
rewrite
  (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
   choice' key_addr' guess') /#.
case
  (exists (result: bool),
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_chooser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
case
  (ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Chooser_Final /#.
case
  (ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}) => /=.
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Guesser_WaitGuessFromAdv /#.
case
  (exists (guess : bool),
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess).
elim* => guess'.
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
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
auto; progress [-delta]; first 9 smt().
rewrite
  (RI_Guesser_WaitGuessToOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
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
auto; progress [-delta]; first 9 smt().
rewrite
  (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
   guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (result : bool),
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Guesser_WaitErrorToAdv /#.
case
  (ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite RI_Guesser_Final /#.
exfalso => &1 &2 [#] _ _ _ _ [] /#.
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
case
  (ri_chooser_wait_choice_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
(auto; progress [-delta]; first 8 smt());
  rewrite RI_Chooser_WaitChoiceFromAdv /#.
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_cell_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice' key_addr' cell_addr' cell_phys_addr' key'.
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
case
  (exists choice' key_addr' cell_addr' cell_phys_addr' key',
   ri_chooser_wait_guess_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice' key_addr' cell_addr'
   cell_phys_addr' key').
elim* => choice' key_addr' cell_addr' cell_phys_addr' key'.
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
auto; progress [-delta]; first 3 smt().
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_wait_error_to_adv_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice' key_addr' cell_addr' cell_phys_addr' key'.
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
case
  (exists choice key_addr cell_addr cell_phys_addr key,
   ri_chooser_final_gm_rel_invar_chooser Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr cell_addr
   cell_phys_addr key).
elim* => choice' key_addr' cell_addr' cell_phys_addr' key'.
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
case
  (exists choice key_addr guess,
   ri_chooser_wait_key_addr_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} choice key_addr guess).
elim* => choice' key_addr' guess'.
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
(auto; progress [-delta]; first 8 auto; smt());
  rewrite
    (RI_Chooser_WaitKeyAddrToOther _ _ _ _ _
     choice' key_addr' guess') /#.
case
  (exists (result: bool),
   ri_chooser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
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
auto; progress [-delta]; first 8 auto; smt().
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
rewrite (RI_Chooser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_chooser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
auto; progress [-delta]; first 8 smt().
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
rewrite (RI_Chooser_WaitErrorToAdv _ _ _ _ _) /#.
case
  (ri_chooser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
(auto; progress [-delta]; first 8 smt());
  rewrite (RI_Chooser_Final _ _ _ _ _) /#.
case
  (ri_guesser_wait_guess_from_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}) => /=.
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
(auto; progress [-delta]; first 8 smt());
  rewrite (RI_Guesser_WaitGuessFromAdv _ _ _ _ _) /#.
case
  (exists (guess : bool),
   ri_guesser_wait_cell_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} guess).
elim* => guess'.
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
   guess{1} cell_addr{2} (oget Memory.honest_virt_map{1}.[cell_addr{2}])
   cell.`cont (guess{2} = cell.`cont)); smt(get_some).
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
(auto; progress [-delta]; first 8 smt());
  rewrite (RI_Guesser_WaitCellAddrFromOther _ _ _ _ _ guess') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_guess_to_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
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
(auto; progress [-delta]; first 9 smt());
  rewrite
    (RI_Guesser_WaitGuessToOther _ _ _ _ _
     guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (guess : bool, cell_addr : addr, cell_phys_addr : addr,
           cont : bool, result : bool),
   ri_guesser_wait_key_addr_from_other Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}
   guess cell_addr cell_phys_addr cont result).
elim* => guess' cell_addr' cell_phys_addr' cont' result'.
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
    (gm_to_honest_virt_map
     (glob Memory){1}).[oget unlocked_cell_addr_opt{1}] = Some phys_addr /\
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
(auto; progress [-delta]; first 9 smt());
  rewrite
    (RI_Guesser_WaitKeyAddrFromOther _ _ _ _ _
     guess' cell_addr' cell_phys_addr' cont' result') /#.
case
  (exists (result : bool),
   ri_guesser_wait_result_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2} result).
elim* => result'.
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
(auto; progress [-delta]; first 8 smt());
  rewrite (RI_Guesser_WaitResultToAdv _ _ _ _ _ result') /#.
case
  (ri_guesser_wait_error_to_adv Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
(auto; progress [-delta]; first 8 smt());
  rewrite (RI_Guesser_WaitErrorToAdv _ _ _ _ _) /#.
case
  (ri_guesser_final Honest.Honest.state{1}
   IdealProtocol.state{2} Simulator.H.state{2}
   (glob Memory){1} (glob Memory){2}).
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
(auto; progress [-delta]; first 8 smt());
  rewrite (RI_Guesser_Final _ _ _ _ _) /#.
exfalso => &1 &2 [#] _ _ _ _ [] /#.
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

(* we have perfect security: the adversary has no chance of
   distinguishing the real and ideal worlds

   assuming we resrict ourselves to Malicious and Adv being
   non-probabilistic, we can conclude that the real experiment results
   in true iff the ideal experiement does *)

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
