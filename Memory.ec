(* Physical and Party-indexed Virtual Memories

   *** can be used for multiple two party protocols, where one
   party is honest and one is (potentially) malicious ***

   immutable objects (keys and cells) are stored in the physical
   memory, indexed by addresses (non-negative integers)

   each of the honest and malicious parties has a virtual memory
   mapping virtual addresses (non-negative integers) to physical ones

   there is a way for a party to translate one of its virtual
   addresses into a virtual address of the other party, which is
   added to the other party's virtual address table, and points to
   the same physical address

   operations are non-destructive, and so create new objects

   keys are unforgeable and are represented as unique non-negative
   integers

   cells are records consisting of a key (needed to unlock it),
   a boolean contents and a locked status

   unlocking creates a new, unlocked cell; the contents of
   an unlocked cell can be retieved without a key *)

prover ["Z3" "Alt-Ergo"].  (* both must succeed for all smt goals *)

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

(* addresses *)

type addr = int.

(* interface of memory *)

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

  var next_virt_addr : (party, addr) fmap
  var virt_map : (party, (addr, addr) fmap) fmap

  proc init() : unit = {
    next_key       <- 0;
    next_phys_addr <- 0;
    phys_map       <- empty;
    next_virt_addr <- empty.[Honest <- 0].[Malicious <- 0];
    virt_map       <- empty.[Honest <- empty].[Malicious <- empty];
  }

  proc phys_alloc(obj : object) : addr = {
    var r : addr;
    phys_map.[next_phys_addr] <- obj;
    r <- next_phys_addr;
    next_phys_addr <- next_phys_addr + 1;
    return r;
  }

  proc virt_alloc(pty : party, phys_addr : addr) : addr = {
    var next : addr <- oget (next_virt_addr.[pty]);
    virt_map.[pty] <- (oget virt_map.[pty]).[next <- phys_addr];
    next_virt_addr.[pty] <- next + 1;
    return next;
  }

  proc trans_virt_addr(pty : party, addr : addr) : addr option = {
    var r : addr option;
    var phys_addr, other_virt_addr : addr;
    if (addr \in oget virt_map.[pty]) {
      phys_addr <- oget (oget virt_map.[pty]).[addr];
      other_virt_addr <@ virt_alloc(other pty, phys_addr);
      r <- Some other_virt_addr;
    }
    else { r <- None; }
    return r;
  }

  proc create_key(pty : party) : addr = {
    var key : key <- next_key;
    var phys_addr, virt_addr : addr;
    next_key <- next_key + 1;
    phys_addr <@ phys_alloc(Key key);
    virt_addr <@ virt_alloc(pty, phys_addr);
    return virt_addr;
  }

  proc is_key(pty : party, key_addr : addr) : bool = {
    var r : bool;
    if (key_addr \in oget virt_map.[pty]) {
      r <- is_key (oget phys_map.[oget (oget virt_map.[pty]).[key_addr]]);
    }
    else { r <- false; }
    return r;
  }

  proc create_cell(pty : party, key_addr : addr, b : bool) : addr option = {
    var r : addr option;
    var phys_addr, virt_addr : addr;
    if (key_addr \in oget virt_map.[pty]) {
      match oget phys_map.[oget (oget virt_map.[pty]).[key_addr]] with
      | Key key => {
          phys_addr <@
            phys_alloc(Cell {|key = key; cont = b; locked = true|});
          virt_addr <@ virt_alloc(pty, phys_addr);
          r <- Some virt_addr;
        }
      | Cell _  => { r <- None; }
      end;
    }
    else { r <- None; }
    return r;
  }

  proc is_cell(pty : party, cell_addr : addr) : bool = {
    var r : bool;
    if (cell_addr \in oget virt_map.[pty]) {
      r <- is_cell (oget phys_map.[oget (oget virt_map.[pty]).[cell_addr]]);
    }
    else { r <- false; }
    return r;
  }

  proc unlock_cell(pty : party, cell_addr : addr, key_addr : addr)
         : addr option = {
    var r : addr option; var phys_addr, virt_addr : addr;
    var obj_cell, obj_key : object; var cell : cell; var key : key;
    if (cell_addr \in oget virt_map.[pty] /\
        key_addr  \in oget virt_map.[pty]) {
      obj_cell <- oget phys_map.[oget (oget virt_map.[pty]).[cell_addr]];
      obj_key  <- oget phys_map.[oget (oget virt_map.[pty]).[key_addr]];
      if (is_cell obj_cell /\ is_key obj_key) {
        cell <- oget (get_as_Cell obj_cell);
        key  <- oget (get_as_Key obj_key);
        if (cell.`key = key) {
          cell <- {|cell with locked = false|};
          phys_addr <@ phys_alloc(Cell cell);
          virt_addr <@ virt_alloc(pty, phys_addr);
          r <- Some virt_addr;
        }
        else { r <- None; }
      }
      else { r <- None; }
    }
    else { r <- None; }
    return r;
  }

  proc contents_cell(pty : party, cell_addr : addr) : bool option = {
    var r : bool option;
    if (cell_addr \in oget virt_map.[pty]) {
      match oget phys_map.[oget (oget virt_map.[pty]).[cell_addr]] with
      | Key _     => { r <- None; }
      | Cell cell => {
          if (! cell.`locked) { r <- Some cell.`cont; }
          else { r <- None; }
        }
      end;
    }
    else { r <- None; }
    return r;
  }
}.

(* glob Memory is the tuple type with the global variables of Memory
   in alphabetical order; this is planned by the EasyCrypt developers
   to be turned into a more usable record type *)

type gm = glob Memory.

op gm_to_next_key       (gm : gm)  : key                             = gm.`1.
op gm_to_next_phys_addr (gm : gm)  : addr                            = gm.`2.
op gm_to_phys_map       (gm : gm)  : (addr, object) fmap             = gm.`4.
op gm_to_next_virt_addr (gm : gm)  : (party, addr) fmap              = gm.`3.
op gm_to_virt_map       (gm : gm)  : (party, (addr, addr) fmap) fmap = gm.`5.

lemma gm_eqP (gm1 gm2 : gm) :
  gm_to_next_key gm1 = gm_to_next_key gm2 =>
  gm_to_next_phys_addr gm1 = gm_to_next_phys_addr gm2 =>
  gm_to_phys_map gm1 = gm_to_phys_map gm2 =>
  gm_to_next_virt_addr gm1 = gm_to_next_virt_addr gm2 =>
  gm_to_virt_map gm1 = gm_to_virt_map gm2 =>
  gm1 = gm2.
proof. smt(). qed.

(* invariant respected by the procedures of Memory *)

op gm_invar_pre (gm : gm) : bool =
  (forall (pty : party), pty \in gm_to_next_virt_addr gm) /\
  (forall (pty : party), pty \in gm_to_virt_map gm) /\
  0 <= gm_to_next_key gm /\
  0 <= gm_to_next_phys_addr gm /\
  (forall (pty : party),
   0 <= oget (gm_to_next_virt_addr gm).[pty]) /\
  (forall (addr : addr),
   addr \in gm_to_phys_map gm =>
   0 <= addr < gm_to_next_phys_addr gm) /\
  (forall (pty : party, addr : addr),
   addr \in oget (gm_to_virt_map gm).[pty] =>
   0 <= addr < oget (gm_to_next_virt_addr gm).[pty]) /\
  (forall (pty : party, addr : addr),
   rng (oget (gm_to_virt_map gm).[pty]) addr =>
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

lemma gm_invar_old_virt_addr_does_not_give_new_key
      (gm : gm, pty : party, virt_addr : addr) :
  gm_invar gm => virt_addr \in oget (gm_to_virt_map gm).[pty] =>
  let key = gm_to_next_key gm in
  let phys_addr = oget (oget (gm_to_virt_map gm).[pty]).[virt_addr] in
  oget (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Key key].[phys_addr] <>
  Key key.
proof.
move => gm_invar_gm virt_addr_in_dom_virt_map_of_gm /=.
have H1 :
  oget (oget (gm_to_virt_map gm).[pty]).[virt_addr] \in
  gm_to_phys_map gm by smt(get_some).
have H2 :
  oget (oget (gm_to_virt_map gm).[pty]).[virt_addr] <>
  gm_to_next_phys_addr gm by smt(get_some).
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
   gm_invar (glob Memory) /\
   Memory.next_key       = 0 /\
   Memory.next_phys_addr = 0 /\
   Memory.phys_map       = empty /\
   Memory.next_virt_addr = empty.[Honest <- 0].[Malicious <- 0] /\
   Memory.virt_map       = empty.[Honest <- empty].[Malicious <- empty]].
proof.
proc; auto; smt(mem_set mem_empty mem_rng_empty get_setE get_some).
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
   Memory.next_virt_addr = gm_to_next_virt_addr gm /\
   Memory.virt_map = gm_to_virt_map gm /\
   (* changed *)
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map = (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Key key] /\
   res = gm_to_next_phys_addr gm].
proof.
proc; auto; progress; smt(get_setE).
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
   Memory.next_virt_addr = gm_to_next_virt_addr gm /\
   Memory.virt_map = gm_to_virt_map gm /\
   (* changed *)
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map = (gm_to_phys_map gm).[gm_to_next_phys_addr gm <- Cell cell] /\
   res = gm_to_next_phys_addr gm].
proof.
proc; auto; progress; smt(get_setE).
qed.

lemma memory_virt_alloc (gm : gm, pty' : party, phys_addr' : addr) :
  hoare
  [Memory.virt_alloc :
   pty = pty' /\ phys_addr = phys_addr' /\ phys_addr' \in Memory.phys_map /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   Memory.next_virt_addr.[other pty'] = (gm_to_next_virt_addr gm).[other pty'] /\
   Memory.virt_map.[other pty'] = (gm_to_virt_map gm).[other pty'] /\
   (* changed *)
   oget Memory.next_virt_addr.[pty'] =
     oget (gm_to_next_virt_addr gm).[pty'] + 1 /\
   oget Memory.virt_map.[pty'] =
   (oget (gm_to_virt_map gm).[pty'])
     .[oget (gm_to_next_virt_addr gm).[pty'] <- phys_addr'] /\
   res = oget (gm_to_next_virt_addr gm).[pty']].
proof.
proc; auto; smt(mem_set rng_set_new get_some get_setE).
qed.

lemma memory_trans_virt_addr_ll :
  islossless Memory.trans_virt_addr.
proof. islossless. qed.

lemma memory_trans_virt_addr_gm_invar :
  hoare
  [Memory.trans_virt_addr :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; inline*; auto.
(progress; first 8 smt(get_setE get_some)); last 5 smt(get_setE get_some).
rewrite /gm_to_next_virt_addr /=; smt(get_setE get_some).
qed.

lemma memory_trans_virt_addr (gm : gm, pty' : party, addr' : addr) :
  hoare
  [Memory.trans_virt_addr :
   pty = pty' /\ addr = addr' /\
   addr \in oget Memory.virt_map.[pty] /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   Memory.next_virt_addr.[pty'] = (gm_to_next_virt_addr gm).[pty'] /\
   Memory.virt_map.[pty'] = (gm_to_virt_map gm).[pty'] /\
   (* changed *)
   let phys_addr = oget (oget (Memory.virt_map.[pty'])).[addr'] in
   let next_virt_addr_other = oget (gm_to_next_virt_addr gm).[other pty'] in
   oget Memory.next_virt_addr.[other pty'] =
     next_virt_addr_other + 1 /\
   oget Memory.virt_map.[other pty'] =
   (oget (gm_to_virt_map gm).[other pty'])
     .[next_virt_addr_other <- phys_addr] /\
   res = Some next_virt_addr_other].
proof.
proc.
if.
sp; wp.
exlim (glob Memory), phys_addr => gm' pa'.
call (memory_virt_alloc gm' (other pty') pa').
auto; smt(get_setE get_some).
auto; smt().
qed.

lemma memory_trans_virt_addr_bad (gm : gm) :
  hoare
  [Memory.trans_virt_addr :
   addr \notin oget Memory.virt_map.[pty] /\
   glob Memory = gm /\ gm_invar gm ==>
   glob Memory = gm /\ gm_invar (glob Memory)].
proof.
proc; inline*; if; auto.
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
   oget Memory.next_virt_addr.[pty'] =
   oget (gm_to_next_virt_addr gm).[pty'] + 1 /\
   oget Memory.virt_map.[pty'] =
   (oget (gm_to_virt_map gm).[pty'])
     .[oget (gm_to_next_virt_addr gm).[pty'] <-
       gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other pty'] = (gm_to_next_virt_addr gm).[other pty'] /\
   Memory.virt_map.[other pty'] = (gm_to_virt_map gm).[other pty'] /\
   res = oget (gm_to_next_virt_addr gm).[pty']].
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
   Memory.next_virt_addr = gm_to_next_virt_addr gm /\
   Memory.virt_map = gm_to_virt_map gm).
exlim (glob Memory) => gm'.
exlim key => key'.
call (memory_phys_alloc_key gm' key').
auto; smt().
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_virt_alloc gm' pty' phys_addr').
auto; smt(mem_set get_setE).
qed.

op key_addr_good (pty : party, gm : gm, key_addr : addr) : bool =
  key_addr \in oget (gm_to_virt_map gm).[pty] /\
  is_key
  (oget
   ((gm_to_phys_map gm)
      .[oget (oget (gm_to_virt_map gm).[pty]).[key_addr]])).

op key_addr_to_key (pty : party, gm : gm, key_addr : addr) : key =
  oget
  (get_as_Key
   (oget
    ((gm_to_phys_map gm)
       .[oget (oget (gm_to_virt_map gm).[pty]).[key_addr]]))).

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
qed.

lemma memory_create_cell_gm_invar :
  hoare
  [Memory.create_cell :
   gm_invar (glob Memory) ==> gm_invar (glob Memory)].
proof.
proc; if.
match.
(inline*; auto; progress; first 11 smt(mem_set get_setE oget_some));
  last 2 smt(get_setE oget_some).
move : H2; rewrite /gm_to_phys_map /= get_setE.
case (addr = Memory.next_phys_addr{hr}) => /= [addr_eq_npa <- | addr_ne_npa].
exists (oget (oget Memory.virt_map{hr}.[pty{hr}]).[key_addr{hr}]).
smt(get_setE oget_some some_oget).
smt(get_setE oget_some some_oget).
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
   Memory.phys_map =
   (gm_to_phys_map gm)
      .[gm_to_next_phys_addr gm <-
        Cell
        {|key = key_addr_to_key pty' gm key_addr';
          cont = b'; locked = true|}] /\
   oget Memory.next_virt_addr.[pty'] =
   oget (gm_to_next_virt_addr gm).[pty'] + 1 /\
   oget Memory.virt_map.[pty'] =
   (oget (gm_to_virt_map gm).[pty'])
      .[oget (gm_to_next_virt_addr gm).[pty'] <- gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other pty'] = (gm_to_next_virt_addr gm).[other pty'] /\
   Memory.virt_map.[other pty'] = (gm_to_virt_map gm).[other pty'] /\
   res = Some (oget (gm_to_next_virt_addr gm).[pty'])].
proof.
proc => /=.
rcondt 1; first auto; smt().
match Key 1; first auto; smt().
exlim key => key'.
seq 1 :
  (pty = pty' /\ key_addr' \in oget (gm_to_virt_map gm).[pty'] /\
   key_addr_good pty' gm key_addr' /\
   key' = key_addr_to_key pty' gm key_addr' /\
   gm_invar gm /\ phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell {|key = key'; cont = b'; locked = true|}] /\
   Memory.next_virt_addr = gm_to_next_virt_addr gm /\
   Memory.virt_map = gm_to_virt_map gm).
call (memory_phys_alloc_cell gm {|key = key'; cont = b'; locked = true|}).
auto; progress [-delta];
  have /# :
    Memory.phys_map{hr}
      .[oget (oget Memory.virt_map{hr}.[pty{hr}]).[key_addr{hr}]] =
    Some (Key key{hr}) by smt(get_some).
wp.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_virt_alloc gm' pty' phys_addr').
auto => /> /= ; progress; smt(mem_set get_setE).
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
   Memory.next_virt_addr = gm_to_next_virt_addr gm /\
   Memory.virt_map = gm_to_virt_map gm /\
   res = None].
proof.
proc => /=; if.
match Cell 1; auto; smt().
auto.
qed.

op cell_addr_good (pty : party, gm : gm, cell_addr : addr) : bool =
  cell_addr \in oget (gm_to_virt_map gm).[pty] /\
  is_cell
  (oget
   ((gm_to_phys_map gm)
      .[oget (oget (gm_to_virt_map gm).[pty]).[cell_addr]])).

op cell_addr_to_cell (pty : party, gm : gm, cell_addr : addr) : cell =
  oget
  (get_as_Cell
   (oget
    ((gm_to_phys_map gm)
       .[oget (oget (gm_to_virt_map gm).[pty]).[cell_addr]]))).

lemma good_cell_addr_key_in_mem (pty : party, gm : gm, cell_addr : addr) :
  gm_invar gm => cell_addr_good pty gm cell_addr =>
  exists (key_addr : addr),
  (gm_to_phys_map gm).[key_addr] =
  Some (Key (cell_addr_to_cell pty gm cell_addr).`key).
proof.
move => gmi_gm.
rewrite /cell_addr_good /cell_addr_to_cell.
move => [H1 H2].
have [cell H3] :
  exists cell,
  oget
  (gm_to_phys_map gm)
    .[oget (oget (gm_to_virt_map gm).[pty]).[cell_addr]] =
  Cell cell by smt().
rewrite /get_as_Cell H3 /=.
have /# :
  (gm_to_phys_map gm).[oget (oget (gm_to_virt_map gm).[pty]).[cell_addr]] =
  Some (Cell cell) by smt(get_some).
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
proc; if; last auto.
sp; if; last auto.
sp; if; last auto.
sp; wp; elim* => cell0; inline*.
(auto; progress; first 7 smt(get_setE)); last 6 smt(oget_some get_setE).
move : H5; rewrite /gm_to_virt_map /= get_setE /=; smt(mem_set).
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
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell
       {|(cell_addr_to_cell pty' gm cell_addr') with locked = false|}] /\
   oget Memory.next_virt_addr.[pty'] =
   oget (gm_to_next_virt_addr gm).[pty'] + 1 /\
   oget Memory.virt_map.[pty'] =
   (oget (gm_to_virt_map gm).[pty'])
     .[oget (gm_to_next_virt_addr gm).[pty'] <- gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other pty'] =
   (gm_to_next_virt_addr gm).[other pty'] /\
   Memory.virt_map.[other pty'] =  (gm_to_virt_map gm).[other pty'] /\
   res = Some (oget (gm_to_next_virt_addr gm).[pty'])].
proof.
proc.
rcondt 1; first auto; smt().
sp 2.
rcondt 1; first auto; smt().
sp 2.
rcondt 1; first auto; smt().
sp 1.
elim* => cell' /=.
seq 1 :
  (pty = pty' /\ gm_invar gm /\
   cell' = cell_addr_to_cell pty gm cell_addr' /\
   cell_addr_good pty gm cell_addr' /\
   phys_addr = gm_to_next_phys_addr gm /\
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm + 1 /\
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell {|cell' with locked = false|}] /\
   Memory.next_virt_addr = gm_to_next_virt_addr gm /\
   Memory.virt_map = gm_to_virt_map gm).
call (memory_phys_alloc_cell gm {|cell' with locked = false|}).
auto; smt().
wp => /=.
exlim (glob Memory) => gm'.
exlim phys_addr => phys_addr'.
call (memory_virt_alloc gm' pty' phys_addr').
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
if; [sp; if; [sp; if; [exfalso; smt() | auto] | auto] | auto].
qed.

lemma memory_contents_cell_ll : islossless Memory.contents_cell.
proof.
islossless.
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
proc => /=.
if.
case
  (exists (key : key),
   oget Memory.phys_map.[oget (oget Memory.virt_map.[pty']).[cell_addr]] =
   Key key).
match Key 1; auto.
match Cell 1; first auto; smt().
rcondf 1; auto; smt().
auto.
qed.

(* a party's interface to the memory; like the corresponding functions
   of MEMORY, but where the party is implicit, and initialization is
   not possible *)

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
   addr = addr' /\ addr \in oget Memory.virt_map.[party] /\
   glob Memory = gm /\ gm_invar gm ==>
   gm_invar (glob Memory) /\
   (* unchanged *)
   Memory.next_key = gm_to_next_key gm /\
   Memory.next_phys_addr = gm_to_next_phys_addr gm /\
   Memory.phys_map = gm_to_phys_map gm /\
   Memory.next_virt_addr.[party] = (gm_to_next_virt_addr gm).[party] /\
   Memory.virt_map.[party] = (gm_to_virt_map gm).[party] /\
   (* changed *)
   let phys_addr = oget (oget (Memory.virt_map.[party])).[addr'] in
   let next_virt_addr_other = oget (gm_to_next_virt_addr gm).[other party] in
   oget Memory.next_virt_addr.[other party] =
     next_virt_addr_other + 1 /\
   oget Memory.virt_map.[other party] =
   (oget (gm_to_virt_map gm).[other party])
     .[next_virt_addr_other <- phys_addr] /\
   res = Some next_virt_addr_other].
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
   oget Memory.next_virt_addr.[party] =
   oget (gm_to_next_virt_addr gm).[party] + 1 /\
   oget Memory.virt_map.[party] =
   (oget (gm_to_virt_map gm).[party])
     .[oget (gm_to_next_virt_addr gm).[party] <-
       gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other party] = (gm_to_next_virt_addr gm).[other party] /\
   Memory.virt_map.[other party] = (gm_to_virt_map gm).[other party] /\
   res = oget (gm_to_next_virt_addr gm).[party]].
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
   oget Memory.next_virt_addr.[party] =
   oget (gm_to_next_virt_addr gm).[party] + 1 /\
   oget Memory.virt_map.[party] =
   (oget (gm_to_virt_map gm).[party])
     .[oget (gm_to_next_virt_addr gm).[party] <-
       gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other party] = (gm_to_next_virt_addr gm).[other party] /\
   Memory.virt_map.[other party] = (gm_to_virt_map gm).[other party] /\
   res = oget (gm_to_next_virt_addr gm).[party]] = 1%r.
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
   Memory.phys_map =
   (gm_to_phys_map gm)
      .[gm_to_next_phys_addr gm <-
        Cell
        {|key = key_addr_to_key party gm key_addr';
          cont = b'; locked = true|}] /\
   oget Memory.next_virt_addr.[party] =
   oget (gm_to_next_virt_addr gm).[party] + 1 /\
   oget Memory.virt_map.[party] =
   (oget (gm_to_virt_map gm).[party])
      .[oget (gm_to_next_virt_addr gm).[party] <- gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other party] = (gm_to_next_virt_addr gm).[other party] /\
   Memory.virt_map.[other party] = (gm_to_virt_map gm).[other party] /\
   res = Some (oget (gm_to_next_virt_addr gm).[party])].
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
   Memory.phys_map =
   (gm_to_phys_map gm)
      .[gm_to_next_phys_addr gm <-
        Cell
        {|key = key_addr_to_key party gm key_addr';
          cont = b'; locked = true|}] /\
   oget Memory.next_virt_addr.[party] =
   oget (gm_to_next_virt_addr gm).[party] + 1 /\
   oget Memory.virt_map.[party] =
   (oget (gm_to_virt_map gm).[party])
      .[oget (gm_to_next_virt_addr gm).[party] <- gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other party] = (gm_to_next_virt_addr gm).[other party] /\
   Memory.virt_map.[other party] = (gm_to_virt_map gm).[other party] /\
   res = Some (oget (gm_to_next_virt_addr gm).[party])] = 1%r.
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
   Memory.phys_map =
   (gm_to_phys_map gm)
     .[gm_to_next_phys_addr gm <-
       Cell
       {|(cell_addr_to_cell party gm cell_addr') with locked = false|}] /\
   oget Memory.next_virt_addr.[party] =
   oget (gm_to_next_virt_addr gm).[party] + 1 /\
   oget Memory.virt_map.[party] =
   (oget (gm_to_virt_map gm).[party])
     .[oget (gm_to_next_virt_addr gm).[party] <- gm_to_next_phys_addr gm] /\
   Memory.next_virt_addr.[other party] =
   (gm_to_next_virt_addr gm).[other party] /\
   Memory.virt_map.[other party] =  (gm_to_virt_map gm).[other party] /\
   res = Some (oget (gm_to_next_virt_addr gm).[party])].
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
