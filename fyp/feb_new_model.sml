(* 

  The same model from model.sml but with no hard deadlines
  variables such as td, tmine. After removing these deadlines,
  the model will be much simpler and hence easier to verify the
  system.

  To think before doing anything, what to be done with the register?
  Register is preventing us with generalising our model to all
  possible transactions.

*)

(*

  Modeling issues are coming up as expected.
  Need to re-evaluate what should are shouldn't be modelled
  depending on our properties of interest.

*)

load "stringTheory";

open HolKernel Parse boolLib bossLib;

val _ = new_theory "smart_contract";

open  arithmeticTheory 
      boolTheory 
      combinTheory  
      indexedListsTheory
      listLib 
      listTheory 
      metisLib 
      numLib
      numTheory 
      optionTheory
      pairTheory 
      pred_setTheory 
      prim_recTheory
      rich_listTheory 
      satTheory
      stringTheory
      listSyntax;


(* Product Type definition: *)
(* Address and Alias *)
Datatype:
  user = <| n:num ; a:string |>
End

Datatype:
  tx = DATA user | NO_DATA
End

Definition HD_def:
  (HD [] = NO_DATA) /\
  (HD (x::xs) = DATA x)
End

Definition RM_HD_def:
  (RM_HD [] = []) /\
  (RM_HD (x::xs) = xs)
End

(* TRANSACTIONS

  The transaction model contains two parallel process, one is
  used for getting the tx from the network and adding it to
  pending transactions, and the other process is used to send
  the tx for mining.

*)

val TRANSACTIONS_def = Define `
  TRANSACTIONS pending_tx mine =
    !t. (case pending_tx t of
           []      => (mine t = NO_DATA) /\ (pending_tx (t+1) = [])
         | (x::xs) => (mine t = DATA x) /\ (pending_tx (t+1) = xs))`;

val PENDING_TX_def = Define `
  (PENDING_TX txs 0       = txs) /\
  (PENDING_TX txs (SUC n) = PENDING_TX (RM_HD txs) n)`

(* Lemma: Show equivalence between the above two definitons *)

Theorem PENDING_TX_EQUIV:
  (!pending_tx mine txs. (pending_tx 0 = txs) /\ 
    TRANSACTIONS pending_tx mine ==> (pending_tx = PENDING_TX txs))
Proof
  NTAC 2 GEN_TAC >>

QED


Theorem PENDING_TX_IMP_LENGTH_PROP:
  (!txs. PENDING_TX txs (LENGTH txs) = [])
Proof
  Induct >| [
    (SIMP_TAC list_ss [PENDING_TX_def]),
    (GEN_TAC >> ASM_SIMP_TAC list_ss [PENDING_TX_def, RM_HD_def])
  ]
QED

(* If transactions are empty in the system for some time unit,
   so it will remain empty in the next time unit.*)

Theorem TRANS_THM:
  (!pending_tx mine. TRANSACTIONS pending_tx mine ==> 
      (!t. pending_tx t = [] ==> 
        pending_tx (t+1) = []))
Proof
  REPEAT GEN_TAC >>
  NTAC 3 STRIP_TAC >>
  UNDISCH_TAC ``TRANSACTIONS pending_tx mine`` >>
  REWRITE_TAC [TRANSACTIONS_def] >>
  SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] >>
  Q.EXISTS_TAC `t` >>
  ASM_SIMP_TAC list_ss []
QED

Theorem TRANS_THM:
  (!pending_tx mine. TRANSACTIONS pending_tx mine ==> (!t transactions. (pending_tx 0 = transactions) ==> pending_tx (t+LENGTH(transactions)) = []))
Proof
  REPEAT GEN_TAC >>
  STRIP_TAC >> STRIP_TAC >>
  Induct >>
    UNDISCH_TAC ``TRANSACTIONS pending_tx mine`` >>
    REWRITE_TAC [TRANSACTIONS_def] >>
  SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] >>
  Q.EXISTS_TAC `t` >>
  Cases_on `pending_tx t`
   >- (ASM_SIMP_TAC list_ss [])


QED


(* MINING

  The mining model mines a transaction and then send it to its
  smart contract for execution.

*)

Definition MINING_def:
  MINING mine sc_tx = !t. (sc_tx t = mine t)
End


(* REGISTER CONTRACT

  The register contract model is where the tx gets executed and
  the results are sent back to the user. The transaction after
  execution should be prepared for adding to blocks and notify
  variable should be updated.

*)

Datatype:
  register = list user
End

Definition FIND_USER_def:
  (FIND_USER (u, []) = F) /\
  (FIND_USER (u, (x::xs)) = if (x = u) then T else FIND_USER (u, xs))
End


Definition REGISTER_CONTRACT_def:
  REGISTER_CONTRACT sc_tx block_tx reg success =
    !t. (case (sc_tx t) of
           DATA x => 
              (if (FIND_USER(x, (reg t))) 
                 then
                   ((block_tx t = DATA x) /\ (reg (t+1) = reg t) /\ (success t = F))
                 else
                   ((block_tx t = DATA x) /\ (reg (t+1) = x::(reg t)) /\
                      (success t = T)))
        | NO_DATA => ((block_tx t = NO_DATA) /\ (reg (t+1) = reg t) /\
                      (success t = T)))
End



(* BLOCKS

  The blocks component is a list of blocks which is used to keep
  the record of transactions. 

*)


Definition BLOCKS_def:
  BLOCKS block_tx blocks =
    !t. (case block_tx t of
           DATA x  => (blocks (t+1) = (x::(blocks t)))
         | NO_DATA => (blocks (t+1) = (blocks t)))
End

(* CHANNEL 

    The channel may or may not be used in the formal model.
    I am thinking if I use the channel, the model would get more
    complex and so would the proof work. However, excluding the
    channel would leave us with 1 less scenario to test, namely
    the hacker stealing from channel.

    Discuss in DETAIL with Dr. Adnan

*)

Definition CHANNEL_def:
  CHANNEL tc dtc input output =
    !t. if t < tc then
          output t = NO_DATA
        else
          output t = input (t - dtc t) /\ 0 < tc /\ (dtc t = tc)
End


(* BLOCKCHAIN

  The blockchain model would a logical conjunction of four
  HOL definitions, each of which is an autonomous component of 
  the blockchain parameterized with time.

*)


Definition BLOCKCHAIN_def:
  BLOCKCHAIN tc1 dtc1 tc2 dtc2 tc3 dtc3 ch1 ch2 ch3 pending_tx mine sc_tx reg success block_tx blocks = 
    ((TRANSACTIONS pending_tx ch1) /\
     (CHANNEL tc1 dtc1 ch1 mine) /\
     (MINING mine ch2) /\ 
     (CHANNEL tc2 dtc2 ch2 sc_tx) /\
     (REGISTER_CONTRACT sc_tx ch3 reg success) /\
     (CHANNEL tc3 dtc3 ch3 block_tx) /\
     (BLOCKS block_tx blocks))
End

(* 06 MARCH, START HERE LOL *)

(* USER

  The user model is the essentially the user node making a
  transaction for registering an alias to its address.

  Possible considerations:

  - Remove the temporal property from user model

*)

Definition USER_REG_CALL_def:
  USER_REG_CALL pending_tx notify = 
    ((pending_tx 0 = [user_data]) /\ (notify 0 = F))
End


(* USER INTERACTION WITH BLOCKCHAIN

  This represents the complete system model (with the exception
  of the hacker model) as conjunction of user and blockchain
  model.

*)

Definition USER_INTERACT_BLOCKCHAIN_def:
  USER_INTERACT_BLOCKCHAIN tc dtc pending_tx notify mine sc_tx reg success block_tx blocks =
    ((USER_REG_CALL pending_tx notify) /\
     (BLOCKCHAIN tc dtc pending_tx notify mine sc_tx reg success block_tx blocks))
End


(* Initial Conditions
 
   This definition will initialise the time variables to their
   starting values and begin the blockchain system with empty
   pending transactions and blocks
*)

Definition INIT_def:
  INIT trans_list pending_tx mine sc_tx block_tx blocks = (
    (pending_tx 0 = trans_list) /\ (mine 0   = NO_DATA) /\ 
    (sc_tx 0 = no_data) /\ (block_tx 0 = (no_data,F)) /\ 
    (blocks 0 = [])
  )
End


Definition HACKED_PENDING_TX_def:
  HACKED_PENDING_TX tc pending_tx
    = ?t. (t < tc) /\ ~(pending_tx t = [])
End

(* Verification Theorems *)

(* Functional Correctness *)

(* Works with the hacker *)

Theorem USER_INTERACT_BLOCKCHAIN_SUCCESS:
  !pending_tx notify mine sc_tx reg success block_tx blocks.
  (INIT mine sc_tx block_tx blocks)  /\ (USER_INTERACT_BLOCKCHAIN pending_tx notify mine sc_tx reg success block_tx blocks) ==> (?t. blocks t = [(user_data,T)])
Proof
 (* TODO: Fill Proof *) 
  REWRITE_TAC [INIT_def] >>
  REWRITE_TAC [USER_INTERACT_BLOCKCHAIN_def] >>
  REWRITE_TAC [BLOCKCHAIN_def] >>
  REWRITE_TAC [USER_REG_CALL_def] >>
  REWRITE_TAC [TRANSACTIONS_def]
  REWRITE_TAC [MINING_def] >>
  REWRITE_TAC [REGISTER_CONTRACT_def] >>
  REWRITE_TAC [BLOCKS_def] >>
  REWRITE_TAC [hd_def,
    last_def,
    rm_last_def,
    find_user_def
  ]
  REPEAT GEN_TAC
  STRIP_TAC
  Cases_on `pending_tx <> []`
QED


Theorem USER_INTERACT_BLOCKCHAIN_HACKED:
  !pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks.
  (INIT mine sc_tx block_tx blocks tr dtr tm dtm tc dtc tb dtb) /\ (USER_INTERACT_BLOCKCHAIN pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks) ==> (HACKED_PENDING_TX tr pending_tx)
Proof
 (* TODO: Fill Proof *)
QED


(* Other properties that need to be verified *)

(* Introducing small LEMMAS to see model implications *)

(* If a transaction arrives, it sends to for mining step *)
Theorem TRANS_LEMMA:
  !tr dtr pending_tx mine. 
      (?t. pending_tx t = [user_data] ==>
        TRANSACTIONS tr dtr pending_tx mine  ==>
          (?t. mine t = user_data /\ pending_tx (t+1) = [] /\ dtr (t+1) = tr))
Proof
  rpt GEN_TAC
  >> STRIP_TAC
  >> REWRITE_TAC [TRANSACTIONS_def]
  >> GEN_TAC
  >> ASM_REWRITE_TAC []
  >> EVAL_TAC
QED



val _ = export_theory();


