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
    
    This definition represents the TRANSACTIONS process in our
    system. The process works by checking the pending transactions
    list. If this list is empty then nothing is sent to the next
    process. If this list contains transactions then the first
    element of the list is sent to mining and the list is updated
    by removing that element for next time unit.

*)

val TRANSACTIONS_def = Define `
  TRANSACTIONS pending_tx mine =
    !t. (case pending_tx t of
           []      => (mine t = NO_DATA) /\ (pending_tx (t+1) = [])
         | (x::xs) => (mine t = DATA x) /\ (pending_tx (t+1) = xs))`;

(* Alternate definition for sanity checks and easier proof calculus *)

val PENDING_TX_def = Define `
  (PENDING_TX txs 0       = txs) /\
  (PENDING_TX txs (SUC n) = PENDING_TX (RM_HD txs) n)`

(* Lemma: 
    Show equivalence between the above two definitons. This
    equivalence will help us prove theorem easily.
*)

Theorem PENDING_TX_EQUIV:
  (!pending_tx mine txs. (pending_tx 0 = txs) /\ 
    TRANSACTIONS pending_tx mine ==> (pending_tx = PENDING_TX txs))
Proof
  NTAC 2 GEN_TAC >>

QED

(* Lemma/Property *)

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

(* Much more difficult to prove, might need more assumptions? *)

Theorem TRANS_THM:
  (!pending_tx mine. TRANSACTIONS pending_tx mine ==> (!t transactions. (pending_tx 0 = transactions) ==> pending_tx (t+LENGTH(transactions)) = []))
Proof
  cheat (* FILL THIS LATER *)
QED


(* MINING

  This represents the mining process in our system. The mining model
  mines a transaction and then send it to its smart contract for
  execution.

*)

Definition MINING_def:
  MINING mine sc_tx = !t. (sc_tx t = mine t)
End



(* Datatype to represent the register. It is list of tuples. *)

Datatype:
  register = list user
End

(* Utility function to find a user entry in the register.
   Move to another HOL theory? 
*)

Definition FIND_USER_def:
  (FIND_USER (u, []) = F) /\
  (FIND_USER (u, (x::xs)) = if (x = u) then T else FIND_USER (u, xs))
End

(* REGISTER CONTRACT

  This definition represents the smart contract process in our
  system. This smart contract checks if the user name and address
  are already present in the register. If yes, then it send failure
  and success otherwise. It then send the transaction to blocks
  process to be added to the blockchain.

*)

Definition REGISTER_CONTRACT_def:
  REGISTER_CONTRACT sc_tx block_tx reg success =
    !t. (case (sc_tx t) of
           DATA x => 
              (if (FIND_USER(x, (reg t))) 
                 then
                   ((block_tx t = NO_DATA) /\ (reg (t+1) = reg t) /\ (success t = F))
                 else
                   ((block_tx t = DATA x) /\ (reg (t+1) = x::(reg t)) /\
                      (success t = T)))
        | NO_DATA => ((block_tx t = NO_DATA) /\ (reg (t+1) = reg t) /\
                      (success t = T)))
End



(* BLOCKS

  This represents the blocks process of the blockchain system. The 
  blocks component is a list of blocks which is used to keep the
  record of transactions. It only stores successful transactions.

*)


Definition BLOCKS_def:
  BLOCKS block_tx blocks =
    !t. (case block_tx t of
           DATA x  => (blocks (t+1) = (x::(blocks t)))
         | NO_DATA => (blocks (t+1) = (blocks t)))
End


(* CHANNEL 
    
    The channel copies the input data to output after tc timeunits.
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
  HOL definitions and the channels in between those processes,
  each of which is an autonomous component of the blockchain
  parameterized with time.

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


(* USER

  The user model is the essentially the user node making a
  transaction for registering an alias to its address.

*)

Definition USER_REG_CALL_def:
  USER_REG_CALL txs pending_tx success = 
    ((pending_tx 0 = txs) /\ (success 0 = F))
End


(* USER INTERACTION WITH BLOCKCHAIN

  This represents the complete system model as conjunction of user and blockchain
  model.

*)

Definition USER_INTERACT_BLOCKCHAIN_def:
  USER_INTERACT_BLOCKCHAIN txs pending_tx success tc1 dtc1 tc2 dtc2
    tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx
    blocks =
      ((USER_REG_CALL txs pending_tx success) /\
       (BLOCKCHAIN tc1 dtc1 tc2 dtc2 tc3 dtc3 ch1 ch2 ch3 pending_tx mine sc_tx reg success block_tx blocks))
End

(* Initial Conditions
 
   This definition will initialise the time variables to their
   starting values and begin the blockchain system with empty
   variables
*)

Definition BLOCKCHAIN_INITAL_VALUES_def:
  BLOCKCHAIN_INITIIAL_VALUES tc1 dtc1 tc2 dtc2 tc3 dtc3 ch1 ch2 ch3 
     mine sc_tx reg block_tx blocks = (
     (dtc1 0 = tc1) /\ (dtc2 0 = tc2) /\ (dtc3 0 = tc3) /\
     (ch1 0 = NO_DATA) /\ (ch2 0 = NO_DATA) /\ (ch3 0 = NO_DATA) /\
     (mine 0 = NO_DATA) /\ (sc_tx 0 = NO_DATA) /\ (block_tx 0 = NO_DATA) /\ 
     (reg 0 = []) /\ (blocks 0 = [])
  )
End

(* Represents the condition when a transaction is hacked 
   from the system throught pending transactions. 
*)

Definition HACKED_PENDING_TX_def:
  HACKED_PENDING_TX tc pending_tx
    = ?t. (t < tc) /\ ~(pending_tx t = [])
End

(* Verification Theorems *)

(* Functional Correctness *)

(* Works with the hacker *)

