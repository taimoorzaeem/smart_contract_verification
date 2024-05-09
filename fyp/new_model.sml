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
      listSyntax;


Datatype:
  user_alias = alias | no_alias
End

Datatype:
  user_address = address | no_address
End

(* Product Type definition: *)
Datatype:
  user = <| n:user_alias ; a:user_address |>
End

Definition USER_DATA_def:
  user_data = (alias,address)
End

Definition NO_DATA_def:
  no_data = (no_alias,no_address)
End

Definition HD_def:
  (HD [] = no_data) /\
  (HD (x::xs) = x)
End

Definition LAST_def:
  (LAST [] = no_data) /\
  (LAST [x] = x) /\
  (LAST (x::xs) = LAST xs)
End

Definition RM_LAST_def:
  (RM_LAST [] = []) /\
  (RM_LAST [x] = []) /\
  (RM_LAST (x::xs) = x::(RM_LAST xs))
End


Datatype:
  transaction = data | no_data
End

(* TRANSACTIONS

  The transaction model contains two parallel process, one is
  used for getting the tx from the network and adding it to
  pending transactions, and the other process is used to send
  the tx for mining.

*)


Definition TRANSACTIONS_def:
  TRANSACTIONS pending_tx mine =
    !t. (if pending_tx t <> [] 
            then
              (mine t = LAST (pending_tx t)) /\
              (pending_tx (t+1) = RM_LAST (pending_tx t))
            else
              (mine t = no_data) /\
              (pending_tx (t+1) = (pending_tx t)))
End


(* MINING

  The mining model mines a transaction and then send it to its
  smart contract for execution.

*)

Definition MINING_def:
  MINING mine sc_tx = 
    !t. (if mine t = user_data then
            (sc_tx t = user_data)
          else
            (sc_tx t = no_data))
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

Definition find_user_def:
  (find_user (u, []) = F) /\
  (find_user (u, (x::xs)) = if (FST x = FST u) then T else find_user (u, xs))
End


Definition REGISTER_CONTRACT_def:
  REGISTER_CONTRACT sc_tx block_tx reg notify success =
    !t. if (notify t = F) /\ (sc_tx t = user_data) then
            (if find_user (user_data, reg t) then
              (block_tx t = (user_data,F)) /\
              (reg (t+1) = (reg t)) /\
              (success t = F) /\ (notify t = T)
            else
              (block_tx t = (user_data,T)) /\
              (reg (t+1) = user_data::(reg t)) /\
              (success t = T) /\ (notify t = T))
          else
            T
End



(* BLOCKS

  The blocks component is a list of blocks which is used to keep
  the record of transactions. 

*)


Definition BLOCKS_def:
  BLOCKS block_tx blocks =
    !t. (if (FST (block_tx t) = user_data) then
             (blocks t = (user_data::(blocks (t-1))))
        else
            (blocks t = (blocks (t-1))))
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
          output t = no_data
        else
          output t = input (t - dtc t) /\ 0 < tc /\ (dtc t = tc)
End


(* BLOCKCHAIN

  The blockchain model would a logical conjunction of four
  HOL definitions, each of which is an autonomous component of 
  the blockchain parameterized with time.

*)


Definition BLOCKCHAIN_def:
  BLOCKCHAIN tc dtc pending_tx notify mine sc_tx reg success block_tx blocks = 
    ((TRANSACTIONS pending_tx mine) /\
     (CHANNEL tc dtc pending_tx mine) /\
     (MINING mine sc_tx) /\ 
     (CHANNEL tc dtc mine sc_tx) /\
     (REGISTER_CONTRACT sc_tx block_tx reg notify success) /\
     (CHANNEL tc dtc sc_tx block_tx) /\
     (BLOCKS block_tx blocks))
End


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
  INIT mine sc_tx block_tx blocks = (
    (mine 0   = no_data) /\ (sc_tx 0 = no_data) /\ 
    (block_tx 0 = (no_data,F)) /\ (blocks 0 = [])
  )
End


Definition HACKED_PENDING_TX_def:
  HACKED_PENDING_TX tr pending_tx
    = ?t. (t < tr) /\ (pending_tx t = [user_data])
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


