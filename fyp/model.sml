(* 
  Time interval in all processes is taken 1, which we can
  change to a variable quantity later. *) 
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

Definition FIRST_TX_def:
  (FIRST_TX [] = no_data) /\
  (FIRST_TX (x::xs) = x)
End

Definition LAST_TX_def:
  (LAST_TX [] = no_data) /\
  (LAST_TX [x] = x) /\
  (LAST_TX (x::xs) = LAST_TX xs)
End

Definition RM_LAST_TX_def:
  (RM_LAST_TX [] = []) /\
  (RM_LAST_TX [x] = []) /\
  (RM_LAST_TX (x::xs) = x::(RM_LAST_TX xs))
End

(* TRANSACTIONS

  The transaction model contains two parallel process, one is
  used for getting the tx from the network and adding it to
  pending transactions, and the other process is used to send
  the tx for mining.

*)


val TRANSACTIONS_def = Define `
  TRANSACTIONS tr dtr pending_tx mine =
    !t. (if pending_tx t <> [] then
           (if dtr t = 0 then
              (mine t = LAST_TX (pending_tx t)) /\
              (dtr (t+1) = tr)                  /\
              (pending_tx (t+1) = RM_LAST_TX (pending_tx t))
            else
              (mine t = no_data)       /\
              (dtr (t+1) = dtr t - 1) /\
              (pending_tx (t+1) = pending_tx t))
         else
           (mine t = no_data) /\ 
           (dtr (t+1) = tr)   /\ 
           (pending_tx (t+1) = pending_tx t))`

(* Divide this big definition into smaller ones. *)

val PENDING_TX_AND_DTR_def = Define `
  (PENDING_TX_AND_DTR tr pending_tx 0 = ([user_data], tr)) /\
  (PENDING_TX_AND_DTR tr pending_tx (SUC n) = 
    (if pending_tx n <> [] then 
       (if SND (PENDING_TX_AND_DTR tr pending_tx n) = 0 then 
           ((RM_LAST_TX (pending_tx n)), tr)
        else
            (pending_tx n, (SND (PENDING_TX_AND_DTR tr pending_tx n)) - 1))
     else
        (pending_tx n, tr)))`
         
val MINE_AND_DTR_def = Define `
  (MINE_AND_DTR tr pending_tx mine 0 = (no_data, tr)) /\
  (MINE_AND_DTR tr pending_tx mine (SUC n) =
    (if pending_tx n <> [] then 
       (if SND (MINE_AND_DTR tr pending_tx mine n) = 0 then 
           ((LAST_TX (pending_tx n)), tr)
        else
            (no_data, (SND (MINE_AND_DTR tr mine pending_tx n)) - 1))
     else
        (no_data, tr)))`

(* Prove Equivalence *)

val TRANSACTIONS_EQ_PENDING_TX_AND_MINE_DTR_TR = prove(``!tr dtr pending_tx mine. TRANSACTIONS tr dtr pending_tx mine ==> (!t. dtr t = SND (PENDING_TX_AND_DTR tr pending_tx t))``,

REPEAT STRIP_TAC >>
FULL_SIMP_TAC std_ss [TRANSACTIONS_def] >>


);

(* MINING

  The mining model mines a transaction and then send it to its
  smart contract for execution.

*)

Definition MINING_def:
  MINING tm dtm mine sc_tx = 
    !t. (if  (mine t = user_data) then
          (if (dtm t = 0) then
            (sc_tx t = user_data) /\
            (dtm (t+1) = tm)
          else
            (sc_tx t = no_data) /\ (dtm (t+1) = dtm t - 1))
      else
        (sc_tx t = no_data) /\ (dtm (t+1) = tm))
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
  (FIND_USER (u, (x::xs)) = if (FST x = FST u) then T else FIND_USER (u, xs))
End


Definition REGISTER_CONTRACT_def:
  REGISTER_CONTRACT tc dtc sc_tx block_tx reg notify success =
    !t. if (notify t = F) /\ (sc_tx t = user_data) then
            (if (dtc t = 0) then 
                (if FIND_USER (user_data, reg t) then
                  (block_tx t = (user_data,F)) /\
                  (success t = F) /\ (notify t = T) /\
                  (dtc (t+1) = tc)
                else
                  (block_tx t = (user_data,T)) /\
                  (reg (t+1) = user_data::(reg t)) /\
                  (success t = T) /\ (notify t = T) /\
                  (dtc (t+1) = tc))
            else
              (dtc (t+1) = dtc t - 1))
        else
          (dtc (t+1) = tc)
End



(* BLOCKS

  The blocks component is a list of blocks which is used to keep
  the record of transactions. 

*)


Definition BLOCKS_def:
  BLOCKS tb dtb block_tx blocks =
    !t. if (FST (block_tx t) = user_data) then
          (if (dtb t = 0) then
            (blocks t = (user_data,SND (block_tx (t-1)))::(blocks (t-1))) /\
            (dtb (t+1) = tb)
          else
            (dtb (t+1) = dtb t - 1))
        else
           (dtb (t+1) = tb)
End


(* BLOCKCHAIN

  The blockchain model would a logical conjunction of four
  HOL definitions, each of which is an autonomous component of 
  the blockchain parameterized with time.

*)


Definition BLOCKCHAIN_def:
  BLOCKCHAIN tr dtr pending_tx notify tm dtm mine tc dtc sc_tx reg  success tb dtb block_tx blocks = 
    ((TRANSACTIONS tr dtr pending_tx mine) /\ 
     (MINING tm dtm mine sc_tx) /\ 
     (REGISTER_CONTRACT tc dtc sc_tx block_tx reg notify success) /\
     (BLOCKS tb dtb block_tx blocks))
End




(* USER

  The user model is the essentially the user node making a
  transaction for registering an alias to its address.

  Possible considerations:

  - Remove the temporal property from user model (probably not)

*)

Definition USER_REG_CALL_def:
  USER_REG_CALL pending_tx notify = 
    ((pending_tx 0 = [user_data]) /\ (notify 0 = F))
End

(* CHANNEL 

    The channel may or may not be used in the formal model.
    I am thinking if I use the channel, the model would get more
    complex and so would the proof work. However, excluding the
    channel would leave us with 1 less scenario to test, namely
    the hacker stealing from channel.

    Discuss in DETAIL with Dr. Adnan


Definition CHANNEL_def:
  CHANNEL td dtd input pending_tx =
    !t. 
      (if t < dtd then
        T
      else
        output t = input (t - dtd t) /\ 0 < td /\ (dtd t = td))
End

*)


(* USER INTERACTION WITH BLOCKCHAIN

  This represents the complete system model (with the exception
  of the hacker model) as conjunction of user and blockchain
  model.

*)

Definition USER_INTERACT_BLOCKCHAIN_def:
  USER_INTERACT_BLOCKCHAIN pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks =
    ((USER_REG_CALL pending_tx notify) /\ 
    (BLOCKCHAIN tr dtr pending_tx notify tm dtm mine tc dtc sc_tx reg success tb dtb block_tx blocks))
End


(* Initial Conditions
 
   This definition will initialise the time variables to their
   starting values and begin the blockchain system with empty
   pending transactions and blocks
*)

Definition INIT_def:
  INIT mine sc_tx block_tx blocks tr dtr tm dtm tc dtc tb dtb = (
    (mine 0   = no_data) /\ (sc_tx 0 = no_data) /\ (block_tx 0 = (no_data,F)) /\
    (blocks 0 = [])      /\ (dtr 0 = tr)        /\
    (dtm 0 = tm)       /\ (dtc 0 = tc)      /\ (dtb 0 = tb))
End


Definition HACKED_PENDING_TX_def:
  HACKED_PENDING_TX tr pending_tx
    = ?t. (t < tr) /\ (pending_tx t = [user_data])
End

(* Verification Theorems *)

(* Functional Correctness *)

(* Works with the hacker *)


(*
  Informal Proof:
    
    According to the timevals given for each process,
    the time value for when blocks == [(user_data,T)]
    would be
      t = tr + tm + tc + tb

    We need more generalization of our input transactions lists

*)
(*
Theorem USER_INTERACT_BLOCKCHAIN_SUCCESS:
  !pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks.
  (INIT mine sc_tx block_tx blocks tr dtr tm dtm tc dtc tb dtb) /\ (USER_INTERACT_BLOCKCHAIN pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks) ==> (?t. blocks t = [(user_data,T)])
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
*)

(*

  Define lemma to easily work with time variables.
  The idea is to define lemmas for rewriting case
  splits with the variables for example tr and dtr

  !t tr dtr. 
    (t < tr /\ dtr 0 = tr ==> 
      (if dtr t = 0 then dtr (t+1) = tr else dtr (t+1) = dtr t - 1) ==>
      dtr t <> 0)

*)


val CYCLIC_COUNTDOWN_def = Define `
   (CYCLIC_COUNTDOWN tr 0 = tr) ∧
   (CYCLIC_COUNTDOWN tr (SUC n) = if CYCLIC_COUNTDOWN tr n = 0 then tr else CYCLIC_COUNTDOWN tr n - 1)`



val CYCLIC_COUNTDOWN_ALT_DEF = store_thm("CYCLIC_COUNTDOWN_ALT_DEF",
  ``∀tr n. CYCLIC_COUNTDOWN tr n = tr - (n MOD (SUC tr))``,
GEN_TAC >>
Induct_on `n` >- (
  SIMP_TAC arith_ss [CYCLIC_COUNTDOWN_def]
) >>
`∃a b. n = a * (SUC tr) + b ∧ b < SUC tr` by PROVE_TAC[arithmeticTheory.DA, prim_recTheory.LESS_0] >>
ASM_SIMP_TAC std_ss [CYCLIC_COUNTDOWN_def, arithmeticTheory.MOD_TIMES,arithmeticTheory.ADD_SUC] >>
Cases_on `b = tr` >> ASM_SIMP_TAC arith_ss [])




val CYCLIC_COUNTDOWN_FIRST_0 = store_thm("CYCLIC_COUNTDOWN_FIRST_0",
  ``∀tr. CYCLIC_COUNTDOWN tr tr = 0``,
SIMP_TAC arith_ss [CYCLIC_COUNTDOWN_ALT_DEF]);

val CYCLIC_COUNTDOWN_EQ_0 = store_thm("CYCLIC_COUNTDOWN_EQ_0",
  ``∀tr n. (CYCLIC_COUNTDOWN tr n = 0) <=> (n MOD SUC tr = tr)``,
REPEAT GEN_TAC >>
EQ_TAC >> SIMP_TAC arith_ss [CYCLIC_COUNTDOWN_ALT_DEF] >>
`n MOD SUC tr < SUC tr` by PROVE_TAC[arithmeticTheory.MOD_LESS, prim_recTheory.LESS_0] >>
DECIDE_TAC)


val CYCLIC_COUNTDOWN_EQ_MAX = store_thm("CYCLIC_COUNTDOWN_EQ_MAX",
  ``∀tr n. (CYCLIC_COUNTDOWN tr n = tr) <=> (n MOD SUC tr = 0)``,
SIMP_TAC arith_ss [CYCLIC_COUNTDOWN_ALT_DEF, arithmeticTheory.SUB_EQ_EQ_0] >>
METIS_TAC[arithmeticTheory.MOD_ONE])


val CYCLIC_COUNTDOWN_LOCAL_SPEC = prove(``!dtr tr. (dtr 0 = tr) ∧
    (!t. if dtr t = 0 then dtr (t+1) = tr else dtr (t+1) = dtr t - 1) ==>
    (dtr = CYCLIC_COUNTDOWN tr)``,

REPEAT STRIP_TAC >>
SIMP_TAC std_ss [FUN_EQ_THM] >>
Induct >- (
  ASM_REWRITE_TAC [CYCLIC_COUNTDOWN_def]
) >>
FULL_SIMP_TAC std_ss [CYCLIC_COUNTDOWN_def, GSYM arithmeticTheory.ADD1] >>
METIS_TAC[])



val MAIN_THM = prove(``!dtr tr. (dtr 0 = tr) ==>
    (!t. if dtr t = 0 then dtr (t+1) = tr else dtr (t+1) = dtr t - 1)
      ==> (dtr tr = 0)``,

REPEAT STRIP_TAC >>
`dtr = CYCLIC_COUNTDOWN tr` by PROVE_TAC[CYCLIC_COUNTDOWN_LOCAL_SPEC] >>
ASM_REWRITE_TAC[CYCLIC_COUNTDOWN_FIRST_0])

(* Given t < tr, the timer will never complete i.e. dtr t <> 0 *)

val MAIN_THM2 = prove(``∀t tr dtr.
    ((!t. if dtr t = 0 then dtr (t+1) = tr else dtr (t+1) = dtr t - 1) ==>
       t < tr /\ dtr 0 = tr ==>
             dtr t <> 0)``,

REPEAT GEN_TAC >> NTAC 2 STRIP_TAC >>
`dtr = CYCLIC_COUNTDOWN tr` by PROVE_TAC[CYCLIC_COUNTDOWN_LOCAL_SPEC] >>
FULL_SIMP_TAC arith_ss [CYCLIC_COUNTDOWN_ALT_DEF])

(*
Given the initial values (INIT) of the variables and the whole blockchain system(USER_INTERACT_BLOCKCHAIN), if for all t less than the time of retrieval "tr", it implies that pending transactions at that t should not be null ("<> []").

*)

Theorem FOR_ALL_T_LESS_TR_PENDING_NOT_EMPTY:
  !pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks.
  (INIT mine sc_tx block_tx blocks tr dtr tm dtm tc dtc tb dtb) /\ (USER_INTERACT_BLOCKCHAIN pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks) ==> (!t. t < tr ==> pending_tx t <> [])
Proof
  REWRITE_TAC [INIT_def]
  >> REWRITE_TAC [USER_INTERACT_BLOCKCHAIN_def, BLOCKCHAIN_def]
  >> REPEAT GEN_TAC >> STRIP_TAC >> GEN_TAC
  >> STRIP_TAC
  >> UNDISCH_TAC ``TRANSACTIONS tr dtr pending_tx mine``
  >> REWRITE_TAC [TRANSACTIONS_def]
  >> Cases_on `(!t. pending_tx t <> [])`
    >- (ASM_REWRITE_TAC []
      >> REWRITE_TAC [GSYM TRANSACTIONS_PENDING_TX_NOT_NULL_def]
      >> STRIP_TAC
      >> `dtr t <> 0` by PROVE_TAC[DTR_T_NOT_EQ_0]
      >> UNDISCH_TAC ``TRANSACTIONS_PENDING_TX_NOT_NULL tr dtr pending_tx mine``
      >> REWRITE_TAC [TRANSACTIONS_PENDING_TX_NOT_NULL_def]
      >> SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM]
      >> Q.EXISTS_TAC `t`
      >> ASM_REWRITE_TAC []
      >> REPEAT STRIP_TAC >> ASM_REWRITE_TAC [])
    
    >> FULL_SIMP_TAC std_ss []
    >> `?t. pending_tx t = []` by PROVE_TAC [NOT_FOR_ALL_PENDING_EQ_EXISTS_PENDING]
    >> SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM]
    >> Q.EXISTS_TAC `t'`
    >> ASM_REWRITE_TAC []
    >> S


       
       )

QED




Theorem FOR_ALL_T_LESS_TR_MINE_EQ_NO_DATA:
  !pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks.
  (INIT mine sc_tx block_tx blocks tr dtr tm dtm tc dtc tb dtb) /\ (USER_INTERACT_BLOCKCHAIN pending_tx notify tr dtr tm dtm mine sc_tx tc dtc reg success tb dtb block_tx blocks) ==> (!t. t < tr ==> mine t = no_data)
Proof
  REWRITE_TAC [INIT_def]
  >> REWRITE_TAC [USER_INTERACT_BLOCKCHAIN_def, BLOCKCHAIN_def]
  >> REPEAT GEN_TAC >> STRIP_TAC >> GEN_TAC >> STRIP_TAC
  >> UNDISCH_TAC ``TRANSACTIONS tr dtr pending_tx mine``
  >> REWRITE_TAC [TRANSACTIONS_def]
  >> Cases_on `(!t. pending_tx t <> [])`
    >- (ASM_REWRITE_TAC []
      >> REWRITE_TAC [GSYM TRANSACTIONS_PENDING_TX_NOT_NULL_def]
      >> STRIP_TAC
      >> `dtr t <> 0` by PROVE_TAC[DTR_T_NOT_EQ_0]
      >> UNDISCH_TAC ``TRANSACTIONS_PENDING_TX_NOT_NULL tr dtr pending_tx mine``
      >> REWRITE_TAC [TRANSACTIONS_PENDING_TX_NOT_NULL_def]
      >> SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM]
      >> Q.EXISTS_TAC `t`
      >> ASM_REWRITE_TAC []
      >> REPEAT STRIP_TAC >> ASM_REWRITE_TAC [])
    
    >> FULL_SIMP_TAC std_ss []
    >> `?t. pending_tx t = []` by PROVE_TAC [NOT_FOR_ALL_PENDING_EQ_EXISTS_PENDING]
    >> SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM]
    >> Q.EXISTS_TAC `t'`
    >> ASM_REWRITE_TAC []
    >> S


QED

val _ = export_theory();

val TRANSACTIONS_def = Define `
  TRANSACTIONS tr dtr pending_tx mine =
    !t. (if pending_tx t <> [] then
           (if dtr t = 0 then
              (mine (t+1) = LAST_TX (pending_tx t)) /\
              (dtr (t+1) = tr)                  /\
              (pending_tx (t+1) = RM_LAST_TX (pending_tx t))
            else
              (mine (t+1) = no_data)       /\
              (dtr (t+1) = dtr t - 1) /\
              (pending_tx (t+1) = pending_tx t))
         else
           (mine (t+1) = no_data) /\ 
           (dtr (t+1) = tr)   /\ 
           (pending_tx (t+1) = pending_tx t))`


(dtr 0 = tr) /\ (pending_tx 0 = [user_data]) /\ (TRANSACTIONS tr dtr pending_tx mine) ==> (!t. t < tr ==> pending_tx t <> [])

Proof

  NTAC 3 STRIP_TAC >>
  UNDISCH_TAC ``TRANSACTIONS tr dtr pending_tx mine``
  REWRITE_TAC [TRANSACTIONS_def]
  SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM]
  Q.EXISTS_TAC `t`
  Cases_on `pending_tx t <> []`
    >- (ASM_REWRITE_TAC [])
    >- (ASM_REWRITE_TAC []
        >> STRIP_TAC
  


    >> 




val TRANSACTIONS_NO_MINE_def = Define `
  TRANSACTIONS_NO_MINE tr dtr pending_tx =
    !t. (if pending_tx t <> [] then
           (if dtr t = 0 then
              (dtr (t+1) = tr)                  /\
              (pending_tx (t+1) = RM_LAST_TX (pending_tx t))
            else
              (dtr (t+1) = dtr t - 1) /\
              (pending_tx (t+1) = pending_tx t))
         else
           (dtr (t+1) = tr)   /\ 
           (pending_tx (t+1) = pending_tx t))`

val TRANSACTIONS_IMP_TRANSACTIONS_NO_MINE = prove(``!tr dtr pending_tx mine. TRANSACTIONS tr dtr pending_tx mine ==> TRANSACTIONS_NO_MINE tr dtr pending_tx``,

REPEAT STRIP_TAC >>
REWRITE_TAC [TRANSACTIONS_NO_MINE_def] >>
GEN_TAC >>
UNDISCH_TAC ``TRANSACTIONS tr dtr pending_tx mine`` >>
REWRITE_TAC [TRANSACTIONS_def] >>
SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] >>
Q.EXISTS_TAC `t` >>
RW_TAC std_ss [] (* Automatic case-spliting and do rewrites *)

);

val COUNTDOWN_def = Define `
     (COUNTDOWN tr 0 = tr)
  /\ (COUNTDOWN tr (SUC n) = if COUNTDOWN tr n = 0 then tr else COUNTDOWN tr n - 1)`

val PENDING_TX_def = Define `
     (PENDING_TX tr 0 = [user_data])
  /\ (PENDING_TX tr (SUC n) = 
        if PENDING_TX tr n <> [] then
          (if COUNTDOWN tr n = 0 then 
              RM_LAST_TX (PENDING_TX tr n)
          else
            PENDING_TX tr n)
        else 
          PENDING_TX tr n)`

val TRANSACTIONS_NO_MINE_IMP_PENDING_EQ_PENDING = prove(``!pending_tx dtr tr.
    (pending_tx 0 = [user_data]) /\ (dtr 0 = tr) ==> 
    TRANSACTIONS_NO_MINE tr dtr pending_tx       ==> 
    (pending_tx = PENDING_TX tr)``,

REWRITE_TAC [TRANSACTIONS_NO_MINE_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [FUN_EQ_THM] >>
Induct
  >> ASM_REWRITE_TAC [PENDING_TX_def] 

  >> FULL_SIMP_TAC std_ss [PENDING_TX_def, GSYM ADD1]
  >> METIS_TAC [COUNTDOWN_def]

);

val MINE_def = Define `
     (MINE tr 0 = no_data)
  /\ (MINE tr (SUC n) = 
        if PENDING_TX tr n <> [] then
          (if COUNTDOWN tr n = 0 then 
              LAST_TX (PENDING_TX tr n)
          else
            no_data)
        else 
          no_data)`


val TRANSACTIONS_NO_MINE_EQ_PENDING_TX = prove(``!pending_tx dtr tr.
    (pending_tx 0 = [user_data]) /\ (dtr 0 = tr) ==> 
    TRANSACTIONS_NO_MINE tr dtr pending_tx       ==> 
    (pending_tx = PENDING_TX tr)``,

REWRITE_TAC [TRANSACTIONS_NO_MINE_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [FUN_EQ_THM] >>
Induct >- (
  ASM_REWRITE_TAC [PENDING_TX_JUST_def]
) >>
REWRITE_TAC [PENDING_TX_JUST_def] >>
FULL_SIMP_TAC std_ss [PENDING_TX_JUST_def, GSYM arithmeticTheory.ADD1] >>
METIS_TAC [PENDING_TX_JUST_def]

);

val FIRST_def = Define `
  FIRST (x, y, z) = x`
val SECOND_def = Define `
  SECOND (x, y, z) = y`
val THIRD_def = Define `
  THIRD (x, y, z) = z`

val PENDING_MINE_COUNTDOWN_def = Define `
   (PENDING_MINE_COUNTDOWN tr 0 = ([user_data], no_data, tr)) /\
   (PENDING_MINE_COUNTDOWN tr (SUC n) = 
      if FIRST (PENDING_MINE_COUNTDOWN tr n) <> [] then 
        (if THIRD (PENDING_MINE_COUNTDOWN tr n) = 0 then
          (RM_LAST_TX (FIRST (PENDING_MINE_COUNTDOWN tr n)), LAST_TX (FIRST (PENDING_MINE_COUNTDOWN tr n)), tr)
        else
          (FIRST (PENDING_MINE_COUNTDOWN tr n), no_data, THIRD (PENDING_MINE_COUNTDOWN tr n) - 1))
      else 
        (FIRST (PENDING_MINE_COUNTDOWN tr n), no_data, tr))`
        

val TRANS_EQ_PENDING_MINE_COUNTDOWN = prove(``!pending_tx mine dtr tr.
  (pending_tx 0 = [user_data]) /\ (mine 0 = no_data) /\ (dtr 0 = tr) ==> TRANSACTIONS tr dtr pending_tx mine ==> (!t. (pending_tx t,mine t,dtr t) = PENDING_MINE_COUNTDOWN tr t)``,

REWRITE_TAC [TRANSACTIONS_def] >>
REPEAT GEN_TAC >>
NTAC 2 STRIP_TAC >>
Induct >- (
  ASM_REWRITE_TAC [PENDING_MINE_COUNTDOWN_def]
) >>
FULL_SIMP_TAC std_ss [PENDING_MINE_COUNTDOWN_def, GSYM ADD1] >> 
METIS_TAC [FIRST_def, THIRD_def]

);


val T_LESS_TR_IMP_LEMMA = prove(``!t pending_tx mine dtr tr.
  (pending_tx 0 = [user_data]) /\ (mine 0 = no_data) /\ (dtr 0 = tr) /\ (t < tr) ==> (!t. (pending_tx t, mine t, dtr t) = PENDING_MINE_COUNTDOWN tr t) ==> (pending_tx t, mine t, dtr t) = ([user_data], no_data, THIRD (PENDING_MINE_COUNTDOWN tr t) - 1)``,

REPEAT STRIP_TAC >>
UNDISCH_TAC ``∀t. (pending_tx t,mine t,dtr t) = PENDING_MINE_COUNTDOWN tr t``
Induct



);

val T_LESS_TR_IMP_PENDING_EQ_NULL = prove(``!t pending_tx mine dtr tr.
  (pending_tx 0 = [user_data]) /\ (mine 0 = no_data) /\ (dtr 0 = tr) ==> TRANSACTIONS tr dtr pending_tx mine /\ (t < tr) ==> pending_tx t = [user_data]``,

REPEAT STRIP_TAC >>
`(!t. (pending_tx t,mine t,dtr t) = PENDING_MINE_COUNTDOWN tr t)` by PROVE_TAC[TRANS_EQ_PENDING_MINE_COUNTDOWN] >>
UNDISCH_TAC ``(!t. (pending_tx t,mine t,dtr t) = PENDING_MINE_COUNTDOWN tr t)`` >>
SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] >>
Q.EXISTS_TAC `t` >>
FULL_SIMP_TAC std_ss [TRANSACTIONS_def] >>
STRIP_TAC >>
FULL_SIMP_TAC std_ss [GSYM ADD1] >>


)'

val PENDING_TX_def = Define `
  (PENDING_TX tr 0 = [user_data]) /\
  (PENDING_TX tr (SUC n) = 
    if PENDING_TX tr n <> [] /\ COUNTDOWN tr n = 0 then 
        RM_LAST_TX (PENDING_TX tr n) 
    else 
      PENDING_TX tr n)`


val MINE_def = Define `
  (MINE tr 0 = no_data) /\
  (MINE tr (SUC n) = 
    if PENDING_TX tr n <> [] /\ COUNTDOWN tr n = 0 then 
        LAST_TX (PENDING_TX tr n) 
    else 
      no_data)`

val TRANSACTIONS_SMALL_def = Define `
  (TRANSACTIONS_SMALL tr 0 = ((PENDING_TX tr 0), (MINE tr 0), (COUNTDOWN tr 0))) /\
  (TRANSACTIONS_SMALL tr (SUC n) = ((PENDING_TX tr (SUC n)), (MINE tr (SUC n)) ,(COUNTDOWN tr (SUC n))))`


val TRANSACTIONS_EQ_DEF = prove(``!pending_tx mine tr dtr.
  (pending_tx 0 = [user_data]) /\ (mine 0 = no_data) /\ (dtr 0 = tr) ==> TRANSACTIONS tr dtr pending_tx mine ==> (pending_tx = PENDING_TX tr)``

REWRITE_TAC [TRANSACTIONS_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [FUN_EQ_THM] >>
Induct >- (
  ASM_REWRITE_TAC [PENDING_TX_def]
) >>
FULL_SIMP_TAC std_ss [PENDING_TX_def, GSYM ADD1] >>
METIS_TAC [PENDING_TX_def, MINE_def, COUNTDOWN_def]




(*

val TRANSACTIONS_def = Define `
  TRANSACTIONS pending_tx =
    !t. (if pending_tx t <> [] then
              (pending_tx (t+1) = RM_LAST_TX (pending_tx t))
            else
              (pending_tx (t+1) = pending_tx t))`

val PENDING_TX_def = Define `
  (PENDING_TX 0       = [user_data]) /\
  (PENDING_TX (SUC n) = if PENDING_TX n <> [] then RM_LAST_TX (PENDING_TX n) else PENDING_TX n)`

val TRANS_EQ_PENDING = prove(``!pending_tx.
  (pending_tx 0 = [user_data]) /\ (TRANSACTIONS pending_tx) ==> (pending_tx = PENDING_TX)``

REWRITE_TAC [TRANSACTIONS_def] >>
REPEAT STRIP_TAC >>
SIMP_TAC std_ss [FUN_EQ_THM] >>
Induct >- (
  ASM_REWRITE_TAC [PENDING_TX_def]
) >>
FULL_SIMP_TAC std_ss [PENDING_TX_def, GSYM ADD1] >>
METIS_TAC []

);
*)


