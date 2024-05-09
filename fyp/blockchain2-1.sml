(* 
  Time interval in all processes is taken 1, which we can
  change to a variable quantity later. *) 


load "realTheory";

open  HolKernel 
      Parse 
      arithmeticTheory 
      boolLib 
      boolTheory 
      bossLib 
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
      realTheory
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
  user_data = <| n:user_alias ; a:user_address |>
End

Definition USER_def:
  user = (alias,address)
End

Definition NO_USER_def:
  no_user = (no_alias,no_address)
End

(* CHANNEL

  The channel copies the input to the output after tc units of time

*)

Definition CHANNEL_def:
  CHANNEL tc dtc input output =
    !t:real. 
      (if t < tc then
        output t = no_user
      else
        output t = input (t - dtc t) /\ 0 < tc /\ (dtc t = tc))
End



(* TRANSACTIONS

  The transaction model contains two parallel process, one is
  used for getting the tx from the network and adding it to
  pending transactions, and the other process is used to send
  the tx for mining.

*)


Definition hd_def:
  (hd [] = no_user) /\
  (hd (x::xs) = x)
End


Definition TRANSACTIONS_def:
  TRANSACTIONS tg:real dtg tmine dtmine trans_in pending_tx trans_out =
    !t:real. (if (trans_in t = user) then
                 (if (dtg t = 0) then
                    (pending_tx t = (pending_tx t) ++ [ user ])
                  else
                    (trans_in t = no_user) /\ (dtg (t + 1) = dtg t - 1))
                    
              else
                 (trans_in t = no_user) /\ (dtg (t + 1) = tg)) 

                 /\

             (if ~(pending_tx t = []) then
                  (if (dtmine t = 0) then
                    (trans_out t = hd (pending_tx t))
                  else
                    (trans_out t = no_user) /\ (dtmine (t + 1) = dtmine t - 1))
              else
                  (trans_out t = no_user) /\ (dtmine (t + 1) = tmine))
End




(* MINING

  The mining model mines a transaction and then send it to its
  smart contract for execution.

*)

Definition MINING_def:
  MINING mine_in mine_out tm dtm = 
    !t:real. 
      if  (mine_in t = user) then
        (if (dtm t = 0) then
          mine_out t = user
        else
          (mine_out t = no_user) /\ (dtm (t + 1) = dtm t - 1))
      else
        (mine_out t = no_user) /\ (dtm (t + 1) = tm)

End




(* REGISTER CONTRACT

  The register contract model is where the tx gets executed and
  the results are sent back to the user. The transaction after
  execution should be prepared for adding to blocks and notify
  variable should be updated.

*)

Datatype:
  register = list user_data
End

Definition found_user_def:
  (found_user (user, [])  = F) /\
  (found_user (user, (x::xs)) = if (x = user) then T else found_user (user, xs))
End


Definition REGISTER_CONTRACT_def:
  REGISTER_CONTRACT contr_in contr_out register notify success te dte =
    !t:real.
      if (contr_in t = user) /\ ~(notify) then
        if (dte t = 0) then
          (if (found_user (user, register)) then
            ~(success) /\ (notify)
          else
            (success) /\ (notify) /\ (contr_out t = user))
        else
          (contr_in t = no_user) /\ (dte (t + 1) = dte t - 1)
      else
        (contr_in t = no_user) /\ (dte (t + 1) = te)


End




(* BLOCKS

  The blocks component is a list of blocks which is used to keep
  the record of transations. 

*)


Definition BLOCKS_def:
  BLOCKS blocks_in (blocks:real -> user list) tb dtb =
    !t:real.
      if (blocks_in t = user) then
        (if (dtb t = 0) then
          (blocks t = (blocks t) ++ [ user ])
        else
          (blocks_in t = no_user) /\ (dtb (t + 1) = dtb t - 1))
      else
         (blocks_in t = no_user) /\ (dtb (t + 1) = tb)

End




(* BLOCKCHAIN

  The blockchain model would a logical conjunction of four
  HOL definitions, each of which is an autonomous component of 
  the blockchain parameterized with time.

*)


Definition BLOCKCHAIN_def:
  BLOCKCHAIN trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register
   notify success pending_tx blocks tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc = 
    ((TRANSACTIONS tg dtg tmine dtmine trans_in pending_tx trans_out) /\ 
    (CHANNEL tc dtc trans_out mine_in) /\
    (MINING mine_in mine_out tm dtm) /\ 
    (CHANNEL tc dtc mine_out contr_in) /\
    (REGISTER_CONTRACT contr_in contr_out register notify success te dte) /\
    (CHANNEL tc dtc contr_out blocks_in) /\
    (BLOCKS blocks_in blocks tb dtb))
End




(* USER

  The user model is the essentially the user node making a
  transaction for registering an alias to its address.

  Possible considerations:

  - Remove the temporal property from user model (probably not)

*)

Definition USER_REG_CALL_def:
  USER_REG_CALL user_out reg_call notify tu dtu = 
    !t:real. 
      if (reg_call) /\ ~(notify) then
          (* Pass the name and address to the channel *)
          if (dtu t = 0) then
            (user_out t = user) /\ ~(reg_call)
          else
            (user_out t = no_user) /\ (dtu (t + 1) = dtu t - 1)
      else
          (* Keep some dummy values on the channel variables *)
          (user_out t = no_user) /\ (dtu (t + 1) = tu)
End



(* USER INTERACTION WITH BLOCKCHAIN

  This represents the complete system model (with the exception
  of the hacker model) as conjunction of user and blockchain
  model.

*)

Definition USER_INTERACT_BLOCKCHAIN_def:
  USER_INTERACT_BLOCKCHAIN reg_call user_out trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register notify success pending_tx blocks tu dtu tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc =
    ((USER_REG_CALL user_out reg_call notify tu dtu) /\ 
    (CHANNEL tc dtc user_out trans_in) /\
    (BLOCKCHAIN trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register notify success pending_tx blocks tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc))

End


(* Initial Conditions
 
   This definition will initialise the time variables to their
   starting values and begin the blockchain system with empty
   pending transactions and blocks
*)

Definition INIT_def:
  INIT user_out trans_in trans_out mine_in mine_out contr_in contr_out blocks_in pending_tx blocks tg dtg tm dtm te dte tb dtb tu dtu tmine dtmine tc dtc =
    ((user_out 0 = no_user) /\ (trans_in 0 = no_user) /\ (trans_out 0 = no_user) /\
     (mine_in 0 = no_user) /\ (mine_out 0 = no_user) /\ (contr_in 0 = no_user) /\
     (contr_out 0 = no_user) /\ (blocks_in 0 = no_user) /\ (pending_tx 0 = []) /\
     (blocks 0 = []) /\ (dtg 0 = tg) /\ (dtm 0 = tm) /\ (dte 0 = te) /\ (dtb 0 = tb) /\
     (dtu 0 = tu) /\ (dtmine 0 = tmine) /\ (dtc 0 = tc))
End



(* Live assumption
    reg_call = T /\ notify = F
    
    should be dealt later
*)


Definition CONTRACT_CALL_def:
  CONTRACT_CALL reg_call notify = (reg_call /\ ~notify)
End



(*
  HACKER

  The hacker is not gonna try to register with the user's name
  but instead, the hacker will only try to steal the user's alias

  *)


  (* SCENARIO: 2 *)

  (* We use this hacker definition with multiple time values
      and channels
     for example: time = tu + tc,      channel = user_out
                  time = tu + tc + tg, channel = trans_in
  *)

Definition HACKED_CHANNEL_def:
  HACKED_CHANNEL time channel
    = ?t:real. (t < time) ==> (channel t = user)
End


(* Vulnerability Verification Theorem *)
Theorem BLOCKCHAIN_CHANNEL_HACKED_1:
  !reg_call user_out trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register notify success pending_tx blocks tu dtu tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc.
  USER_INTERACT_BLOCKCHAIN reg_call user_out trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register notify success pending_tx blocks tu dtu tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc /\ CONTRACT_CALL reg_call notify
    ==> (HACKED_CHANNEL (tu + tc) user_out)
Proof
  REWRITE_TAC []
QED






Theorem BLOCKCHAIN_CHANNEL_HACKED_2:
  !reg_call user_out trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register notify success pending_tx blocks tu dtu tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc.
  USER_INTERACT_BLOCKCHAIN reg_call user_out trans_in trans_out mine_in mine_out contr_in contr_out blocks_in register notify success pending_tx blocks tu dtu tg dtg tmine dtmine tm dtm te dte tb dtb tc dtc /\ CONTRACT_CALL reg_call notify
    ==> (HACKED_CHANNEL (tu + tc + tg) trans_in)
Proof

QED
