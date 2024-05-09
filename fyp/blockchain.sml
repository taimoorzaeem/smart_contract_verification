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
  TRANSACTIONS tg dtg get_tx pending_tx mine_tx =
    !t:real. (if (get_tx t = user) then
                 (if (dtg t = 0) then
                    (pending_tx t = (pending_tx t) ++ [ user ])
                  else
                    (get_tx t = no_user) /\ (dtg (t + 1) = dtg t - 1))
                    
              else
                 (get_tx t = no_user) /\ (dtg (t + 1) = tg)) 

                 /\

             (if ~(pending_tx t = []) then
                  (mine_tx t = hd (pending_tx t))
              else
                  T)
End




(* MINING

  The mining model mines a transaction and then send it to its
  smart contract for execution.

*)

Definition MINING_def:
  MINING mine_tx exec_tx tm dtm = 
    !t:real. 
      (if (mine_tx t = user) then
        (if (dtm t = 0) then
          exec_tx t = user
        else
          (exec_tx t = no_user) /\ (dtm (t + 1) = dtm t - 1))
      else
        (exec_tx t = no_user) /\ (dtm (t + 1) = tm))

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
  REGISTER_CONTRACT exec_tx block_tx register notify success te dte =
    !t:real.
      if (exec_tx t = user) /\ ~(notify) then
        if (dte t = 0) then
          (if (found_user (user, register)) then
            ~(success) /\ (notify)
          else
            (success) /\ (notify)) /\ (block_tx t = user)
        else
          (exec_tx t = no_user) /\ (dte (t + 1) = dte t - 1)
      else
        (exec_tx t = no_user) /\ (dte (t + 1) = te)


End




(* BLOCKS

  The blocks component is a list of blocks which is used to keep
  the record of transations. 

*)


Definition BLOCKS_def:
  BLOCKS block_tx blocks tb dtb =
    !t:real.
      if (block_tx t = user) then
        (if (dtb t = 0) then
          (blocks t = (blocks t) ++ [ user ])
        else
          (block_tx t = no_user) /\ (dtb (t + 1) = dtb t - 1))
      else
         (block_tx t = no_user) /\ (dtb (t + 1) = tb)

End




(* BLOCKCHAIN

  The blockchain model would a logical conjunction of four
  HOL definitions, each of which is an autonomous component of 
  the blockchain parameterized with time.

*)


Definition BLOCKCHAIN_def:
  BLOCKCHAIN get_tx mine_tx exec_tx block_tx register notify success pending_tx blocks tg dtg tm dtm te dte tb dtb = 
    ((TRANSACTIONS tg dtg get_tx pending_tx mine_tx) /\ 
    (MINING mine_tx exec_tx tm dtm) /\ 
    (REGISTER_CONTRACT exec_tx block_tx register notify success te dte) /\
    (BLOCKS block_tx blocks tb dtb))
End




(* USER

  The user model is the essentially the user node making a
  transaction for registering an alias to its address.

*)

Definition USER_REG_CALL_def:
  USER_REG_CALL get_tx reg_call notify tu dtu = 
    !t:real. 
      if (reg_call) /\ ~(notify) then
          (* Pass the name and address to the channel *)
          if (dtu t = 0) then
            (get_tx t = user) /\ ~(reg_call)
          else
            (get_tx t = no_user) /\ (dtu (t + 1) = dtu t - 1)
      else
          (* Keep some dummy values on the channel variables *)
          (get_tx t = no_user) /\ (dtu (t + 1) = tu)
End



(* USER INTERACTION WITH BLOCKCHAIN

  This represents the complete system model (with the exception
  of the hacker model) as conjunction of user and blockchain
  model.

*)


Definition USER_INTERACT_BLOCKCHAIN_def:
  USER_INTERACT_BLOCKCHAIN reg_call tu dtu get_tx mine_tx exec_tx blocks_tx register notify success pending_tx blocks tg dtg tm dtm te dte tb dtb =
    ((USER_REG_CALL get_tx reg_call notify tu dtu) /\ 
    (BLOCKCHAIN get_tx mine_tx exec_tx blocks_tx register notify success pending_tx blocks tg dtg tm dtm te dte tb dtb))

End


(* Initial Conditions
  
*)

Definition INIT_def:
  INIT get_tx mine_tx exec_tx block_tx pending_tx blocks tg dtg tm dtm te dte tb dtb tu dtu =
    ((get_tx 0 = no_user) /\ (mine_tx 0 = no_user) /\ (exec_tx 0 = no_user) /\ (block_tx 0 = no_user) /\ (pending_tx 0 = []) /\ (blocks 0 = []) /\ (dtg 0 = tg) /\ (dtm 0 = tm) /\ (dte 0 = te) /\ (dtb 0 = tb) /\ (dtu 0 = tu))
End



(* Live assumption
    reg_call = T /\ notify = F
    
    should be dealt later
*)

