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


(* User Model *)
(* Time Interval = 1, use a variable in future *)
Definition USER_REG_CALL_def:
  USER_REG_CALL register notify tu dtu = 
    !t:real. 
      if (register) /\ ~(notify) then
          (* Pass the name and address to the channel *)
          if (dtu t = 0) then
            (channel t = user) /\ ~(register)
          else
            (channel t = no_user) /\ (dtu (t + 1) = dtu t - 1)
      else
          (* Keep some dummy values on the channel variables *)
          (channel t = no_user) /\ (dtu (t + 1) = tu)
End






Definition CHANNEL_REG_CALL_def:
  CHANNEL_REG_CALL in_data out_data tc dtc notified =
    !t:real.
      if ~(notified) then
        if (dtc t = 0) then
          (out_data t = in_data)
        else
          (out_data t = no_user) /\ (dtc (t + 1) = dtc t - 1)
      else
        (out_data t = no_user) /\ (dtc (t + 1) = tc)
End


(* Verification Properties *)

(* Work in Progress *)
Theorem SC_channel_in_out:
  !in_data out_data tc dtc notified. CHANNEL_REG_CALL in_data out_data tc dtc notified ==> (?t:real. out_data t = in_data)
Proof
  STRIP_TAC
  RW_TAC arith_ss [CHANNEL_REG_CALL_def]
  RW_TAC std_ss [CHANNEL_REG_CALL_def]
  RW_TAC real_ss [CHANNEL_REG_CALL_def]
  METIS_TAC [CHANNEL_REG_CALL_def]

  ASM_REWRITE_TAC []



Datatype:
  register = list user_data
End

Definition found_user_def:
  (found_user (user, [])  = F) /\
  (found_user (user, (x::xs)) = if (x = user) then T else found_user (user, xs))
End



Definition REGISTER_CONTRACT_def:
  REGISTER_CONTRACT reg userD notified success =
    !t:real.
      if ~(notified) then
        if (found_user (userD, reg)) then
          (success t = F) /\ (notified = T)
        else
          (success t = T) /\ (notified = T)
      else
        T
End 

