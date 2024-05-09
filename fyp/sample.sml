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


Definition USER_REG_CALL_def:
  USER_REG_CALL reg_called c_data tp dtp notified = 
    !t:real. 
      if (reg_called) /\ ~(notified) then
          (* Pass the name and address to the channel *)
          if (dtp t = 0) then
            (c_data t = user) /\ (reg_called = F)
          else
            (c_data t = no_user) /\ (dtp (t + 1) = dtp t - 1)
      else
          (* Keep some dummy values on the channel variables *)
          (c_data t = no_user) /\ (dtp (t + 1) = tp)
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
  !in_data out_data tc dtc notified. CHANNEL_REG_CALL in_data out_data tc dtc notified /\ ~(notified) /\ (!t. dtc t = 0) ==> (!t:real. out_data t = in_data)
Proof
  METIS_TAC [CHANNEL_REG_CALL_def]
  GEN_TAC
QED



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
