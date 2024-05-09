
(* System Properties for verification *)

Theorem T_EQUAL_TU:
  !t. t = tu ==> (user_out t = user)
Proof
  GEN_TAC
  >> STRIP_TAC
  >> ASM_REWRITE_TAC []
  >> ONCE_REWRITE_TAC [GSYM INIT_def]


QED


!t. t = tu + tc ==> (trans_in t = user)


!t. t = tu + tc + tg ==> (last (pending_tx t) = user)


!t. t = tu + tc + tg + tmine ==> (trans_out t = user)


!t. t = tu + tc + tg + tmine + tc ==> (mine_in t = user)


!t. t = tu + tc + tg + tmine + tc + tm ==> (mine_out t = user)


!t. t = tu + tc + tg + tmine + tc + tm + tc ==> (contr_in t = user)


!t. t = tu + tc + tg + tmine + tc + tm + tc + te ==> (contr_out t = user)


!t. t = tu + tc + tg + tmine + tc + tm + tc + te + tc ==> (blocks_in t = user)


!t. t = tu + tc + tg + tmine + tc + tm + tc + te + tc + tb ==> (last (blocks t) = user)
