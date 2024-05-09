 (* Transactions Properties *)

 (!txs. PENDING_TX txs (LENGTH txs) = [])

(!pending_tx mine. TRANSACTIONS pending_tx mine ==>  
    (!t. pending_tx t = [] ==> pending_tx (t+1) = []))

(* Channel Properties *)

(!tc dtc input output. CHANNEL tc dtc input output
  ==> ~(t < tc) ==> output (t + tc) = input t)

(* Right combined properties of multiple processes*)

(* The time difference between the values of pending_tx
   and mine is tc1 time units *)

(!txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks.
  BLOCKCHAIN_SYSTEM txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks
    ==> (!t. pending_tx t = mine (t+tc1)))

(* The time difference between the values of mine
   and sc_tx is tc2 time units *)

(!txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks.
  BLOCKCHAIN_SYSTEM txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks
    ==> (!t. mine t = sc_tx (t+tc2)))

(* The time difference between the values of sc_tx
   and blocks is tc3 time units *)

(!txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks.
  BLOCKCHAIN_SYSTEM txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks
    ==> (!t. sc_tx t = blocks (t+tc3)))

(* The time difference between the values of pending_tx
   and sc_tx is tc1+tc2 time units *)

(!txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks.
  BLOCKCHAIN_SYSTEM txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks
    ==> (!t. pending_tx t = sc_tx (t+tc1+tc2)))

(* The time difference between the values of mine
   and blocks is tc2+tc3 time units *)

(!txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks.
  BLOCKCHAIN_SYSTEM txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks
    ==> (!t. mine t = blocks (t+tc2+tc3)))

(* The time difference between the values of pending_tx
   and mine is tc1 time units *)

(!txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks.
  BLOCKCHAIN_SYSTEM txs pending_tx success tc1 dtc1 tc2 dtc2
  tc3 dtc3 ch1 ch2 ch3 mine sc_tx reg block_tx blocks
    ==> (!t. pending_tx t = blocks (t+tc1+tc2+tc3)))
