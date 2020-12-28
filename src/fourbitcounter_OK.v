Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Kami.PrimFifo.
Require Import Init.Nat.

Require Import fourbitcount2.

Set Implicit Arguments.

Theorem fourbitcounter_OK :
   fourbitcount2.spec.spec "top" <<== fourbitcount2.module'mkTb.mkTb "top".

Proof.
admit. (* fixme: proof goes here *)

Admitted.
