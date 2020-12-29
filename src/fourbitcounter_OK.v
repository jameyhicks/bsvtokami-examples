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

Definition ruleMap0 (_: RegsT): string -> option string :=
  "increment" |-> "increment"; "done" |-> "done"; ||.
Definition ruleMap1 (_: RegsT): string -> option string :=
  "increment" |-> "increment"; "done" |-> "done"; ||.

Definition regMap (r: RegsT): RegsT.
  (* We are using tactics to build a map from register valuations in [impl] to register valuations in [spec]. *)
  kgetv "c.top"%string datav r (Bit 4) (M.empty _: RegsT).
  (* First, extract the value of [impl] register ["data"]. *)
  exact (M.add "c.top"%string (existT _ _ datav) (M.empty _)).
  (* Then, give the corresponding values of all registers for [spec]. *)
Defined.
Hint Unfold ruleMap0: MethDefs.
Hint Unfold ruleMap1: MethDefs.
Hint Unfold regMap: MethDefs. (* for kdecompose_regMap_init *)

Theorem fourbitcounter_0_OK :
   fourbitcount2.module'mkTb.mkTb "top" <<== fourbitcount2.module'spec.spec0 "top".
Proof.
    kinline_compute.
    kdecompose_nodefs regMap ruleMap0.
    kinvert.
    kinv_magic.
    * destruct wlt_dec. trivial. contradiction.
    * kinv_magic.
Qed.

Theorem fourbitcounter_1_OK :
   fourbitcount2.module'mkTb.mkTb "top" <<== fourbitcount2.module'spec.spec1 "top".
Proof.
    kinline_compute.
    kdecompose_nodefs regMap ruleMap1.
    kinvert.
    kinv_magic.
    * trivial.  kinv_magic.
   destruct wlt_dec. trivial. contradiction.
    * kinv_magic.
Qed.

Definition ruleMap (_: RegsT): string -> option string :=
  "increment" |-> "spec_rule"; "done" |-> "spec_rule"; ||.
Hint Unfold ruleMap: MethDefs.
Hint Unfold regMap: MethDefs. (* for kdecompose_regMap_init *)

Theorem fourbitcounter_OK :
   fourbitcount2.module'mkTb.mkTb "top" <<== fourbitcount2.module'spec.spec "top".

Proof.
kinline_compute.
kdecompose_nodefs regMap ruleMap.
kinv_magic.
admit. (* fixme: proof goes here *)

Admitted.

Theorem fourbitcounter_2_OK :
   fourbitcount2.module'spec.spec2 "top" <<== fourbitcount2.module'spec.spec2 "top".

Proof.
kinline_compute.
kdecompose_nodefs regMap ruleMap1.
kinv_magic.
admit. (* fixme proof *)
Admitted.

