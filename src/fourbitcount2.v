Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Kami.PrimFifo.
Require Import Init.Nat.
Require Import Bsvtokami.

Set Implicit Arguments.
Definition Int := Bit.
Open Scope string.

Module module'mkTb.
  Section section'mkTb.
    Variable instancePrefix : string.
    Definition mkTb := (MODULE {
    Register (instancePrefix--"c") : (Bit 4) <- Default
    with 
    Rule ("increment") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c < $15) ;
        Write (instancePrefix--"c") : Bit 4 <- #c + $1 ;
        Call unused : Void <- (MethodSig ("$display") ((Bit 4)) : Void) (#c) ;
    Retv
    )

    with 
    Rule ("done") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c == $15) ;
        Call unused : Void <- (MethodSig ("$finish") () : Void)  () ;

    Retv
    )

    }).

    Definition mkTb1 := (MODULE {
    Register (instancePrefix--"c") : (Bit 4) <- Default
    with 
    Rule ("increment") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        If (#c < $15) then (
	    Write (instancePrefix--"c") : Bit 4 <- #c + $1 ;
	    Call unused : Void <- (MethodSig ("$display") ((Bit 4)) : Void) (#c) ;
            Retv ) else (Retv) ;
         Retv
    )

    with 
    Rule ("done") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        If (#c == $15)  then (Call unused : Void <- (MethodSig ("$finish") () : Void)  () ; Retv ) else (Retv) ;
        Retv
    )

    }).
  End section'mkTb.
End module'mkTb.

Module module'spec.
  Section section'spec.
  Variable instancePrefix : string.
  Definition spec:=
  MODULE {
     Register (instancePrefix -- "c") : Bit 4 <- Default
     
    with Rule "spec_rule" :=
       Read c : Bit 4 <- (instancePrefix--"c") ;
       If (#c < $15) then (Write (instancePrefix--"c") : Bit 4 <- #c + $1 ; Call unused1 : Void <- (MethodSig ("$display") ((Bit 4)):Void) (#c); Retv ) else ( Retv );
       If (#c == $15) then (Call unused : Void <- (MethodSig ("$finish") () : Void)  () ; Retv ) else (Retv);
      Retv
    }.

  Definition spec0 :=
  MODULE {
     Register (instancePrefix -- "c") : Bit 4 <- Default
   with  
    Rule ("increment") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c < $15) ;
        Write (instancePrefix--"c") : Bit 4 <- #c + $1 ;
        Call unused : Void <- (MethodSig ("$display") ((Bit 4)) : Void) (#c) ;
    Retv
    )
    with 
    Rule ("done") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c == $15) ;
        Call unused : Void <- (MethodSig ("$finish") () : Void)  () ;
        Retv
    )
   }.

  Definition spec1 :=
  MODULE {
     Register (instancePrefix -- "c") : Bit 4 <- Default
   with  
    Rule ("increment") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c < $15) ;
        Write (instancePrefix--"c") : Bit 4 <- #c + $1 ;
        Call unused : Void <- (MethodSig ("$display") ((Bit 4)) : Void) (#c) ;
    Retv
    )
    with 
    Rule ("done") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c == $15) ;
        Call unused : Void <- (MethodSig ("$finish") () : Void)  () ;

    Retv
    )
    with 
    Rule ("extra") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        Assert(#c == $7) ;
        Call unused : Void <- (MethodSig ("extra") () : Void)  () ;

    Retv
    )
   }.

  Definition spec2 :=
  MODULE {
     Register (instancePrefix -- "c") : Bit 4 <- Default
   with  
    Rule ("increment") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        If (#c < $15) then (
	    Write (instancePrefix--"c") : Bit 4 <- #c + $1 ;
	    Call unused : Void <- (MethodSig ("$display") ((Bit 4)) : Void) (#c) ;
            Retv ) else (Retv) ;
         Retv
    )

    with 
    Rule ("done") := 
    (
        Read c : (Bit 4) <- (instancePrefix--"c") ;
        If (#c == $15)  then (Call unused : Void <- (MethodSig ("$finish") () : Void)  () ; Retv ) else (Retv) ;
        Retv
    )
  }.
   End section'spec.
End module'spec.

Hint Unfold module'mkTb.mkTb : ModuleDefs.
Hint Unfold module'mkTb.mkTb1 : ModuleDefs.

Lemma impl_ModEquiv:
  ModPhoasWf (module'mkTb.mkTb "top").
Proof. kequiv. Qed.
Hint Resolve impl_ModEquiv.

Lemma impl1_ModEquiv:
  ModPhoasWf (module'mkTb.mkTb1 "top").
Proof. kequiv. Qed.
Hint Resolve impl1_ModEquiv.

Hint Unfold module'spec.spec : ModuleDefs.
Lemma spec_ModEquiv:
  ModPhoasWf (module'spec.spec "top").
Proof. kequiv. Qed.
Hint Resolve spec_ModEquiv.

Hint Unfold module'spec.spec0 : ModuleDefs.
Lemma spec0_ModEquiv:
  ModPhoasWf (module'spec.spec0 "top").
Proof. kequiv. Qed.
Hint Resolve spec0_ModEquiv.

Hint Unfold module'spec.spec1 : ModuleDefs.
Lemma spec1_ModEquiv:
  ModPhoasWf (module'spec.spec1 "top").
Proof. kequiv. Qed.
Hint Resolve spec1_ModEquiv.

Hint Unfold module'spec.spec2 : ModuleDefs.
Lemma spec2_ModEquiv:
  ModPhoasWf (module'spec.spec2 "top").
Proof. kequiv. Qed.
Hint Resolve spec2_ModEquiv.
