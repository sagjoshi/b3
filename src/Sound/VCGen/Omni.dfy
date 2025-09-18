module VCGenOmni {
  import opened Defs
  import opened Context
  import Omni

  /*method VCGen(s: Stmt, context_in: Context) returns (context: Context, VCs: seq<Expr>) 
    requires s.IsDefinedOn(|context_in.incarnation|)
    requires s.Single()

    ensures |context_in.incarnation| <= |context.incarnation|
    ensures (forall e <- VCs :: e.Holds()) ==> 
      forall st: State :: 
        context_in.IsSatisfiedOn(st) ==>
        Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels)
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
      if (forall e <- VCs :: e.Holds()) {
        assert context.MkEntailment(e).Holds();
        forall st: State | context.IsSatisfiedOn(st) 
          ensures Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels) {
          assert context.AdjustState(st).Eval(e) by { 
            EvalConjLemma(context.ctx, st);
            context.AdjustStateSubstituteLemma(st, e);
          }
        }
      }
    case Assume(e) =>
      context := context_in.Add(e);
      VCs := [];
      forall st: State | context_in.IsSatisfiedOn(st) 
        ensures Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels) {
        if context.AdjustState(st).Eval(e) {
          context_in.SubstituteIsDefinedOnLemma(e, |st|);
          context_in.AdjustStateSubstituteLemma(st, e);
        }
      }
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
      forall st: State | context_in.IsSatisfiedOn(st) 
        ensures Omni.Sem(s, context_in.AdjustState(st), context.AdjustedModels) {
        context_in.SubstituteIsDefinedOnLemma(x, |st|);
        var v' := st.Eval(context_in.Substitute(x));
        var st' := st + [v'];
        var stTransformed := context_in.AdjustState(st)[v := context_in.AdjustState(st).Eval(x)];

        assert stTransformed == context.AdjustState(st') by {
          context_in.AdjustStateSubstituteLemma(st, x);
        }

        assert context.IsSatisfiedOn(st') by {
          context_in.SubstituteIsDefinedOnLemma(x, |st'|);
          DepthEqLemma(BVar(vNew), context_in.Substitute(x)); 
          
          context_in.Substitute(x).EvalDepthLemma(st, st');
          EvalEqLemma(BVar(vNew), context_in.Substitute(x), st');
          assert forall e: Expr :: e.IsDefinedOn(|st|) ==> 
            st.Eval(e) ==> st'.Eval(e) by 
          {
            forall e: Expr | e.IsDefinedOn(|st|) && st.Eval(e) { 
              e.EvalDepthLemma(st, st');
            }
          }
        }
      }
    // case Pop => 
    //   context := context_in.(incarnation := SeqTail(context_in.incarnation));
    //   VCs := [];
  }*/

/*method SeqVCGen(s: seq<Stmt>, context: Context) returns (VCs: seq<Expr>) 
  requires SeqIsDefinedOn(s, |context.incarnation|)

  decreases SeqSize(s)
  ensures
    (forall e <- VCs :: e.Holds()) ==> 
      forall st: State:: 
        context.IsSatisfiedOn(st) ==> Omni.SeqSem(s, context.AdjustState(st), AllStates)
  {
    if s == [] { 
      VCs := []; 
      return; 
    }
    var stmt, cont := s[0], s[1..];
    assert s == [stmt] + cont;
    SeqSizeSplitLemma(s);
    if stmt.Single() {
      var VCstmt, VCcont, context';
      context', VCstmt := VCGen(stmt, context);
      VCcont := SeqVCGen(cont, context');
      VCs := VCstmt + VCcont;
    } else {
      match stmt 
      case Seq(ss) =>
        SeqFunConcatLemmas(ss, cont);
        VCs := SeqVCGen(ss + cont, context);
        if (forall e <- VCs :: e.Holds()) {
          forall st: State | context.IsSatisfiedOn(st) {
            Omni.SeqLemma(ss, cont, context.AdjustState(st), AllStates);
          }
        }
      case Choice(ss0, ss1) =>
        var VCs0 := SeqVCGen([ss0] + cont, context);
        var VCs1 := SeqVCGen([ss1] + cont, context);
        VCs := VCs0 + VCs1;
      case VarDecl(v, s) =>
        var vNew, context' := context.AddVar();
        VCs := SeqVCGen([s] + WithPop(cont), context') by {
          SeqFunConcatLemmas([Pop], cont);
        }
        if (forall e <- VCs :: e.Holds()) {
          forall st: State | context.IsSatisfiedOn(st)
            ensures Omni.SeqSem([VarDecl(v, s)] + cont, context.AdjustState(st), AllStates) {
            Omni.SemNest(VarDecl(v, s), cont, context.AdjustState(st), AllStates) by {
              forall b: Value ensures Omni.Sem(s, context.AdjustState(st).Update(b), 
                UpdateSet(Omni.SeqWP(cont, AllStates)))
              { 
                assert context.AdjustState(st).Update(b) == context'.AdjustState(st + [b]);
                assert context'.IsSatisfiedOn(st + [b]) by {
                  forall e <- context'.ctx 
                    ensures (st + [b]).Eval(e) {
                      e.EvalDepthLemma(st, st + [b]);
                  }
                }
                Omni.SemCons(s, context.AdjustState(st).Update(b), 
                  Omni.SeqWP(WithPop(cont), AllStates), 
                  UpdateSet(Omni.SeqWP(cont, AllStates))) by 
                {
                  forall st | Omni.SeqSem(WithPop(cont), st, AllStates) 
                    ensures Omni.SeqSem(cont, Tail(st), AllStates) {
                    Omni.SeqFrameLemmaAll(cont, v, st);
                  }
                }
              }
            }
          }
        }
      case WithPop(ss) => assume {:axiom} false;
    }
  }*/
}