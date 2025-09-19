module VCGenOmni {
  import opened Defs
  import opened Context
  import Block
  import Omni

  method VCGen(s: Stmt, context_in: Context) returns (context: Context, VCs: seq<Expr>) 
    requires s.IsDefinedOn(|context_in.incarnation|)
    requires s.Single()
    ensures |context_in.incarnation| <= |context.incarnation|
    ensures (forall e <- VCs :: e.Holds()) ==> 
      forall st: State :: 
        context_in.IsSatisfiedOn(st) ==>
        Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels)
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
      if (forall e <- VCs :: e.Holds()) {
        assert context.MkEntailment(e).Holds();
        forall st: State | context.IsSatisfiedOn(st) 
          ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels) {
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
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels) {
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
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels) {
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
  }

  /**
    vars n;
      A; 
      vars k;
->      B; 
        vars l;
          C;
        D;
      E;
    F


    SeqVCGen(
      (B; (vars l; C); D), 
      |incr| = n + k, 
      [(k, E); (n, F)]
    )
      
   */

  // function BlockWP(bcont: Block.Continuation, scont: Omni.Continuation) : iset<Omni.Continuation> 
  //   requires |bcont| == |scont|
  // {
  //   iset posts: Omni.Continuation | 
  //     && |posts| == |bcont|
  //     && forall i: nat :: i < |bcont| ==> posts[i] 
  // }

  method SeqVCGen(s: seq<Stmt>, context: Context, bcont: Block.Continuation) returns (VCs: seq<Expr>) 
    requires bcont.IsDefinedOn(|context.incarnation|)

    requires SeqIsDefinedOn(s, bcont.AllVarsInScope())
    requires SeqJumpsDefinedOn(s, |bcont|)

    requires bcont.VarsDefined()
    requires bcont.JumpsDefined()

    decreases SeqSize(s) + bcont.Size()
    // requires SeqIsDefinedOn(s, |context.incarnation|)
    //requires bcont.IsDefinedOn(|context.incarnation|)

    // ensures
    //   (forall e <- VCs :: e.Holds()) ==> 
    //     forall st: State:: 
    //       context.IsSatisfiedOn(st) ==> 
    //         && Omni.Sem(s, context.AdjustState(st), scont)
    //         &&  Omni.SeqSem(s, context.AdjustState(st), AllStates)
  {
    if s == [] { 
      if bcont == [] {
        VCs := [];
        return;
      } else {
        var varsToDelete := bcont[0].varsInScope;
        var cont := bcont[0].cont;
        var context' := context.Delete(varsToDelete);
        VCs := SeqVCGen(cont, context', bcont[1..]);
      }
    } else {
      var stmt, cont := s[0], s[1..];
      assert s == [stmt] + cont;
      SeqSizeSplitLemma(s);
      SeqFunConcatLemmas([stmt], cont);
      if stmt.Single() {
        var VCstmt, VCcont, context';
        context', VCstmt := VCGen(stmt, context) by {
            // assume {:axiom} false;
        }
        VCcont := SeqVCGen(cont, context', bcont);
        VCs := VCstmt + VCcont;
      } else {
        match stmt 
        case Seq(ss) =>
          VCs := SeqVCGen(ss + cont, context, bcont) by {
            // decreases
            SeqFunConcatLemmas(ss, cont);
          }
        case Choice(ss0, ss1) =>
          var VCs0 := SeqVCGen([ss0] + cont, context, bcont);
          var VCs1 := SeqVCGen([ss1] + cont, context, bcont);
          VCs := VCs0 + VCs1;
        case NewScope(n, body) =>
          var context' := context.AddVars(n);
          VCs := SeqVCGen([body], context', bcont.Update(cont, n)) by {
            // decreases
            bcont.UpdateSize(cont, n);
            assert SeqSize([body]) == body.Size();
          }
        case Escape(l) =>
          var varsToDelete := bcont.VarsInScope(l);
          var context' := context.Delete(varsToDelete) by {
            bcont.VarsInScopeLeqAll(l);
          }
          VCs := SeqVCGen([], context', bcont[l..]) by {
            // decreases
            bcont.SizePrefix(l);
            // IsDefinedOn
            bcont.VarsInScopeLeqAll(l);
            // JumpsDefined
            bcont.DefinedPrefix(l);
          }
      }
    }
  }
}

      
      // match stmt 
      // case Seq(ss) =>
      //   SeqFunConcatLemmas(ss, cont);
      //   VCs := SeqVCGen(ss + cont, context);
      //   if (forall e <- VCs :: e.Holds()) {
      //     forall st: State | context.IsSatisfiedOn(st) {
      //       Omni.SeqLemma(ss, cont, context.AdjustState(st), AllStates);
      //     }
      //   }
      // case Choice(ss0, ss1) =>
      //   var VCs0 := SeqVCGen([ss0] + cont, context);
      //   var VCs1 := SeqVCGen([ss1] + cont, context);
      //   VCs := VCs0 + VCs1;
      // case VarDecl(v, s) =>
      //   var vNew, context' := context.AddVar();
      //   VCs := SeqVCGen([s] + [WithPop(cont)], context') by {
      //     SeqFunConcatLemmas([s], [WithPop(cont)]);
      //   }
      //   if (forall e <- VCs :: e.Holds()) {
      //     forall st: State | context.IsSatisfiedOn(st)
      //       ensures Omni.SeqSem([VarDecl(v, s)] + cont, context.AdjustState(st), AllStates) {
      //       Omni.SemNest(VarDecl(v, s), cont, context.AdjustState(st), AllStates) by {
      //         forall b: Value ensures Omni.Sem(s, context.AdjustState(st).Update(b), 
      //           UpdateSet(Omni.SeqWP(cont, AllStates)))
      //         { 
      //           assert context.AdjustState(st).Update(b) == context'.AdjustState(st + [b]);
      //           assert context'.IsSatisfiedOn(st + [b]) by {
      //             forall e <- context'.ctx 
      //               ensures (st + [b]).Eval(e) {
      //                 e.EvalDepthLemma(st, st + [b]);
      //             }
      //           }
      //           Omni.SemCons(s, context.AdjustState(st).Update(b), 
      //             Omni.SeqWP([WithPop(cont)], AllStates), 
      //             UpdateSet(Omni.SeqWP(cont, AllStates))) by 
      //           {
      //             forall st | Omni.SeqSem([WithPop(cont)], st, AllStates) 
      //               ensures Omni.SeqSem(cont, Tail(st), AllStates) {
      //               Omni.SeqFrameLemmaAll(cont, v, st);
      //             }
      //           }
      //         }
      //       }
      //     }
      //   }
 