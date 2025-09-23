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
        var st' := st.UpdateOrAdd(vNew, v');
        var stTransformed := context_in.AdjustState(st)[v := context_in.AdjustState(st).Eval(x)];

        assert stTransformed == context.AdjustState(st') by {
          context_in.AdjustStateSubstituteLemma(st, x);
        }

        assert context.IsSatisfiedOn(st') by {
          context_in.SubstituteIsDefinedOnLemma(x, vNew);
          DepthEqLemma(BVar(vNew), context_in.Substitute(x)); 
          
          context_in.Substitute(x).EvalDepthLemma(st, st');

          EvalEqLemma(BVar(vNew), context_in.Substitute(x), st');

          assert forall e <- context_in.ctx :: st.Eval(e) ==> st'.Eval(e) by 
          {
            forall e: Expr | e in context_in.ctx && st.Eval(e) ensures st'.Eval(e) {
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

  /**

  s := s0  
  bcont := (n1 s1); (n2 s2); (n3 s3); (n4 s4)

  WP (var n3 
        var n2 
          var n1 s0 
          s1 
        s2 
      s3) [All] ==
  WP (var n3 
        var n2 
          var n1 s0 
          s1 
        s2) [WP(s3, All)] ==
  WP (var n2 
        var n1 s0 
        s1 
      s2) [Upd(n3, WP(s3, All)), Upd(n3, WP(s3, All))] ==
  WP (var n2 
        var n1 s0 
        s1) [WP(s2, Upd(n3, WP(s3, All))), Upd(n3, WP(s3, All))] ==
  WP (var n1 s0 
      s1) [Upd(n2, WP(s2, Upd(n3, WP(s3, All)))), 
           Upd(n2, WP(s2, Upd(n3, WP(s3, All)))), 
                  Upd(n2, Upd(n3, WP(s3, All)))]] ==
  WP (var n1 s0) 
          [WP(s1,Upd(n2, WP(s2, Upd(n3, WP(s3, All))))), 
                 Upd(n2, WP(s2, Upd(n3, WP(s3, All)))), 
                  Upd(n2, Upd(n3, WP(s3, All)))]] ==
    WP (s0) 
          [Upd(n1, WP(s1,Upd(n2, WP(s2, Upd(n3, WP(s3, All)))))), 
           Upd(n1, WP(s1,Upd(n2, WP(s2, Upd(n3, WP(s3, All)))))), 
                 Upd(n1, Upd(n2, WP(s2, Upd(n3, WP(s3, All))))), 
                 Upd(n1, Upd(n2, Upd(n3, WP(s3, All))))]] ==

  
   */

  ghost function BlockWPSeq(bcont: Block.Continuation, post: iset<State>) : Omni.Continuation
    ensures |BlockWPSeq(bcont, post)| == |bcont| + 1
  {
    if bcont == [] then
      [post]
    else 
      var wpSeq := BlockWPSeq(bcont[1..], post);
      var wpNew := Omni.SeqWP(bcont[0].cont, wpSeq);
      var wpSeq := wpSeq.UpdateHead(wpNew);
      wpSeq.UpdateAndAdd(bcont[0].varsInScope)
  }

  lemma BlockWPSeqIdx(bcont: Block.Continuation, l: nat)
    requires l < |bcont|
    ensures BlockWPSeq(bcont, AllStates)[l + 1] == UpdateSet(bcont.VarsInScope(l), BlockWPSeq(bcont[l..], AllStates)[0])
  {
    if l != 0 {
      if |bcont| != 0 {
        var blockWP := BlockWPSeq(bcont[1..], AllStates);
        calc {
          BlockWPSeq(bcont, AllStates)[l + 1];
        ==
          blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP)).UpdateAndAdd(bcont[0].varsInScope)[l + 1];
        ==
          blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP)).Update(bcont[0].varsInScope)[l];
        == 
          UpdateSet(bcont[0].varsInScope, blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP))[l]);
        == { assert blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP))[l] == blockWP[l]; }
          UpdateSet(bcont[0].varsInScope, blockWP[l]);
        == 
          { assert blockWP[l] == UpdateSet(bcont[1..].VarsInScope(l - 1), BlockWPSeq(bcont[l..], AllStates)[0]) by {
              assert bcont[1..][l - 1..] == bcont[l..];
              BlockWPSeqIdx(bcont[1..], l - 1); 
          } }
          UpdateSet(bcont[0].varsInScope, UpdateSet(bcont[1..].VarsInScope(l - 1), BlockWPSeq(bcont[l..], AllStates)[0]));
        == { assert bcont.VarsInScope(l) == bcont[0].varsInScope + bcont[1..].VarsInScope(l - 1); }
          UpdateSet(bcont.VarsInScope(l), BlockWPSeq(bcont[l..], AllStates)[0]);
          }
        }
    } else {
      calc {
        UpdateSet(bcont.VarsInScope(0), BlockWPSeq(bcont[0..], AllStates)[0]);
      == 
        BlockWPSeq(bcont, AllStates)[0];
      ==
        BlockWPSeq(bcont, AllStates)[1];
      }
    }
  }

  ghost predicate BlockSem(s: seq<Stmt>, bcont: Block.Continuation, st: State, post: iset<State>) {
    Omni.SeqSem(s, st, BlockWPSeq(bcont, post))
  }


  method SeqVCGen(s: seq<Stmt>, context: Context, bcont: Block.Continuation) returns (VCs: seq<Expr>) 
    requires bcont.IsDefinedOn(|context.incarnation|)

    requires SeqIsDefinedOn(s, bcont.AllVarsInScope())
    requires SeqJumpsDefinedOn(s, |bcont|)

    requires bcont.VarsDefined()
    requires bcont.JumpsDefined()

    decreases SeqSize(s) + bcont.Size()
    // requires SeqIsDefinedOn(s, |context.incarnation|)
    //requires bcont.IsDefinedOn(|context.incarnation|)

    ensures
      (forall e <- VCs :: e.Holds()) ==> 
        forall st: State:: 
          context.IsSatisfiedOn(st) ==> 
          BlockSem(s, bcont, context.AdjustState(st), AllStates)
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
        if (forall e <- VCs :: e.Holds()) {
          forall st: State | context.IsSatisfiedOn(st)
            ensures BlockSem([], bcont, context.AdjustState(st), AllStates) {
            assert forall i <- context'.incarnation :: i in context.incarnation;
            assert context'.AdjustState(st) == Tail(varsToDelete, context.AdjustState(st));
          }
        }
      }
    } else {
      var stmt, cont := s[0], s[1..];
      assert s == [stmt] + cont;
      SeqSizeSplitLemma(s);
      SeqFunConcatLemmas([stmt], cont);
      if stmt.Single() {
        var VCstmt, VCcont, context';
        context', VCstmt := VCGen(stmt, context);
        VCcont := SeqVCGen(cont, context', bcont);
        VCs := VCstmt + VCcont;
        if (forall e <- VCs :: e.Holds()) {
          forall st: State | context.IsSatisfiedOn(st) 
            ensures BlockSem(s, bcont, context.AdjustState(st), AllStates) {
          }
        }
      } else {
        // assume {:axiom} false;
        match stmt 
        case Seq(ss) =>
          VCs := SeqVCGen(ss + cont, context, bcont) by {
            // decreases
            SeqFunConcatLemmas(ss, cont);
          }
          if (forall e <- VCs :: e.Holds()) {
            forall st: State | context.IsSatisfiedOn(st) 
              ensures BlockSem(s, bcont, context.AdjustState(st), AllStates) {
                Omni.SeqLemma(ss, cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates));
            }
          }
        case Choice(ss0, ss1) =>
          var VCs0 := SeqVCGen([ss0] + cont, context, bcont);
          var VCs1 := SeqVCGen([ss1] + cont, context, bcont);
          VCs := VCs0 + VCs1;
          if (forall e <- VCs :: e.Holds()) {
            forall st: State | context.IsSatisfiedOn(st) 
              ensures BlockSem(s, bcont, context.AdjustState(st), AllStates) {
              
            }
          }
        case NewScope(n, body) =>
          var vNew, context' := context.AddVars(n);
          VCs := SeqVCGen([body], context', bcont.Update(cont, n)) by {
            // decreases
            bcont.UpdateSize(cont, n);
            assert SeqSize([body]) == body.Size();
          }
          if (forall e <- VCs :: e.Holds()) {
            forall st: State | context.IsSatisfiedOn(st) 
              ensures BlockSem(s, bcont, context.AdjustState(st), AllStates) {
              var blockWP := BlockWPSeq(bcont, AllStates);
              var contWP := Omni.SeqWP(cont, blockWP);
              var updWP := ([contWP] + blockWP.UpdateHead(contWP)).Update(n);
              assert Omni.Sem(NewScope(n, body), context.AdjustState(st), blockWP.UpdateHead(contWP)) by {
                forall vs: State | |vs| == n 
                  ensures Omni.Sem(body, context.AdjustState(st).Update(vs), blockWP.UpdateHead(contWP).UpdateAndAdd(n)) {
                  var st' := st.MergeAt(vNew, vs);
                  assert context'.IsSatisfiedOn(st') by {
                    forall e: Expr | e in context.ctx && st.Eval(e) ensures st'.Eval(e) {
                      e.EvalDepthLemma(st, st');
                    }
                  }
                  calc {
                    Omni.SeqSem([body], context'.AdjustState(st'), updWP);
                  == { assert context.AdjustState(st).Update(vs) == context'.AdjustState(st'); }
                    Omni.SeqSem([body], context.AdjustState(st).Update(vs), updWP);
                  ==> { Omni.SeqSemSingle(body, context.AdjustState(st).Update(vs), updWP); }
                    Omni.Sem(body, context.AdjustState(st).Update(vs), updWP);
                  }
                }
              }
              Omni.SemNest(NewScope(n, body), cont, context.AdjustState(st), blockWP);
            }
          }
        case Escape(l) =>
          var bcont' := bcont.Update(cont, 0);
          var varsToDelete := bcont'.VarsInScope(l);
          var context' := context.Delete(varsToDelete) by {
            bcont'.VarsInScopeLeqAll(l);
          }
          VCs := SeqVCGen([], context', bcont'[l..]) by {
            // decreases
            bcont'.SizePrefix(l);
            // IsDefinedOn
            bcont'.VarsInScopeLeqAll(l);
            // JumpsDefined
            assert bcont'[l..].JumpsDefined() && bcont'[l..].VarsDefined() by {
              if l != 0 {
                assert bcont'[l..] == bcont[l - 1..];
                bcont.DefinedPrefix(l - 1);
              }
            }
          }
          if (forall e <- VCs :: e.Holds()) {
            forall st: State | context.IsSatisfiedOn(st)
              ensures Omni.SeqSem([Escape(l)] + cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates)) {
              Omni.SemNest(Escape(l), cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates)) by {
                var blockWP := BlockWPSeq(bcont, AllStates);
                var updBlockWP := blockWP.UpdateHead(Omni.SeqWP(cont, blockWP));
                calc {
                  context.AdjustState(st) in updBlockWP[l];
                  { if l != 0 { BlockWPSeqIdx(bcont, l - 1); } }
                  context.AdjustState(st) in UpdateSet(bcont'.VarsInScope(l), BlockWPSeq(bcont'[l..], AllStates)[0]);
                  Tail(bcont'.VarsInScope(l), context.AdjustState(st)) in BlockWPSeq(bcont'[l..], AllStates)[0];
                  { assert context'.AdjustState(st) == Tail(bcont'.VarsInScope(l), context.AdjustState(st)); }
                  context'.AdjustState(st) in BlockWPSeq(bcont'[l..], AllStates)[0];
                  { assert context'.IsSatisfiedOn(st) by {
                    forall i | i in context'.incarnation ensures i < |st| {
                      assert i in context.incarnation;
                  } } }
                  true;
                }
              }
            }
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
 