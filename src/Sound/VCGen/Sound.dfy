module VCGenOmni' {
  import opened Utils
  import M = Model
  import opened AST
  import opened State
  import opened Context'
  import opened Expr
  import Block'
  import Omni
  import AssignmentTarget'

  method VCGen(s: Stmt, context_in: Context) returns (context: Context, VCs: seq<Expr>) 
    requires s.IsDefinedOn(|context_in.incarnation|)
    requires s.Single()
    ensures |context_in.incarnation| <= |context.incarnation|
    ensures (forall e <- VCs :: e.Holds()) ==> 
      forall st: State :: 
        context_in.IsSatisfiedOn(st) ==>
        Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels())
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
      if (forall e <- VCs :: e.Holds()) {
        // assert context.MkEntailment(e).Holds();
        forall st: State | context.IsSatisfiedOn(st) 
          ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels()) {
          context.MkEntailmentLemma(e, st);
        }
      }
    case Assume(e) =>
      context := context_in.Add(e);
      VCs := [];
      forall st: State | context_in.IsSatisfiedOn(st) 
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels()) {
        if e.HoldsOn(context.AdjustState(st)) {
          context_in.SubstituteIsDefinedOnLemma(e, |st|);
          context_in.AdjustStateSubstituteLemma(st, e);
        }
      }
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
      forall st: State | context_in.IsSatisfiedOn(st)
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels()) {
        context_in.SubstituteIsDefinedOnLemma(x, |st|);
        var v' := context_in.Substitute(x).Eval(st);
        assert x.Eval(context_in.AdjustState(st)) == v' by {
          context_in.AdjustStateSubstituteEvalLemma(st, x);
        }
        var st' := st.UpdateOrAdd(vNew, v');
        var stTransformed := context_in.AdjustState(st)[v := v'];

        assert stTransformed == context.AdjustState(st') by {
          context_in.AdjustStateSubstituteLemma(st, x);
        }

        assert context.IsSatisfiedOn(st') by {
          context_in.SubstituteIsDefinedOnLemma(x, vNew);
          context_in.Substitute(x).EvalDepthLemma(st, st');
          EvalEqLemma(BVar(vNew), context_in.Substitute(x), st');

          assert forall e <- context_in.ctx :: e.HoldsOn(st) ==> e.HoldsOn(st') by 
          {
            forall e: Expr | e in context_in.ctx && e.HoldsOn(st) ensures e.HoldsOn(st') {
              e.EvalDepthLemma(st, st');
            }
          }
        }
      }
    case Call(proc, args) => 
      var contextPre := context_in.mkPreContext(proc, args);
      VCs := seq(|proc.Pre|, (i: nat) requires i < |proc.Pre| => 
        SeqExprDepthLemma(proc.Pre, proc.Pre[i]);
        contextPre.MkEntailment(proc.Pre[i]));
      var vNew, context' := context_in.AddVarSet(args.OutArgs()) by {
        args.OutArgsDepthLemma();
      }
      var contextPost := context'.mkPostContext(proc, args, context_in);
      context := Context(contextPost.AddSeq(proc.Post).ctx, context'.incarnation);

      if (forall e <- VCs :: e.Holds()) {
        forall st: State | context_in.IsSatisfiedOn(st)
          ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels()) {
          var stAdj := context_in.AdjustState(st);
          var callSt := args.Eval(stAdj);
          assert args.IsDefinedOn(|stAdj|);
          forall e <- proc.Pre  
            ensures e.IsDefinedOn(|callSt|) 
            ensures e.HoldsOn(callSt) 
          {
            calc {
              e.HoldsOn(callSt);
              { context_in.mkPreContextLemma(proc, args, st); }
              e.HoldsOn(contextPre.AdjustState(st));
              { contextPre.MkEntailmentLemma(e, st); }
              contextPre.MkEntailment(e).Holds();
              { contextPre.MkEntailmentSeqLemma(proc.Pre, e);
                assert contextPre.MkEntailment(e) in VCs;
                assert forall e <- VCs :: e.Holds(); }
              true;
            }
          }
          forall st': State | 
            && st' in stAdj.EqExcept(args.OutArgs()) 
            && var callSt' := args.Eval(st') + args.EvalOld(stAdj);
               forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && e.HoldsOn(callSt')
            ensures st' in context.AdjustedModels() 
            {
              forall v <- args.OutArgs() 
                ensures v < |context_in.AdjustState(st)| {
                args.OutArgsDepthLemma();
              }
              var st'' := st.UpdateMapShift(vNew, map i: Idx | i in args.OutArgs() :: st'[i]);
              assert st' == context.AdjustState(st'') by {
                assert (map i: Idx | i in args.OutArgs() :: st'[i]).Keys == args.OutArgs();
              }
              var callSt' := args.Eval(st') + args.EvalOld(stAdj);
              assert context.IsSatisfiedOn(st'') by {
                assert forall i <- context.incarnation :: i < |st''|;
                forall e <- context.ctx
                  ensures e.IsDefinedOn(|st''|)
                  ensures e.HoldsOn(st'') {
                  if e in context_in.ctx {
                    e.EvalDepthLemma(st, st'');
                  } else {
                    assert e in contextPost.SeqSubstitute(proc.Post);
                    var e' := contextPost.GetSeqSubstituteLemma(proc.Post, e);
                    forall i <- contextPost.incarnation
                      ensures i < |st''| {
                      context'.mkPostContextIncrSubsetLemma(proc, args, context_in, i);
                    }
                    contextPost.SubstituteIsDefinedOnLemma(e', |st''|);
                    calc {
                      contextPost.Substitute(e').HoldsOn(st'');
                      { contextPost.AdjustStateSubstituteLemma(st'', e'); }
                      e'.HoldsOn(contextPost.AdjustState(st''));
                      { 
                        assert contextPost.AdjustState(st'') == callSt' by {
                          assert |contextPost.AdjustState(st'')| == |callSt'| == |args| + args.NumInOutArgs();
                          forall i | 0 <= i < |args| + args.NumInOutArgs() 
                            ensures (contextPost.AdjustState(st''))[i] == callSt'[i] {
                            if i < |args| {
                              calc {
                                (contextPost.AdjustState(st''))[i];
                                == { args.IsDefinedOnIn(args[i], |context'.incarnation|);
                                     assert context'.incarnation[args[i].v] in context'.incarnation; }
                                st''[context'.incarnation[args[i].v]];
                                ==
                                args.Eval(st')[i];
                                ==
                                callSt'[i];
                              }
                            } else {
                              calc {
                                (contextPost.AdjustState(st''))[i];
                              == { assert contextPost.incarnation[i] in contextPost.incarnation; }
                                st''[contextPost.incarnation[i]];
                              == { args.InOutArgsLemma(args.InOutArgs()[i - |args|]);
                                   args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i - |args|]), |context_in.incarnation|);
                                  assert contextPost.incarnation[i] == context_in.incarnation[args.InOutArgs()[i - |args|]]; }
                                st''[context_in.incarnation[args.InOutArgs()[i - |args|]]];
                              ==
                                args.EvalOld(context_in.AdjustState(st))[i - |args|];
                              ==
                                callSt'[i];
                              }
                            }
                          }
                        } 
                      }
                      true;
                    }
                  }
                }
              }
            }
        }
      }
  }

  ghost function BlockWPSeq(bcont: Block'.Continuation, post: iset<State>) : Omni.Continuation
    ensures |BlockWPSeq(bcont, post)| == |bcont| + 1
    // reads *
  {
    if bcont == [] then
      [post]
    else 
      var wpSeq := BlockWPSeq(bcont[1..], post); // [AllStates]
      var wpNew := Omni.SeqWP(bcont[0].cont, wpSeq); // Omni.SeqWP(Checks, [AllStates])
      var wpSeq := wpSeq.UpdateHead(wpNew); // [Omni.SeqWP(Checks, [AllStates])]
      wpSeq.UpdateAndAdd(bcont[0].varsInScope) 
  }

  lemma BlockWPSeqIdx(bcont: Block'.Continuation, l: nat)
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

  ghost predicate BlockSem(s: seq<Stmt>, bcont: Block'.Continuation, st: State, post: iset<State>) 
    // reads *
  {
    Omni.SeqSem(s, st, BlockWPSeq(bcont, post))
  }

  lemma BlockLastPost(bcont: Block'.Continuation, st: State)  
    requires |bcont| > 0
    requires bcont[|bcont| - 1] == Block'.Point([], 0) 
    ensures st in BlockWPSeq(bcont, AllStates)[|bcont|]
  {
    BlockWPSeqIdx(bcont, |bcont| - 1);
  }

  lemma IsDefinedLoop(inv: Expr, body: Stmt, n: nat, k: nat)
    requires Loop(inv, body).IsDefinedOn(n)
    requires Loop(inv, body).JumpsDefinedOn(k)
    ensures SeqIsDefinedOn([Assume(inv), body, Check(inv), Assume(BConst(false))], n)
    ensures SeqJumpsDefinedOn([Assume(inv), body, Check(inv), Assume(BConst(false))], k)
  {
    assert [Assume(inv), body, Check(inv), Assume(BConst(false))][0] == Assume(inv);
    assert [Assume(inv), body, Check(inv), Assume(BConst(false))][1..] == [body, Check(inv), Assume(BConst(false))];
    assert [body, Check(inv), Assume(BConst(false))][0] == body;
    assert [body, Check(inv), Assume(BConst(false))][1..] == [Check(inv), Assume(BConst(false))];
    assert [Check(inv), Assume(BConst(false))][0] == Check(inv);
    assert [Check(inv), Assume(BConst(false))][1..] == [Assume(BConst(false))];
    assert [Assume(BConst(false))][0] == Assume(BConst(false));
    assert [Assume(BConst(false))][1..] == [];
  }

  method SeqVCGen(s: seq<Stmt>, context: Context, bcont: Block'.Continuation) returns (VCs: seq<Expr>) 
    requires bcont.IsDefinedOn(|context.incarnation|)

    requires SeqIsDefinedOn(s, |context.incarnation|)
    requires SeqJumpsDefinedOn(s, |bcont|)

    requires bcont.VarsDefined(|context.incarnation|)
    requires bcont.JumpsDefined()

    decreases SeqSize(s) + bcont.Size()

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
        VCcont := SeqVCGen(cont, context', bcont) by {
          bcont.VarsDefinedTransitivity(|context.incarnation|, |context'.incarnation|);
        }
        VCs := VCstmt + VCcont;
        if (forall e <- VCs :: e.Holds()) {
          forall st: State | context.IsSatisfiedOn(st) 
            ensures BlockSem(s, bcont, context.AdjustState(st), AllStates) { }
        }
      } else {
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
              ensures BlockSem(s, bcont, context.AdjustState(st), AllStates) { }
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
                    forall e: Expr | e in context.ctx && e.HoldsOn(st) {
                      e.EvalDepthLemma(st, st');
                    }
                  }
                  calc {
                    Omni.SeqSem([body], context'.AdjustState(st'), updWP);
                    { assert context.AdjustState(st).Update(vs) == context'.AdjustState(st'); }
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
            assert bcont'[l..].JumpsDefined() && bcont'[l..].VarsDefined(|context'.incarnation|) by {
              if l != 0 {
                assert bcont'[l..] == bcont[l - 1..];
                assert |context'.incarnation| == |context.incarnation| - varsToDelete;
                bcont.VarsInScopeSuffix(l - 1);
                assert varsToDelete == bcont[..l - 1].AllVarsInScope();
                bcont.DefinedPrefix(l - 1, |context.incarnation|);
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
        case Loop(inv, body) =>
          var VCInvIni := context.MkEntailment(inv);
          var assnvars := AssignmentTarget'.Process(body);

          var vNew, context' := context.AddVarSet(assnvars);

          var VCInvLoop := SeqVCGen([Assume(inv), body, Check(inv), Assume(BConst(false))], context', bcont) by {
            // decreases
            calc {
              SeqSize([Assume(inv), body, Check(inv), Assume(BConst(false))]);
            == 
              1 + SeqSize([body, Check(inv), Assume(BConst(false))]);
            ==
              1 + body.Size() + SeqSize([Check(inv), Assume(BConst(false))]);
            == 
              1 + body.Size() + 1 + SeqSize([Assume(BConst(false))]);
            == 
              1 + body.Size() + 1 + 1 + SeqSize([]);
            }
            // IsDefinedOn
            IsDefinedLoop(inv, body, |context'.incarnation|, |bcont|);
          }
          VCs := [VCInvIni] + VCInvLoop;
          if (forall e <- VCs :: e.Holds()) {
            forall st: State | context.IsSatisfiedOn(st)
              ensures Omni.SeqSem([Loop(inv, body)] + cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates)) {
              var inv' := inv.Sem() * context.AdjustState(st).EqExcept(assnvars);
              var st' := context.AdjustState(st);
              Omni.SemLoopWithCont(inv, body, cont, st', BlockWPSeq(bcont, AllStates), inv') by {
                assert st' in inv.Sem() by {
                  context.MkEntailmentLemma(inv, st);
                }

                forall st': State | st' in inv' 
                  ensures Omni.Sem(body, st', BlockWPSeq(bcont, AllStates).UpdateHead(inv')) {
                  var st'' := st.UpdateMapShift(vNew, map i: Idx | i in assnvars :: st'[i]);
                  assert st' == context'.AdjustState(st'') by {
                    assert (map i: Idx | i in assnvars :: st'[i]).Keys == assnvars;
                  }
                  assert context'.IsSatisfiedOn(st'') by {
                    forall e <- context'.ctx 
                      ensures e.HoldsOn(st'') {
                      e.EvalDepthLemma(st, st'');
                    }
                  }
                  calc {
                    Omni.Sem(body, st', BlockWPSeq(bcont, AllStates).UpdateHead(inv'));
                    { AssignmentTarget'.Correct(body, st', context.AdjustState(st), assnvars, BlockWPSeq(bcont, AllStates), inv.Sem()); }
                    Omni.Sem(body, st', BlockWPSeq(bcont, AllStates).UpdateHead(inv.Sem()));
                    { Omni.InvSem(inv, body, st', BlockWPSeq(bcont, AllStates), Assume(BConst(false))); }
                    Omni.SeqSem([Assume(inv), body, Check(inv), Assume(BConst(false))], st', BlockWPSeq(bcont, AllStates));
                    true;
                  }
                }
              }
            }
          }
      }
    }
  }

  method VCGenProc(proc: Procedure) returns (VCs: seq<Expr>) 
    requires proc.Valid()
    // requires proc.IsSafe()
    ensures (forall e <- VCs :: e.Holds()) ==> Omni.ProcedureIsSound(proc)
  {
    var context := mkInitialContext(proc);
    var bcont: Block'.Continuation := [Block'.Point(proc.PostCheck(), 0)];
    if proc.Body.Some? {
      VCs := SeqVCGen([proc.Body.value], context, bcont);
      if (forall e <- VCs :: e.Holds()) {
        forall st: State | st in proc.PreSet()
          ensures Omni.Sem(proc.Body.value, st, [proc.PostSet()]) {
          assert context.IsSatisfiedOn(st) by {
            forall i <- context.incarnation {
              mkInitialContextLemma(proc,i);
            }
          }
          assert Omni.Sem(proc.Body.value, context.AdjustState(st), BlockWPSeq(bcont, AllStates)) by {
            Omni.SeqSemSingle(proc.Body.value, context.AdjustState(st), BlockWPSeq(bcont, AllStates));
          }
          var wpSeq: Omni.Continuation := [Omni.SeqWP(proc.PostCheck(), [AllStates]), Omni.SeqWP(proc.PostCheck(), [AllStates])];
          assert BlockWPSeq(bcont, AllStates) == wpSeq by {
            wpSeq.Update0();
          }
          Omni.SemConsDepthLemma(proc.Body.value, context.AdjustState(st), wpSeq, [proc.PostSet()], 0) by {
            forall st: State | Omni.SeqSem(proc.PostCheck(), st, [AllStates])
              ensures st in proc.PostSet() {
              Omni.SemPostCheckLemma(proc, st, [AllStates]);
            }
          }
          assert context.AdjustState(st) == st;
        }
      }
    } else {
      VCs := [];
    }
  }

  function SetOfSeq<T>(s: seq<T>): set<T> {
    set x | x in s
  }

  method VCGenProcs(procs: seq<Procedure>) returns (VCs: seq<Expr>)
    requires forall proc <- procs :: proc.Valid()
    // requires forall proc <- procs :: proc.IsSafe()
    requires forall proc <- procs :: proc.ProceduresCalled() <= SetOfSeq(procs)
    ensures (forall e <- VCs :: e.Holds()) ==> 
      forall proc <- procs :: Omni.RefProcedureIsSound(proc)
  {
    VCs := [];
    var VCs';
    for i := 0 to |procs| 
      invariant (forall e <- VCs :: e.Holds()) ==> forall proc <- procs[..i] :: Omni.ProcedureIsSound(proc)
    {
      VCs' := VCGenProc(procs[i]) by {
        assert procs[i] in procs;
      }
      VCs := VCs + VCs';
    }
    if (forall e <- VCs :: e.Holds()) {
      Omni.SemSoundProcs(SetOfSeq(procs));
    }
  }
}