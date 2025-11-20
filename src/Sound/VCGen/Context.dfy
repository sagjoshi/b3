module Context {
  import opened Utils
  import M = Model
  import opened AST
  import opened State
  import opened Expr

  datatype Context = Context(
    ctx: seq<Expr>,
    incarnation: map<Variable, Variable>) 
  {
    // ghost function Models(md: M.Model) : iset<State> { iset st: State | IsSatisfiedOn(st, md) }

    // ghost function AdjustedModels(md: M.Model) : iset<State> { 
    //   iset st: State | exists st' <- Models(md) {:InAdjustedModelsLemma(st', md)} :: AdjustState(st') == st
    // }

//     lemma InAdjustedModelsLemma(st: State, st': State, md: M.Model)
//       requires IsSatisfiedOn(st', md)
//       requires st == AdjustState(st')
//       ensures st in AdjustedModels(md)
//     {

//     }

    function FVars(): set<Variable> 
    {
      SeqExprFVars(ctx) + incarnation.Values
    }

    function FreshVar(typ: Type): Variable
      ensures FreshVar(typ) !in incarnation
      ensures FreshVar(typ) !in SeqExprFVars(ctx)
      ensures forall c <- ctx :: FreshVar(typ) !in c.FVars()
      ensures FreshVar(typ).typ == typ
    // TODO: implemet

    function AdjustState(s: State): State
      requires incarnation.Values <= s.Keys
    {
      map v | v in incarnation.Keys :: s[incarnation[v]]
    }

    function AdjustStateBVars(s: State, bVars: set<Variable>): State
      requires incarnation.Values <= s.Keys + bVars
    {
      map v | v in incarnation.Keys && incarnation[v] !in bVars :: 
        s[incarnation[v]]
    }

    function DeleteVar(vars: set<Variable>): Context
    {
      Context(ctx, incarnation - vars)
    }

    lemma DeleteVarUnion(vars1: set<Variable>, vars2: set<Variable>)
      ensures DeleteVar(vars1 + vars2) == DeleteVar(vars1).DeleteVar(vars2)
    {
    }

    lemma DeleteEmpty()
      ensures DeleteVar({}) == this
    {

    }

    function SubstituteBVars(e: Expr, bVars: set<Variable>): Expr
      requires e.IsDefinedOn(incarnation.Keys + bVars)
      requires incarnation.Keys !! bVars
      decreases e
    {
      match e
      case BConst(bvalue) => e
      case IConst(ivalue) => e
      case CustomConst(value) => e
      case BVar(v) => if v in bVars then BVar(v) else BVar(incarnation[v])
      case OperatorExpr(op, args) => OperatorExpr(op, SeqSubstituteBVars(args, bVars))
      case FunctionCallExpr(func, args) => FunctionCallExpr(func, SeqSubstituteBVars(args, bVars))
      case LetExpr(v, rhs, body) => 
        assert body.FVars() <= e.FVars() + {v};
        LetExpr(v, SubstituteBVars(rhs, bVars), DeleteVar({v}).SubstituteBVars(body, bVars + {v}))
      case QuantifierExpr(univ, v, body) => 
        assert body.FVars() <= e.FVars() + {v};
        QuantifierExpr(univ, v, DeleteVar({v}).SubstituteBVars(body, bVars + {v}))
    }

    function SeqSubstituteBVars(ss: seq<Expr>, bVars: set<Variable>): seq<Expr>
      requires SeqExprFVars(ss) <= incarnation.Keys + bVars
      requires incarnation.Keys !! bVars
      decreases ss
    {
      if ss == [] then [] else
      [SubstituteBVars(ss[0], bVars)] + SeqSubstituteBVars(ss[1..], bVars)
    }

    function Substitute(e: Expr): Expr
      requires e.IsDefinedOn(incarnation.Keys)
    {
      SubstituteBVars(e, {})
    }

    function MkEntailment(e: Expr): Expr
      requires e.IsDefinedOn(incarnation.Keys)
    {
      Implies(Conj(ctx), Substitute(e))
    }

    function MkEntailmentSeq(ss: seq<Expr>): seq<Expr>
      requires forall e <- ss :: e.IsDefinedOn(incarnation.Keys)
    {
      seq(|ss|, (i: nat) requires i < |ss| => MkEntailment(ss[i]))
    }

    lemma MkEntailmentSeqLemma(ss: seq<Expr>, e: Expr)
      requires forall e <- ss :: e.IsDefinedOn(incarnation.Keys)
      requires e in ss
      ensures MkEntailment(e) in MkEntailmentSeq(ss)
    {
      assert MkEntailment(e) == MkEntailmentSeq(ss)[Index(ss, e)];
    }

    ghost predicate IsDefinedOn(d: set<Variable>)
    {
      forall e <- ctx :: e.IsDefinedOn(d)
    }

    /*

    x -> y 

    x && forall y, y

    y -> 0
    */
    ghost predicate IsSatisfiedOn(s: State, md: M.Model) 
    {
      && IsDefinedOn(s.Keys)
      && incarnation.Values <= s.Keys
      && (forall e <- ctx :: e.HoldsOn(s, md))
    }

    lemma SubstituteBVarsIsDefinedOnLemma(e: Expr, bVars: set<Variable>, d: set<Variable>)
      requires e.IsDefinedOn(incarnation.Keys + bVars)
      requires incarnation.Values <= d
      requires bVars <= d
      requires incarnation.Keys !! bVars
      ensures SubstituteBVars(e, bVars).FVars() <= d
      decreases e
    {
      match e 
      case BVar(v) => if v !in bVars { 
          assert v in incarnation.Keys;
          assert incarnation[v] in incarnation.Values; 
        }
      case OperatorExpr(op, args) => 
        SeqSubstituteBVarsIsDefinedOnLemma(args, bVars, d);
      case QuantifierExpr(univ, v, body) =>
        calc {        
          SubstituteBVars(e, bVars).FVars();
          == { assert body.FVars() <= e.FVars() + {v}; }
          DeleteVar({v}).SubstituteBVars(body, bVars + {v}).FVars() - {v};
          <= { DeleteVar({v}).SubstituteBVarsIsDefinedOnLemma(body, bVars + {v}, d + {v}); }
          d;
        }
      case FunctionCallExpr(func, args) =>
        SeqSubstituteBVarsIsDefinedOnLemma(args, bVars, d);
      case LetExpr(v, rhs, body) =>
        calc {        
          SubstituteBVars(e, bVars).FVars();
          == { assert body.FVars() <= e.FVars() + {v}; }
          SubstituteBVars(rhs, bVars).FVars() + 
          (DeleteVar({v}).SubstituteBVars(body, bVars + {v}).FVars() - {v});
          <= { DeleteVar({v}).SubstituteBVarsIsDefinedOnLemma(body, bVars + {v}, d + {v}); }
          d;
        }
      case _ =>
    }

    lemma SeqSubstituteBVarsIsDefinedOnLemma(ss: seq<Expr>, bVars: set<Variable>, d: set<Variable>)
      requires SeqExprFVars(ss) <= incarnation.Keys + bVars
      requires incarnation.Values <= d
      requires incarnation.Keys !! bVars
      requires bVars <= d
      ensures forall e <- SeqSubstituteBVars(ss, bVars) :: e.IsDefinedOn(d)
      ensures SeqExprFVars(SeqSubstituteBVars(ss, bVars)) <= d
      decreases ss
    {
      if ss != [] {
        SubstituteBVarsIsDefinedOnLemma(ss[0], bVars, d);
        SeqSubstituteBVarsIsDefinedOnLemma(ss[1..], bVars, d);
      }
    }

    lemma SubstituteIsDefinedOnLemma(e: Expr, d: set<Variable>)
      requires e.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= d
      ensures Substitute(e).FVars() <= d
    {
      DeleteEmpty();
      SubstituteBVarsIsDefinedOnLemma(e, {}, d);
    }

    lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr, v: Variable, md: M.Model)
      requires e1.IsDefinedOn(s1.Keys + {v})
      requires e2.IsDefinedOn(s2.Keys + {v})
      requires forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.Eval(s1.UpdateAt(v, b), md) == e2.Eval(s2.UpdateAt(v, b), md)
      ensures (forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.HoldsOn(s1.UpdateAt(v, b), md)) == (forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e2.HoldsOn(s2.UpdateAt(v, b), md))
    {  }

    lemma ExistsPush(s1: State, s2: State, e1: Expr, e2: Expr, v: Variable, md: M.Model)
      requires e1.IsDefinedOn(s1.Keys + {v})
      requires e2.IsDefinedOn(s2.Keys + {v})
      requires forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.HoldsOn(s1.UpdateAt(v, b), md) == e2.HoldsOn(s2.UpdateAt(v, b), md)
      ensures (exists b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.HoldsOn(s1.UpdateAt(v, b), md)) == (exists b: M.Any | md.HasType(b, v.typ.ToType()) :: e2.HoldsOn(s2.UpdateAt(v, b), md))
    {  }

    lemma SeqAdjustStateSubstituteBVarsLemma(ss: seq<Expr>, s: State, bVars: set<Variable>, md: M.Model)
      requires SeqExprFVars(ss) <= incarnation.Keys + bVars
      requires incarnation.Values <= s.Keys
      requires bVars <= s.Keys
      requires incarnation.Keys !! bVars
      ensures
        (SeqSubstituteBVarsIsDefinedOnLemma(ss, bVars, s.Keys);
         SeqEval(ss, s.Restrict(bVars) + AdjustStateBVars(s, bVars), md) == 
         SeqEval(SeqSubstituteBVars(ss, bVars), s, md))
      decreases ss
    {
      if ss != [] {
        SeqAdjustStateSubstituteBVarsLemma(ss[1..], s, bVars, md);
        SeqSubstituteBVarsIsDefinedOnLemma(ss, bVars, s.Keys);
        AdjustStateSubstituteBVarsLemma(s, ss[0], bVars, md);
      }
    }


    lemma AdjustStateSubstituteBVarsLemma(s: State, e: Expr, bVars: set<Variable>, md: M.Model)
      requires e.IsDefinedOn(incarnation.Keys + bVars)
      requires incarnation.Values <= s.Keys + bVars
      requires incarnation.Keys !! bVars
      requires bVars <= s.Keys
      ensures (SubstituteBVarsIsDefinedOnLemma(e, bVars, s.Keys);
        e.Eval(s.Restrict(bVars) + AdjustStateBVars(s, bVars), md)) == SubstituteBVars(e, bVars).Eval(s, md)
      decreases e
    {
      match e
      case OperatorExpr(op, args) =>
        SeqAdjustStateSubstituteBVarsLemma(args, s, bVars, md);
      case FunctionCallExpr(func, args) =>
        SeqAdjustStateSubstituteBVarsLemma(args, s, bVars, md);
      case QuantifierExpr(univ, v, body) =>
        assert body.FVars() <= e.FVars() + {v};
        assert (incarnation - {v}).Values <= incarnation.Values;
        DeleteVar({v}).SubstituteBVarsIsDefinedOnLemma(body, bVars + {v}, s.Keys + {v});
        assert forall b: M.Any | md.HasType(b, v.typ.ToType()) ::
          body.Eval((s.Restrict(bVars) + AdjustStateBVars(s, bVars)).UpdateAt(v, b), md) ==
          DeleteVar({v}).SubstituteBVars(body, bVars + {v}).Eval(s.UpdateAt(v, b), md) by {
          forall b: M.Any | md.HasType(b, v.typ.ToType()) 
            ensures 
              body.Eval((s.Restrict(bVars) + AdjustStateBVars(s, bVars)).UpdateAt(v, b), md) == 
              DeleteVar({v}).SubstituteBVars(body, bVars + {v}).Eval(s.UpdateAt(v, b), md)
            {
              calc {
                DeleteVar({v}).SubstituteBVars(body, bVars + {v}).Eval(s.UpdateAt(v, b), md);
                == { DeleteVar({v}).AdjustStateSubstituteBVarsLemma(s.UpdateAt(v, b), body, bVars + {v}, md); }
                body.Eval(s.UpdateAt(v, b).Restrict(bVars + {v}) + DeleteVar({v}).AdjustStateBVars(s.UpdateAt(v, b), bVars + {v}), md);
                == { assert s.UpdateAt(v, b).Restrict(bVars + {v}) == s.Restrict(bVars).UpdateAt(v, b); }
                body.Eval(s.Restrict(bVars).UpdateAt(v, b) + DeleteVar({v}).AdjustStateBVars(s.UpdateAt(v, b), bVars + {v}), md);
                == { 
                    assert DeleteVar({v}).AdjustState(s.UpdateAt(v, b)) == DeleteVar({v}).AdjustState(s);
                    assume false;
                 }
                body.Eval((s.Restrict(bVars) + AdjustStateBVars(s, bVars)).UpdateAt(v, b), md);
              }
            }
          ForallPush(s.Restrict(bVars) + AdjustStateBVars(s, bVars), s, body, DeleteVar({v}).SubstituteBVars(body, bVars + {v}), v, md);
        }
      case QuantifierExpr(false, v, body) => assume false;
        // SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        // assert forall b: M.Any | md.HasType(b, tp.ToType()) :: 
        //   body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md) == 
        //   SubstituteIdx(body, i + 1).Eval(s.Update([b]), md) by {
        //   forall b: M.Any | md.HasType(b, tp.ToType()) 
        //     ensures body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md) == SubstituteIdx(body, i + 1).Eval(s.Update([b]), md) {
        //     assert ([b] + s)[..i+1] == [b] + s[..i];
        //     assert ([b] + s)[i+1..] == s[i..];
        //     assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]));
        //     AdjustStateSubstituteIdxLemma([b] + s, body, i + 1, md);
        //   }
        // }
        // ExistsPush(s[..i] + AdjustState(s[i..]), s, body, SubstituteIdx(body, i + 1), tp.ToType(), md);
      case BVar(v) => if v in incarnation.Keys { assert incarnation[v] in incarnation.Values; }
      case LetExpr(v, rhs, body) => assume false;
        // var b := SubstituteIdx(rhs, i).Eval(s, md) by {
        //   SubstituteIdxIsDefinedOnLemma(rhs, i, |s|);
        // }
        // if b.Some? {
        //   var b := b.value;
        //   calc {
        //     LetExpr(v, rhs, body).Eval(s[..i] + AdjustState(s[i..]), md);
        //     ==
        //     body.Eval((s[..i] + AdjustState(s[i..])).Update([rhs.Eval(s[..i] + AdjustState(s[i..]), md).value]), md);
        //     == { SubstituteIdxIsDefinedOnLemma(rhs, i, |s|); }
        //     body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md);
        //     == { assert ([b] + s)[..i+1] == [b] + s[..i];
        //         assert ([b] + s)[i+1..] == s[i..];
        //         assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..])); }
        //     body.Eval(([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]), md);
        //     == { AdjustStateSubstituteIdxLemma([b] + s, body, i + 1, md);
        //         SubstituteIdxIsDefinedOnLemma(body, i + 1, |s| + 1); }
        //     SubstituteIdx(body, i + 1).Eval(s.Update([b]), md);
        //   }
        // }
      case _  => 
    }

//     lemma AdjustStateSubstituteEvalLemma(s: State, e: Expr, md: M.Model)
//       requires e.IsDefinedOn(|incarnation|)
//       requires forall ic <- incarnation :: ic < |s|
//       ensures Substitute(e).IsDefinedOn(|s|)
//       ensures e.Eval(AdjustState(s), md) == Substitute(e).Eval(s, md)
//     {
//       SubstituteIsDefinedOnLemma(e, |s|);
//       AdjustStateSubstituteIdxLemma(s, e, 0, md);
//       assert [] + AdjustState(s) == AdjustState(s);
//     }

//     lemma AdjustStateSubstituteLemma(s: State, e: Expr, md: M.Model)
//       requires e.IsDefinedOn(|incarnation|)
//       requires forall ic <- incarnation :: ic < |s|
//       ensures Substitute(e).IsDefinedOn(|s|)
//       ensures e.HoldsOn(AdjustState(s), md) == Substitute(e).HoldsOn(s, md)
//     {
//       SubstituteIsDefinedOnLemma(e, |s|);
//       AdjustStateSubstituteIdxLemma(s, e, 0, md);
//       assert [] + AdjustState(s) == AdjustState(s);
//     }
//   }

    // lemma MkEntailmentLemma(e: Expr, st: State, md: M.Model)
    //   requires e.IsDefinedOn(incarnation.Keys)
    //   requires forall ic <- incarnation.Values :: ic in st.Keys
    //   requires IsSatisfiedOn(st, md)
    //   requires MkEntailment(e).Holds(md)
    //   ensures e.HoldsOn(AdjustState(st), md)
    // {
    //   assert Implies(Conj(ctx), Substitute(e)).IsDefinedOn(|st|) by {
    //     IsDefinedOnImpliesLemma(Conj(ctx), Substitute(e), st) by {
    //       EvalConjLemma(ctx, st, md);
    //       SubstituteIsDefinedOnLemma(e, st.Keys);
    //     }
    //   }
    //   assert e.HoldsOn(AdjustState(st), md) by { 
    //     calc {
    //       e.HoldsOn(AdjustState(st), md);
    //       { SubstituteIsDefinedOnLemma(e, st.Keys);
    //         AdjustStateSubstituteLemma(st, e, md); }
    //       Substitute(e).HoldsOn(st, md);
    //       { EvalConjLemma(ctx, st, md);
    //         AdjustStateSubstituteLemma(st, e, md);
    //         HoldsOnImpliesLemma(Conj(ctx), Substitute(e), st, md); }
    //       MkEntailment(e).Holds(md);
    //     }
    //   }
    // }

//     function Add(e: Expr): Context
//       requires e.IsDefinedOn(|incarnation|)
//     {
//       this.(ctx := ctx + [Substitute(e)])
//     }

//     function SeqSubstitute(ss: seq<Expr>): seq<Expr>
//       requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
//     {
//       seq(|ss|, (i: nat) requires i < |ss| => Substitute(ss[i]))
//     }

//     lemma GetSeqSubstituteLemma(ss: seq<Expr>, e: Expr) returns (e': Expr) 
//       requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
//       requires e in SeqSubstitute(ss)
//       ensures e' in ss
//       ensures Substitute(e') == e
//     {
//       e' := ss[Index(SeqSubstitute(ss), e)];
//     }

//     function AddSeq(ss: seq<Expr>): Context
//       requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
//     {
//       this.(ctx := ctx + SeqSubstitute(ss))
//     }

//     function mkPreContext(proc: Procedure, args: CallArguments): Context
//       requires Call(proc, args).ValidCalls()
//       requires args.IsDefinedOn(|incarnation|)
//       ensures |mkPreContext(proc, args).incarnation| == |args|
//       ensures forall i <- mkPreContext(proc, args).incarnation :: i in incarnation
//     {
//       var incrPre := seq(|args|, (i: nat) requires i < |args| => 
//         args.IsDefinedOnIn(args[i], |incarnation|);
//         incarnation[args[i].v]);
//       forall i <- incrPre 
//         ensures i in incarnation
//       {
//         assert i == incrPre[Index(incrPre, i)];
//         assert args[Index(incrPre, i)] in args;
//         args.IsDefinedOnIn(args[Index(incrPre, i)], |incarnation|);
//         assert i == incarnation[args[Index(incrPre, i)].v];
//       }
//       Context(ctx, incrPre)
//     }

//     lemma mkPreContextLemma(proc: Procedure, args: CallArguments, s: State)
//       requires Call(proc, args).ValidCalls()
//       requires args.IsDefinedOn(|incarnation|)
//       requires forall i <- incarnation :: i < |s|
//       ensures mkPreContext(proc, args).AdjustState(s) == args.Eval(AdjustState(s))
//     {
//       forall i | 0 <= i < |args|
//         ensures (mkPreContext(proc, args).AdjustState(s))[i] == args.Eval(AdjustState(s))[i]
//       {
//         calc {
//           (mkPreContext(proc, args).AdjustState(s))[i];
//           == { args.IsDefinedOnIn(args[i], |incarnation|); 
//                assert incarnation[args[i].v] in incarnation; }
//           s[incarnation[args[i].v]];
//           ==
//           args.Eval(AdjustState(s))[i];
//         }
//       }
//     }

//     function mkPostContext(proc: Procedure, args: CallArguments, oldContext: Context): Context
//       requires Call(proc, args).ValidCalls()
//       requires args.IsDefinedOn(|incarnation|)
//       requires args.IsDefinedOn(|oldContext.incarnation|)
//       requires |oldContext.incarnation| >= args.NumInOutArgs()
//       ensures |mkPostContext(proc, args, oldContext).incarnation| == |args| + args.NumInOutArgs()
//     {
//       var oldNum := args.NumInOutArgs();
//       var incrPost: seq<Idx> := seq(|args|, (i: nat) requires i < |args| => 
//         args.IsDefinedOnIn(args[i], |incarnation|);
//         incarnation[args[i].v]); 
//       var incrPostOld: seq<Idx> := seq(args.NumInOutArgs(), (i: nat) requires i < args.NumInOutArgs() => 
//         args.InOutArgsLemma(args.InOutArgs()[i]); 
//         args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i]), |oldContext.incarnation|);
//         oldContext.incarnation[args.InOutArgs()[i]]);
//       Context(ctx, incrPost + incrPostOld)
//     }

//     lemma mkPostContextIncrSubsetLemma(proc: Procedure, args: CallArguments, oldContext: Context, i: nat)
//       requires Call(proc, args).ValidCalls()
//       requires args.IsDefinedOn(|incarnation|)
//       requires args.IsDefinedOn(|oldContext.incarnation|)
//       requires |oldContext.incarnation| >= args.NumInOutArgs()
//       requires i in mkPostContext(proc, args, oldContext).incarnation
//       ensures i in oldContext.incarnation || i in incarnation
//     {
//       var oldNum := args.NumInOutArgs();
//       var incrPost: seq<Idx> := seq(|args|, (i: nat) requires i < |args| => 
//         args.IsDefinedOnIn(args[i], |incarnation|);
//         incarnation[args[i].v]); 
//       var incrPostOld: seq<Idx> := seq(args.NumInOutArgs(), (i: nat) requires i < args.NumInOutArgs() => 
//         args.InOutArgsLemma(args.InOutArgs()[i]); 
//         args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i]), |oldContext.incarnation|);
//         oldContext.incarnation[args.InOutArgs()[i]]);
//       assert incrPost + incrPostOld == mkPostContext(proc, args, oldContext).incarnation;
//       assert i in incrPost + incrPostOld;
//       if i in incrPost {
//         assert i == incrPost[Index(incrPost, i)];
//         args.IsDefinedOnIn(args[Index(incrPost, i)], |incarnation|);
//         assert i == incarnation[args[Index(incrPost, i)].v];
//       } else {
//         assert i in incrPostOld;
//         assert i == incrPostOld[Index(incrPostOld, i)];
//         args.InOutArgsLemma(args.InOutArgs()[Index(incrPostOld, i)]);
//         args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[Index(incrPostOld, i)]), |oldContext.incarnation|);
//         assert i == oldContext.incarnation[args.InOutArgs()[Index(incrPostOld, i)]];
//       }
//     }

//     method AddEq(v: Idx, e: Expr) returns (ghost vNew: Idx, context: Context)
//       requires v < |incarnation|
//       requires e.IsDefinedOn(|incarnation|)
//       ensures |incarnation| == |context.incarnation|
//       ensures ctx + [Eq(BVar(vNew), Substitute(e))] == context.ctx
//       ensures incarnation[v := vNew] == context.incarnation
//       ensures forall i <- incarnation :: i < vNew 
//       ensures forall c <- ctx :: c.Depth() < vNew
//       ensures SeqMax(incarnation) < vNew
//       ensures SeqExprDepth(ctx) < vNew
//       // ensures 
//     {
//       var v' := FreshIdx();
//       var ctx' := ctx + [Eq(BVar(v'), Substitute(e))];
//       var incarnation' := incarnation[v := v'];
//       context := Context(ctx', incarnation');
//       vNew := v';
//     }

//     method AddVarSet(vars: set<Idx>) returns (ghost vNew: Idx, context: Context)
//       requires forall v <- vars :: v < |incarnation|
//       ensures context.ctx         == ctx
//       ensures |context.incarnation| == |incarnation|
//       ensures forall i: nat :: i in vars ==> context.incarnation[i] == vNew + i
//       ensures vNew > SeqMax(incarnation)
//       ensures forall c <- ctx :: c.Depth() < vNew
//       ensures SeqExprDepth(ctx) < vNew
//       ensures forall i: nat :: i !in vars && i < |incarnation| ==> context.incarnation[i] == incarnation[i]
//       ensures forall i <- context.incarnation :: i <= vNew + Max'(vars)
//     {
//       var vars' := vars; 
//       var incr' := incarnation;
//       var v' := FreshIdx();
//       vNew := v';
//       while vars' != {}
//         invariant |incr'| == |incarnation|
//         invariant vars' <= vars
//         invariant forall i: nat :: i in vars - vars' ==> incr'[i] == vNew + i
//         invariant forall i: nat :: i !in vars - vars' && i < |incarnation| ==> incr'[i] == incarnation[i]
//         invariant forall i: nat :: i < |incarnation| ==> incr'[i] <= vNew + Max'(vars)
//       {
//         var v :| v in vars';
//         vars' := vars' - {v};
//         incr' := incr'[v := v' + v];
//       }
//       context := Context(ctx, incr');
//     }

//     function Delete(n: nat): Context
//       requires n <= |incarnation|
//     {
//       Context(ctx, incarnation[n..])
//     }
      

//     method AddVars(n: nat) returns (ghost vNew: Idx, context: Context)
//       // ensures incarnation <= AddVars(n).incarnation 
//       ensures context.ctx         == ctx
//       ensures |context.incarnation| == |incarnation| + n
//       ensures forall i: nat :: i < n ==> context.incarnation[i] == vNew + i
//       ensures forall i: nat :: n <= i < |incarnation| + n ==> context.incarnation[i] == incarnation[i - n]
//       ensures forall c <- ctx :: c.Depth() < vNew
//       ensures SeqMax(incarnation) < vNew
//       ensures SeqExprDepth(ctx) < vNew
//     {
//       var v := FreshIdx();
//       var addOn := seq(n, (i: nat) => v + i);
//       context := Context(ctx, addOn + incarnation);
//       vNew := v;
//     }

//     // lemma SubstituteIdxIsDefinedOnLemmaOperator

//   function mkInitialContext(proc: Procedure): Context
//   {
//     var incr := seq(|proc.Parameters|, (i: nat) => i);
//     var incrOld := seq(proc.NumInOutArgs(), (i: nat) requires i < proc.NumInOutArgs() => 
//       proc.InOutVarsIdxs()[i]);
//     Context(proc.Pre, incr + incrOld)
//   }

//   lemma mkInitialContextLemma(proc: Procedure, i: nat)
//     requires i in mkInitialContext(proc).incarnation
//     ensures i < |proc.Parameters| + proc.NumInOutArgs()
//   {
//     var incr := seq(|proc.Parameters|, (i: nat) => i);
//     var incrOld := seq(proc.NumInOutArgs(), (i: nat) requires i < proc.NumInOutArgs() => 
//       proc.InOutVarsIdxs()[i]);
//     if i in incrOld {
//       assert i == proc.InOutVarsIdxs()[Index(incrOld, i)];
//       proc.InOutVarsIdxsLemma(proc.Parameters, 0, Index(incrOld, i));
//     }
  }
}