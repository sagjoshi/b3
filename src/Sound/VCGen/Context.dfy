module Context {
  import opened Utils
  import M = Model
  import opened AST
  import opened State
  import opened Expr

  datatype Context = Context(
    ctx: seq<Expr>,
    incarnation: seq<nat>) 
  {
    ghost function Models(md: M.Model) : iset<State> { iset st: State | IsSatisfiedOn(st, md) }

    ghost function AdjustedModels(md: M.Model) : iset<State> { 
      iset st: State | exists st' <- Models(md) {:InAdjustedModelsLemma(st', md)} :: AdjustState(st') == st
    }

    lemma InAdjustedModelsLemma(st: State, st': State, md: M.Model)
      requires IsSatisfiedOn(st', md)
      requires st == AdjustState(st')
      ensures st in AdjustedModels(md)
    {

    }

    function Depth(): Idx 
    {
      max(SeqExprDepth(ctx), SeqMax(incarnation))
    }

    function FreshIdx(): Idx
      ensures forall i <- incarnation :: i < FreshIdx()
      ensures SeqExprDepth(ctx) < FreshIdx()
      ensures forall c <- ctx :: c.Depth() < FreshIdx()
    {
      max(SeqMax(incarnation), SeqExprDepth(ctx)) + 1
    }

    

    function AdjustState(s: State): State
      requires forall i <- incarnation :: i < |s|
    { 
      seq(|incarnation|, (i: nat) requires i < |incarnation| => 
        assert incarnation[i] in incarnation;
        s[incarnation[i]])
    }

    function SubstituteIdx(e: Expr, i: Idx): Expr
      requires e.IsDefinedOn(|incarnation| + i)
    {
      match e
      case BConst(bvalue) => e
      case IConst(ivalue) => e
      case CustomConst(value) => e
      case BVar(v) =>
        if v >= i then  
          BVar(incarnation[v - i] + i) 
        else e
      case OperatorExpr(op, args) =>
        OperatorExpr(op, SeqSubstituteIdx(args, i))
      case FunctionCallExpr(func, args) =>
        FunctionCallExpr(func, SeqSubstituteIdx(args, i))
      case LetExpr(v, rhs, body) =>
        LetExpr(v, SubstituteIdx(rhs, i), SubstituteIdx(body, i + 1))
      case QuantifierExpr(univ, v, tp, body) =>
        QuantifierExpr(univ, v, tp, SubstituteIdx(body, i + 1))
    }

    function SeqSubstituteIdx(ss: seq<Expr>, i: Idx): seq<Expr>
      requires SeqExprDepth(ss) <= |incarnation| + i
    {
      if ss == [] then [] else
      [SubstituteIdx(ss[0], i)] + SeqSubstituteIdx(ss[1..], i)
    }

    function Substitute(e: Expr): Expr
      requires e.IsDefinedOn(|incarnation|)
    {
      SubstituteIdx(e, 0)
    }

    function MkEntailment(e: Expr): Expr
      requires e.IsDefinedOn(|incarnation|)
    {
      Implies(Conj(ctx), Substitute(e))
    }

    function MkEntailmentSeq(ss: seq<Expr>): seq<Expr>
      requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
    {
      seq(|ss|, (i: nat) requires i < |ss| => MkEntailment(ss[i]))
    }

    lemma MkEntailmentSeqLemma(ss: seq<Expr>, e: Expr)
      requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
      requires e in ss
      ensures MkEntailment(e) in MkEntailmentSeq(ss)
    {
      assert MkEntailment(e) == MkEntailmentSeq(ss)[Index(ss, e)];
    }

    lemma MkEntailmentLemma(e: Expr, st: State, md: M.Model)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < |st|
      requires IsSatisfiedOn(st, md)
      requires MkEntailment(e).Holds(md)
      ensures e.HoldsOn(AdjustState(st), md)
    {
      assert Implies(Conj(ctx), Substitute(e)).IsDefinedOn(|st|) by {
        IsDefinedOnImpliesLemma(Conj(ctx), Substitute(e), st) by {
          EvalConjLemma(ctx, st, md);
          SubstituteIsDefinedOnLemma(e, |st|);
        }
      }
      assert e.HoldsOn(AdjustState(st), md) by { 
        calc {
          e.HoldsOn(AdjustState(st), md);
          { SubstituteIsDefinedOnLemma(e, |st|);
            AdjustStateSubstituteLemma(st, e, md); }
          Substitute(e).HoldsOn(st, md);
          { EvalConjLemma(ctx, st, md);
            AdjustStateSubstituteLemma(st, e, md);
            HoldsOnImpliesLemma(Conj(ctx), Substitute(e), st, md); }
          MkEntailment(e).Holds(md);
        }
      }
   }

    function Add(e: Expr): Context
      requires e.IsDefinedOn(|incarnation|)
    {
      this.(ctx := ctx + [Substitute(e)])
    }

    function SeqSubstitute(ss: seq<Expr>): seq<Expr>
      requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
    {
      seq(|ss|, (i: nat) requires i < |ss| => Substitute(ss[i]))
    }

    lemma GetSeqSubstituteLemma(ss: seq<Expr>, e: Expr) returns (e': Expr) 
      requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
      requires e in SeqSubstitute(ss)
      ensures e' in ss
      ensures Substitute(e') == e
    {
      e' := ss[Index(SeqSubstitute(ss), e)];
    }

    function AddSeq(ss: seq<Expr>): Context
      requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
    {
      this.(ctx := ctx + SeqSubstitute(ss))
    }

    function mkPreContext(proc: Procedure, args: CallArguments): Context
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(|incarnation|)
      ensures |mkPreContext(proc, args).incarnation| == |args|
      ensures forall i <- mkPreContext(proc, args).incarnation :: i in incarnation
    {
      var incrPre := seq(|args|, (i: nat) requires i < |args| => 
        args.IsDefinedOnIn(args[i], |incarnation|);
        incarnation[args[i].v]);
      forall i <- incrPre 
        ensures i in incarnation
      {
        assert i == incrPre[Index(incrPre, i)];
        assert args[Index(incrPre, i)] in args;
        args.IsDefinedOnIn(args[Index(incrPre, i)], |incarnation|);
        assert i == incarnation[args[Index(incrPre, i)].v];
      }
      Context(ctx, incrPre)
    }

    lemma mkPreContextLemma(proc: Procedure, args: CallArguments, s: State)
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(|incarnation|)
      requires forall i <- incarnation :: i < |s|
      ensures mkPreContext(proc, args).AdjustState(s) == args.Eval(AdjustState(s))
    {
      forall i | 0 <= i < |args|
        ensures (mkPreContext(proc, args).AdjustState(s))[i] == args.Eval(AdjustState(s))[i]
      {
        calc {
          (mkPreContext(proc, args).AdjustState(s))[i];
          == { args.IsDefinedOnIn(args[i], |incarnation|); 
               assert incarnation[args[i].v] in incarnation; }
          s[incarnation[args[i].v]];
          ==
          args.Eval(AdjustState(s))[i];
        }
      }
    }

    function mkPostContext(proc: Procedure, args: CallArguments, oldContext: Context): Context
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(|incarnation|)
      requires args.IsDefinedOn(|oldContext.incarnation|)
      requires |oldContext.incarnation| >= args.NumInOutArgs()
      ensures |mkPostContext(proc, args, oldContext).incarnation| == |args| + args.NumInOutArgs()
    {
      var oldNum := args.NumInOutArgs();
      var incrPost: seq<Idx> := seq(|args|, (i: nat) requires i < |args| => 
        args.IsDefinedOnIn(args[i], |incarnation|);
        incarnation[args[i].v]); 
      var incrPostOld: seq<Idx> := seq(args.NumInOutArgs(), (i: nat) requires i < args.NumInOutArgs() => 
        args.InOutArgsLemma(args.InOutArgs()[i]); 
        args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i]), |oldContext.incarnation|);
        oldContext.incarnation[args.InOutArgs()[i]]);
      Context(ctx, incrPost + incrPostOld)
    }

    lemma mkPostContextIncrSubsetLemma(proc: Procedure, args: CallArguments, oldContext: Context, i: nat)
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(|incarnation|)
      requires args.IsDefinedOn(|oldContext.incarnation|)
      requires |oldContext.incarnation| >= args.NumInOutArgs()
      requires i in mkPostContext(proc, args, oldContext).incarnation
      ensures i in oldContext.incarnation || i in incarnation
    {
      var oldNum := args.NumInOutArgs();
      var incrPost: seq<Idx> := seq(|args|, (i: nat) requires i < |args| => 
        args.IsDefinedOnIn(args[i], |incarnation|);
        incarnation[args[i].v]); 
      var incrPostOld: seq<Idx> := seq(args.NumInOutArgs(), (i: nat) requires i < args.NumInOutArgs() => 
        args.InOutArgsLemma(args.InOutArgs()[i]); 
        args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i]), |oldContext.incarnation|);
        oldContext.incarnation[args.InOutArgs()[i]]);
      assert incrPost + incrPostOld == mkPostContext(proc, args, oldContext).incarnation;
      assert i in incrPost + incrPostOld;
      if i in incrPost {
        assert i == incrPost[Index(incrPost, i)];
        args.IsDefinedOnIn(args[Index(incrPost, i)], |incarnation|);
        assert i == incarnation[args[Index(incrPost, i)].v];
      } else {
        assert i in incrPostOld;
        assert i == incrPostOld[Index(incrPostOld, i)];
        args.InOutArgsLemma(args.InOutArgs()[Index(incrPostOld, i)]);
        args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[Index(incrPostOld, i)]), |oldContext.incarnation|);
        assert i == oldContext.incarnation[args.InOutArgs()[Index(incrPostOld, i)]];
      }
    }

    method AddEq(v: Idx, e: Expr) returns (ghost vNew: Idx, context: Context)
      requires v < |incarnation|
      requires e.IsDefinedOn(|incarnation|)
      ensures |incarnation| == |context.incarnation|
      ensures ctx + [Eq(BVar(vNew), Substitute(e))] == context.ctx
      ensures incarnation[v := vNew] == context.incarnation
      ensures forall i <- incarnation :: i < vNew 
      ensures forall c <- ctx :: c.Depth() < vNew
      ensures SeqMax(incarnation) < vNew
      ensures SeqExprDepth(ctx) < vNew
      // ensures 
    {
      var v' := FreshIdx();
      var ctx' := ctx + [Eq(BVar(v'), Substitute(e))];
      var incarnation' := incarnation[v := v'];
      context := Context(ctx', incarnation');
      vNew := v';
    }

    method AddVarSet(vars: set<Idx>) returns (ghost vNew: Idx, context: Context)
      requires forall v <- vars :: v < |incarnation|
      ensures context.ctx         == ctx
      ensures |context.incarnation| == |incarnation|
      ensures forall i: nat :: i in vars ==> context.incarnation[i] == vNew + i
      ensures vNew > SeqMax(incarnation)
      ensures forall c <- ctx :: c.Depth() < vNew
      ensures SeqExprDepth(ctx) < vNew
      ensures forall i: nat :: i !in vars && i < |incarnation| ==> context.incarnation[i] == incarnation[i]
      ensures forall i <- context.incarnation :: i <= vNew + Max'(vars)
    {
      var vars' := vars; 
      var incr' := incarnation;
      var v' := FreshIdx();
      vNew := v';
      while vars' != {}
        invariant |incr'| == |incarnation|
        invariant vars' <= vars
        invariant forall i: nat :: i in vars - vars' ==> incr'[i] == vNew + i
        invariant forall i: nat :: i !in vars - vars' && i < |incarnation| ==> incr'[i] == incarnation[i]
        invariant forall i: nat :: i < |incarnation| ==> incr'[i] <= vNew + Max'(vars)
      {
        var v :| v in vars';
        vars' := vars' - {v};
        incr' := incr'[v := v' + v];
      }
      context := Context(ctx, incr');
    }

    function Delete(n: nat): Context
      requires n <= |incarnation|
    {
      Context(ctx, incarnation[n..])
    }
      

    method AddVars(n: nat) returns (ghost vNew: Idx, context: Context)
      // ensures incarnation <= AddVars(n).incarnation 
      ensures context.ctx         == ctx
      ensures |context.incarnation| == |incarnation| + n
      ensures forall i: nat :: i < n ==> context.incarnation[i] == vNew + i
      ensures forall i: nat :: n <= i < |incarnation| + n ==> context.incarnation[i] == incarnation[i - n]
      ensures forall c <- ctx :: c.Depth() < vNew
      ensures SeqMax(incarnation) < vNew
      ensures SeqExprDepth(ctx) < vNew
    {
      var v := FreshIdx();
      var addOn := seq(n, (i: nat) => v + i);
      context := Context(ctx, addOn + incarnation);
      vNew := v;
    }

    ghost predicate IsDefinedOn(d: Idx)
    {
      forall e <- ctx :: e.IsDefinedOn(d)
    }

    ghost predicate IsSatisfiedOn(s: State, md: M.Model) 
      // reads *
    {
        && IsDefinedOn(|s|)
        && (forall i <- incarnation :: i < |s|)
        && (forall e <- ctx :: e.HoldsOn(s, md))
    }

    lemma SubstituteIdxIsDefinedOnLemma(e: Expr, i: Idx, d: Idx)
      requires e.IsDefinedOn(|incarnation| + i)
      requires forall ic <- incarnation :: ic + i < d
      requires i <= d
      ensures SubstituteIdx(e, i).IsDefinedOn(d)
      ensures SubstituteIdx(e, i).Depth() <= d
      decreases e
    {
      match e 
      case BVar(v) => if v >= i { assert incarnation[v - i] in incarnation; }
      case OperatorExpr(op, args) => 
        SeqSubstituteIdxIsDefinedOnLemma(args, i, d);
      case QuantifierExpr(univ, v, tp, body) =>
        SubstituteIdxIsDefinedOnLemma(body, i + 1, d + 1);
      case FunctionCallExpr(func, args) =>
        SeqSubstituteIdxIsDefinedOnLemma(args, i, d);
      case LetExpr(v, rhs, body) =>
        SubstituteIdxIsDefinedOnLemma(rhs, i, d);
        SubstituteIdxIsDefinedOnLemma(body, i + 1, d + 1);
      case _ =>
    }

    lemma SeqSubstituteIdxIsDefinedOnLemma(ss: seq<Expr>, i: Idx, d: Idx)
      requires SeqExprDepth(ss) <= |incarnation| + i
      requires forall ic <- incarnation :: ic + i < d
      requires i <= d
      ensures forall e <- SeqSubstituteIdx(ss, i) :: e.IsDefinedOn(d)
      ensures SeqExprDepth(SeqSubstituteIdx(ss, i)) <= d
      decreases ss
    {
      if ss != [] {
        SubstituteIdxIsDefinedOnLemma(ss[0], i, d);
        SeqSubstituteIdxIsDefinedOnLemma(ss[1..], i, d);
      }
    }

    // lemma SubstituteIdxIsDefinedOnLemmaOperator

    lemma SubstituteIsDefinedOnLemma(e: Expr, d: Idx)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < d
      ensures Substitute(e).IsDefinedOn(d)
      ensures Substitute(e).Depth() <= d
      decreases e
    {
      SubstituteIdxIsDefinedOnLemma(e, 0, d);
    }

    lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr, tp: M.Type, md: M.Model)
      requires e1.IsDefinedOn(|s1| + 1)
      requires e2.IsDefinedOn(|s2| + 1)
      requires forall b: M.Any | md.HasType(b, tp) :: e1.HoldsOn(s1.Update([b]), md) == e2.HoldsOn(s2.Update([b]), md)
      ensures (forall b: M.Any | md.HasType(b, tp) :: e1.HoldsOn(s1.Update([b]), md)) == (forall b: M.Any | md.HasType(b, tp) :: e2.HoldsOn(s2.Update([b]), md))
    {  }

    lemma ExistsPush(s1: State, s2: State, e1: Expr, e2: Expr, tp: M.Type, md: M.Model)
      requires e1.IsDefinedOn(|s1| + 1)
      requires e2.IsDefinedOn(|s2| + 1)
      requires forall b: M.Any | md.HasType(b, tp) :: e1.HoldsOn(s1.Update([b]), md) == e2.HoldsOn(s2.Update([b]), md)
      ensures (exists b: M.Any | md.HasType(b, tp) :: e1.HoldsOn(s1.Update([b]), md)) == (exists b: M.Any | md.HasType(b, tp) :: e2.HoldsOn(s2.Update([b]), md))
    {  }

    lemma SeqAdjustStateSubstituteIdxLemma(ss: seq<Expr>, s: State, i: Idx, md: M.Model)
      requires SeqExprDepth(ss) <= |incarnation| + i
      requires forall ic <- incarnation :: ic + i < |s|
      requires i <= |s|
      ensures
        (SeqSubstituteIdxIsDefinedOnLemma(ss, i, |s|);
         SeqEval(ss, s[..i] + AdjustState(s[i..]), md) == SeqEval(SeqSubstituteIdx(ss, i), s, md))
      decreases ss
    {
      if ss != [] {
        SeqAdjustStateSubstituteIdxLemma(ss[1..], s, i, md);
        SeqSubstituteIdxIsDefinedOnLemma(ss, i, |s|);
        AdjustStateSubstituteIdxLemma(s, ss[0], i, md);
      }
    }


    lemma AdjustStateSubstituteIdxLemma(s: State, e: Expr, i: Idx, md: M.Model)
      requires e.IsDefinedOn(|incarnation| + i)
      requires forall ic <- incarnation :: ic + i < |s|
      requires i <= |s|
      ensures (SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        e.Eval(s[..i] + AdjustState(s[i..]), md)) == SubstituteIdx(e, i).Eval(s, md)
      decreases e
    {
      match e 
      case OperatorExpr(op, args) => 
        SeqAdjustStateSubstituteIdxLemma(args, s, i, md);
      case FunctionCallExpr(func, args) => 
        SeqAdjustStateSubstituteIdxLemma(args, s, i, md);
      case QuantifierExpr(true, v, tp, body) => 
        SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        assert forall b: M.Any | md.HasType(b, tp.ToType()) :: 
          body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md) == 
          SubstituteIdx(body, i + 1).Eval(s.Update([b]), md) by {
          forall b: M.Any | md.HasType(b, tp.ToType()) 
            ensures body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md) == SubstituteIdx(body, i + 1).Eval(s.Update([b]), md) {
            assert ([b] + s)[..i+1] == [b] + s[..i];
            assert ([b] + s)[i+1..] == s[i..];
            assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]));
            AdjustStateSubstituteIdxLemma([b] + s, body, i + 1, md);
          }
        }
        ForallPush(s[..i] + AdjustState(s[i..]), s, body, SubstituteIdx(body, i + 1), tp.ToType(), md);
      case QuantifierExpr(false, v, tp, body) => 
        SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        assert forall b: M.Any | md.HasType(b, tp.ToType()) :: 
          body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md) == 
          SubstituteIdx(body, i + 1).Eval(s.Update([b]), md) by {
          forall b: M.Any | md.HasType(b, tp.ToType()) 
            ensures body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md) == SubstituteIdx(body, i + 1).Eval(s.Update([b]), md) {
            assert ([b] + s)[..i+1] == [b] + s[..i];
            assert ([b] + s)[i+1..] == s[i..];
            assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]));
            AdjustStateSubstituteIdxLemma([b] + s, body, i + 1, md);
          }
        }
        ExistsPush(s[..i] + AdjustState(s[i..]), s, body, SubstituteIdx(body, i + 1), tp.ToType(), md);
      case BVar(v) => if v >= i { assert incarnation[v - i] in incarnation; }
      case LetExpr(v, rhs, body) => 
        var b := SubstituteIdx(rhs, i).Eval(s, md) by {
          SubstituteIdxIsDefinedOnLemma(rhs, i, |s|);
        }
        if b.Some? {
          var b := b.value;
          calc {
            LetExpr(v, rhs, body).Eval(s[..i] + AdjustState(s[i..]), md);
            ==
            body.Eval((s[..i] + AdjustState(s[i..])).Update([rhs.Eval(s[..i] + AdjustState(s[i..]), md).value]), md);
            == { SubstituteIdxIsDefinedOnLemma(rhs, i, |s|); }
            body.Eval((s[..i] + AdjustState(s[i..])).Update([b]), md);
            == { assert ([b] + s)[..i+1] == [b] + s[..i];
                assert ([b] + s)[i+1..] == s[i..];
                assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..])); }
            body.Eval(([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]), md);
            == { AdjustStateSubstituteIdxLemma([b] + s, body, i + 1, md);
                SubstituteIdxIsDefinedOnLemma(body, i + 1, |s| + 1); }
            SubstituteIdx(body, i + 1).Eval(s.Update([b]), md);
          }
        }
      case _  => 
    }

    lemma AdjustStateSubstituteEvalLemma(s: State, e: Expr, md: M.Model)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < |s|
      ensures Substitute(e).IsDefinedOn(|s|)
      ensures e.Eval(AdjustState(s), md) == Substitute(e).Eval(s, md)
    {
      SubstituteIsDefinedOnLemma(e, |s|);
      AdjustStateSubstituteIdxLemma(s, e, 0, md);
      assert [] + AdjustState(s) == AdjustState(s);
    }

    lemma AdjustStateSubstituteLemma(s: State, e: Expr, md: M.Model)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < |s|
      ensures Substitute(e).IsDefinedOn(|s|)
      ensures e.HoldsOn(AdjustState(s), md) == Substitute(e).HoldsOn(s, md)
    {
      SubstituteIsDefinedOnLemma(e, |s|);
      AdjustStateSubstituteIdxLemma(s, e, 0, md);
      assert [] + AdjustState(s) == AdjustState(s);
    }
  }

  function mkInitialContext(proc: Procedure): Context
  {
    var incr := seq(|proc.Parameters|, (i: nat) => i);
    var incrOld := seq(proc.NumInOutArgs(), (i: nat) requires i < proc.NumInOutArgs() => 
      proc.InOutVarsIdxs()[i]);
    Context(proc.Pre, incr + incrOld)
  }

  lemma mkInitialContextLemma(proc: Procedure, i: nat)
    requires i in mkInitialContext(proc).incarnation
    ensures i < |proc.Parameters| + proc.NumInOutArgs()
  {
    var incr := seq(|proc.Parameters|, (i: nat) => i);
    var incrOld := seq(proc.NumInOutArgs(), (i: nat) requires i < proc.NumInOutArgs() => 
      proc.InOutVarsIdxs()[i]);
    if i in incrOld {
      assert i == proc.InOutVarsIdxs()[Index(incrOld, i)];
      proc.InOutVarsIdxsLemma(proc.Parameters, 0, Index(incrOld, i));
    }
  }
}