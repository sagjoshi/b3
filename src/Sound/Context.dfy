module Context {
  import opened Utils
  import opened AST
  import opened State
  import opened Expr

    function SeqDepthExpr(ss: seq<Expr>): Idx 
      ensures forall e <- ss :: e.Depth() <= SeqDepthExpr(ss)
    {
      if ss == [] then 0 else max(ss[0].Depth(), SeqDepthExpr(ss[1..]))
    }


  function  SeqMax(ss: seq<Idx>): Idx 
    ensures forall i <- ss :: i <= SeqMax(ss)
    ensures forall i: nat :: i < |ss| ==> ss[i] <= SeqMax(ss)
    ensures ss != [] ==> SeqMax(ss) in ss
  {
    if ss == [] then 
      0 
    else
      assert ss == [ss[0]] + (ss[1..]);
      max(ss[0], SeqMax(ss[1..]))
  }

  datatype Context = Context(
    ctx: seq<Expr>,
    incarnation: seq<nat>) 
  {
    ghost const Models : iset<State> := iset st: State | IsSatisfiedOn(st)

    ghost const AdjustedModels : iset<State> := 
      iset st: State | exists st' <- Models {:InAdjustedModelsLemma(st')} :: AdjustState(st') == st

    lemma InAdjustedModelsLemma(st: State, st': State)
      requires IsSatisfiedOn(st')
      requires st == AdjustState(st')
      ensures st in AdjustedModels
    {

    }

    function Depth(): Idx 
    {
      max(SeqDepthExpr(ctx), SeqMax(incarnation))
    }

    function FreshIdx(): Idx
      ensures forall i <- incarnation :: i < FreshIdx()
      ensures SeqDepthExpr(ctx) < FreshIdx()
      ensures forall c <- ctx :: c.Depth() < FreshIdx()
    {
      max(SeqMax(incarnation), SeqDepthExpr(ctx)) + 1
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
      decreases e
    {
      match e
      case BConst(bvalue) => e
      case BVar(v) =>
        if v >= i then  
          BVar(incarnation[v - i] + i) 
        else e
      case And(e0, e1) => 
        And(SubstituteIdx(e0, i), SubstituteIdx(e1, i))
      case Or(e0, e1) => 
        Or(SubstituteIdx(e0, i), SubstituteIdx(e1, i))
      case Not(e) => 
        Not(SubstituteIdx(e, i))
      case Implies(e0, e1) => 
        Implies(SubstituteIdx(e0, i), SubstituteIdx(e1, i))
      case Forall(v, body) => 
        Forall(v, SubstituteIdx(body, i + 1))
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

    // method mkPreContext(proc: Procedure, args: CallArguments) returns (context: Context)
    //   requires Call(proc, args).ValidCalls()
    //   requires args.IsDefinedOn(|incarnation|)
    //   ensures |context.incarnation| == |args|
    //   ensures forall i <- context.incarnation :: i in incarnation
    // {
    //   var incrPre := [];
    //   for i := 0 to |args|
    //     invariant |incrPre| == i
    //     invariant forall j <- incrPre :: j in incarnation
    //     invariant args[..i].Depth() <= args.Depth()
    //     invariant forall s: State :: 
    //       (forall i <- incarnation :: i < |s|) ==> 
    //       Context(ctx, incrPre).AdjustState(s) == args[..i].Eval(AdjustState(s))
    //   {
    //     args.IsDefinedOnIn(args[i], |incarnation|);
    //     incrPre := incrPre + [incarnation[args[i].v]];

    //     assert args[..i + 1].Depth() <= args.Depth() by {
    //       assert args == args[..i + 1] + args[i + 1..];
    //       args[..i + 1].NumInOutArgsConcatLemma(args[i + 1..]);
    //     }
    //   }
    //   context := Context(ctx, incrPre);
    // }

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
      ensures SeqDepthExpr(ctx) < vNew
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
      ensures SeqDepthExpr(ctx) < vNew
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
      ensures SeqDepthExpr(ctx) < vNew
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

    ghost predicate IsSatisfiedOn(s: State) 
    {
        && IsDefinedOn(|s|)
        && (forall i <- incarnation :: i < |s|)
        && (forall e <- ctx :: e.Eval(s))
    }

    ghost predicate Entails(e: Expr) 
    {
      forall s: State ::  
        e.IsDefinedOn(|s|) && IsSatisfiedOn(s) ==> e.Eval(s)
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
      case Forall(v, body) => SubstituteIdxIsDefinedOnLemma(body, i + 1, d + 1);
      case _ =>
    }

    lemma SubstituteIsDefinedOnLemma(e: Expr, d: Idx)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < d
      ensures Substitute(e).IsDefinedOn(d)
      ensures Substitute(e).Depth() <= d
      decreases e
    {
      SubstituteIdxIsDefinedOnLemma(e, 0, d);
    }

    lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr)
      requires e1.IsDefinedOn(|s1| + 1)
      requires e2.IsDefinedOn(|s2| + 1)
      requires forall b: bool :: e1.Eval(s1.Update([b])) == e2.Eval(s2.Update([b]))
      ensures (forall b: bool :: e1.Eval(s1.Update([b]))) == (forall b: bool :: e2.Eval(s2.Update([b])))
    {  }

    lemma AdjustStateSubstituteIdxLemma(s: State, e: Expr, i: Idx)
      requires e.IsDefinedOn(|incarnation| + i)
      requires forall ic <- incarnation :: ic + i < |s|
      requires i <= |s|
      ensures (SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        e.Eval(s[..i] + AdjustState(s[i..]))) == SubstituteIdx(e, i).Eval(s)
      decreases e
    {
      match e 
      case Forall(v, body) =>
        SubstituteIdxIsDefinedOnLemma(e, i, |s|);
        assert forall b: bool :: 
          body.Eval(s[..i] + AdjustState(s[i..]).Update([b])) == 
          SubstituteIdx(body, i + 1).Eval(s.Update([b])) by {
          forall b: bool 
            ensures body.Eval(s[..i] + AdjustState(s[i..]).Update([b])) == SubstituteIdx(body, i + 1).Eval(s.Update([b])) {
            assert ([b] + s)[..i+1] == [b] + s[..i];
            assert ([b] + s)[i+1..] == s[i..];
            assert ((s[..i] + AdjustState(s[i..])).Update([b])) == (([b] + s)[..i+1] + AdjustState(([b] + s)[i+1..]));
            AdjustStateSubstituteIdxLemma([b] + s, body, i + 1);
          }
        }
        ForallPush(s[..i] + AdjustState(s[i..]), s, body, SubstituteIdx(body, i + 1));
      case BVar(v) => if v >= i { assert incarnation[v - i] in incarnation; }
      case _  => 
    }

    lemma AdjustStateSubstituteLemma(s: State, e: Expr)
      requires e.IsDefinedOn(|incarnation|)
      requires forall ic <- incarnation :: ic < |s|
      ensures Substitute(e).IsDefinedOn(|s|)
      ensures e.Eval(AdjustState(s)) == Substitute(e).Eval(s)
    {
      SubstituteIsDefinedOnLemma(e, |s|);
      AdjustStateSubstituteIdxLemma(s, e, 0);
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