module AST {
  import opened Std.Wrappers
  import opened Utils
  import M = Model
  import opened State
  import opened Expr

    datatype Stmt =
    | Check(e: Expr)
    | Assume(e: Expr)
    | Seq(ss: seq<Stmt>)
    | Assign(lhs: Idx, rhs: Expr)
    | NewScope(n: nat, s: Stmt)
    | Escape(l: nat)
    | Choice(0: Stmt, 1: Stmt)
    | Loop(inv: Expr, body: Stmt)
    | Call(proc: Procedure, args: CallArguments)
  {

    predicate Single() {
      match this
      case Assign(_, _) => true
      case Check(_) => true
      case Assume(_) => true
      case Call(_, _) => true
      case _ => false
    }

    predicate ValidCalls() {
      match this
      case Call(proc, args) =>
        && (forall e <- proc.Pre :: e.IsDefinedOn(|args|))
        && (forall e <- proc.Post :: e.IsDefinedOn(|args| + args.NumInOutArgs()))
      case Seq(ss) => forall s <- ss :: s.ValidCalls()
      case Choice(s0, s1) => s0.ValidCalls() && s1.ValidCalls()
      case NewScope(n, s) => s.ValidCalls()
      case Loop(inv, body) => body.ValidCalls()
      case _ =>
        true
    }

    function Size(): nat {
      match this
      case Check(_) => 1
      case Assume(_) => 1
      case Seq(ss) => 1 + SeqSize(ss)
      case Assign(_, _) => 1
      case Choice(s0, s1) => 1 + s0.Size() + s1.Size()
      case NewScope(n, s) => 2 + s.Size()
      case Escape(l) => 2
      case Loop(inv, body) => 4 + body.Size()
      case Call(proc, args) => 1
    }

    function Depth(): Idx 
      requires ValidCalls()
    {
      match this
      case Check(e) => e.Depth()
      case Assume(e) => e.Depth()
      case Seq(ss) => SeqDepth(ss)
      case Assign(id, rhs) => max(id + 1, rhs.Depth())
      case Choice(s0, s1) => max(s0.Depth(), s1.Depth())
      case NewScope(n, s) => if s.Depth() <= n then 0 else s.Depth() - n
      case Escape(l) => 0
      case Loop(inv, body) => max(inv.Depth(), body.Depth())
      case Call(proc, args) => args.Depth() + args.NumInOutArgs()
    }

    predicate IsDefinedOn(d: Idx) 
      requires ValidCalls()
    {
      Depth() <= d
    }


    function JumpDepth() : Idx {
      match this
      case Check(e) => 0
      case Assume(e) => 0
      case Assign(id, rhs) => 0
      case Seq(ss) => SeqJumpDepth(ss)
      case Choice(s0, s1) => max(s0.JumpDepth(), s1.JumpDepth())
      case NewScope(n, s) => if s.JumpDepth() == 0 then 0 else s.JumpDepth() - 1
      case Escape(l) => l
      case Loop(inv, body) => body.JumpDepth()
      case Call(proc, args) => 0
    }

    predicate JumpsDefinedOn(d: Idx) {
      JumpDepth() <= d
    }

    function ProceduresCalled(): set<Procedure> {
      match this
      case Call(proc, _) => {proc}
      case Seq(ss) => SeqProceduresCalled(ss)
      case Choice(s0, s1) => s0.ProceduresCalled() + s1.ProceduresCalled()
      case NewScope(_, s) => s.ProceduresCalled()
      case Loop(_, body) => body.ProceduresCalled()
      case _ => {}
    }

    function FunctionsCalled(): set<Function> {
      match this
      case Seq(ss) => SeqFunctionsCalled(ss)
      case Choice(s0, s1) => s0.FunctionsCalled() + s1.FunctionsCalled()
      case NewScope(_, s) => s.FunctionsCalled()
      case Loop(_, body) => body.FunctionsCalled() + inv.FunctionsCalled()
      case Check(e) => e.FunctionsCalled()
      case Assume(e) => e.FunctionsCalled()
      case Assign(_, rhs) => rhs.FunctionsCalled()
      case Call(proc, args) => SeqExprFunctionsCalled(proc.Pre) + SeqExprFunctionsCalled(proc.Post)
      case Escape(l) => {}
    }

    predicate ImmutableVarsIdx(vars: set<Idx>, i: Idx) {
      match this
      case Assign(x, _) => x + i !in vars
      case NewScope(n, s) => s.ImmutableVarsIdx(vars, i + n) 
      case Seq(ss) => SeqImmutableVarsIdx(ss, vars, i)
      case Choice(s0, s1) => s0.ImmutableVarsIdx(vars, i) && s1.ImmutableVarsIdx(vars, i)
      case Loop(_, body) => body.ImmutableVarsIdx(vars, i)
      case _ => true
    }

    predicate ImmutableVars(vars: set<Idx>) {
      ImmutableVarsIdx(vars, 0)
    }

    lemma IsDefinedOnTransitivity(d1: Idx, d2: Idx)
      requires ValidCalls()
      requires d1 <= d2
      ensures IsDefinedOn(d1) ==> IsDefinedOn(d2)
    {  }
  }

  predicate SeqValidCalls(ss: seq<Stmt>) {
    forall s <- ss :: s.ValidCalls()
  }

  // lemma SeqValidCallsLemma(ss: seq<Stmt>, s: Stmt)

  function SeqProceduresCalled(ss: seq<Stmt>): set<Procedure> {
    if ss == [] then {} else ss[0].ProceduresCalled() + SeqProceduresCalled(ss[1..])
  }

  function SeqFunctionsCalled(ss: seq<Stmt>): set<Function> {
    if ss == [] then {} else ss[0].FunctionsCalled() + SeqFunctionsCalled(ss[1..])
  }

  lemma SeqProceduresCalledLemma(ss: seq<Stmt>, s: Stmt, proc: Procedure)
    requires s in ss
    requires proc in s.ProceduresCalled()
    ensures proc in SeqProceduresCalled(ss)
  {

  }

  predicate SeqImmutableVarsIdx(ss: seq<Stmt>, vars: set<Idx>, i: Idx)
  {
    if ss == [] then true else
    ss[0].ImmutableVarsIdx(vars, i) && SeqImmutableVarsIdx(ss[1..], vars, i)
  }


  datatype ParameterMode = In | InOut | Out

  datatype Parameter = Parameter(mode: ParameterMode)
  
  datatype CallArgument =
    | InArgument(v: Idx)
    | InOutArgument(v: Idx) 
    | OutArgument(v: Idx)
  {
    function OutArg(): set<Idx> {
      match this
      case InArgument(v) => {}
      case InOutArgument(v) => {v}
      case OutArgument(v) => {v}
    }

    function IsInOutArg(): bool {
      match this
      case InOutArgument(v) => true
      case _ => false
    }

    function Depth(): Idx {
      match this
      case InArgument(v) => v + 1
      case InOutArgument(v) => v + 1
      case OutArgument(v) => v + 1
    }

    predicate IsDefinedOn(d: Idx) {
      Depth() <= d
    }

    function Eval(s: State): M.Any
      requires IsDefinedOn(|s|)
    {
      match this
      case InArgument(v) => s[v]
      case InOutArgument(v) => s[v]
      case OutArgument(v) => s[v]
    }
  }

  newtype CallArguments = seq<CallArgument> {
    function OutArgs(): set<Idx> {
      if this == [] then {} else this[0].OutArg() + this[1..].OutArgs()
    }

    function InOutArgs(): seq<Idx> 
      ensures |InOutArgs()| == NumInOutArgs()
    {
      if this == [] then 
        [] else 
      if this[0].IsInOutArg() then 
        [this[0].v] + this[1..].InOutArgs() 
      else this[1..].InOutArgs()
    }

    lemma InOutArgsLemma(v: Idx)
      requires v in InOutArgs()
      ensures InOutArgument(v) in this
    {

    }

    lemma OutArgsDepthLemma()
      ensures forall v <- OutArgs() :: v < Depth()
    { }

    function Depth(): Idx {
      if this == [] then 0 else max(this[0].Depth(), this[1..].Depth())
    }

    predicate IsDefinedOn(d: Idx) {
      Depth() <= d
    }

    lemma IsDefinedOnIn(arg: CallArgument, d: Idx)
      requires arg in this
      requires IsDefinedOn(d)
      ensures arg.IsDefinedOn(d)
    { 
      if this != [] {
        if arg != this[0] {
          this[1..].IsDefinedOnIn(arg, d);
        }
      }
    }
      
    function Eval(s: State): State 
      requires IsDefinedOn(|s|)
      ensures |Eval(s)| == |this|
    {
      seq(|this|, (i: nat) requires i < |this| => 
        IsDefinedOnIn(this[i], |s|);
        this[i].Eval(s))
    }

    function EvalOld(s: State): State 
      requires IsDefinedOn(|s|)
      ensures |EvalOld(s)| == NumInOutArgs()
    {
      seq(NumInOutArgs(), (i: nat) requires i < NumInOutArgs() => 
        InOutArgsLemma(InOutArgs()[i]);
        IsDefinedOnIn(InOutArgument(InOutArgs()[i]), |s|);
        s[InOutArgs()[i]]
      )
    }

    function NumInOutArgs(): nat {
      if this == [] then 
        0 
      else 
        if this[0].InOutArgument? then 
          1 + this[1..].NumInOutArgs() 
        else this[1..].NumInOutArgs()
    }

    lemma NumInOutArgsConcatLemma(args: CallArguments)
      ensures (this + args).NumInOutArgs() == NumInOutArgs() + args.NumInOutArgs()
      ensures (this + args).Depth() == max(this.Depth(), args.Depth())
    {
      if this == [] {
        assert this + args == args;
      } else {
        assert (this + args)[0] == this[0];
        assert (this + args)[1..] == this[1..] + args;
        this[1..].NumInOutArgsConcatLemma(args);
      }
    }
  }

  class Procedure {
    const Name: string
    const Parameters: seq<Parameter>
    const Pre: seq<Expr>
    const Post: seq<Expr>
    var Body: Option<Stmt>

    function NumInOutArgs'(Parameters: seq<Parameter>): nat {
      if Parameters == [] then 0 else
      if Parameters[0].mode == InOut then 1 + NumInOutArgs'(Parameters[1..]) else
      NumInOutArgs'(Parameters[1..])
    }

    function NumInOutArgs(): nat {
      NumInOutArgs'(Parameters)
    }

    predicate IsOldVar(i: Idx) 
    {
      |Parameters| <= i
    }

    function OldVars(): set<Idx> {
      set i: Idx | IsOldVar(i) && i < |Parameters| + NumInOutArgs()
    }


    ghost predicate InPreSet(st: State) 
      // reads *
    {
      && |Parameters| + NumInOutArgs() == |st|
      && (forall i: nat :: i < NumInOutArgs() ==> 
        (InOutVarsIdxsLemma(Parameters, 0, i);
         st[i + |Parameters|] == st[InOutVarsIdxs()[i]]))
      && forall e <- Pre :: e.IsDefinedOn(|st|) && e.HoldsOn(st)
    }

    ghost function PreSet(): iset<State> 
      // reads *
    {
      iset st: State | InPreSet(st)
    }

    ghost predicate InPostSet(st: State) 
      // reads *
    {
      forall e <- Post :: e.IsDefinedOn(|st|) && e.HoldsOn(st)
    }

    ghost function PostSet(): iset<State> 
      // reads *
    {
      iset st': State | InPostSet(st')
    }

    function PostCheck'(p: seq<Expr>): seq<Stmt> 
      requires forall e <- p :: e.IsDefinedOn(|Parameters| + NumInOutArgs())
      ensures SeqValidCalls(PostCheck'(p))
      ensures SeqIsDefinedOn(PostCheck'(p), |Parameters| + NumInOutArgs())
      ensures SeqJumpsDefinedOn(PostCheck'(p), 0)
    {
      if p == [] then [] else
        assert forall e <- p[1..] :: e in p;
        assert p[0] in p;
        assert p[0].IsDefinedOn(|Parameters| + NumInOutArgs());
        assert Check(p[0]).IsDefinedOn(|Parameters| + NumInOutArgs());
        [Check(p[0])] + PostCheck'(p[1..])
    }

    function PostCheck(): seq<Stmt> 
      requires Valid()
      ensures SeqValidCalls(PostCheck())
      ensures SeqIsDefinedOn(PostCheck(), |Parameters| + NumInOutArgs())
      reads this`Body
    {
      PostCheck'(Post)
    }

    function InOutVarsIdxs'(parameter: seq<Parameter>, idx: Idx): seq<Idx>
      ensures |InOutVarsIdxs'(parameter, idx)| == NumInOutArgs'(parameter)
    {
      if parameter == [] then [] else
      if parameter[0].mode == InOut then
        [idx] + InOutVarsIdxs'(parameter[1..], idx + 1)
      else
        InOutVarsIdxs'(parameter[1..], idx + 1)
    }

    function InOutVarsIdxs(): seq<Idx>
    {
      InOutVarsIdxs'(Parameters, 0)
    }

    lemma InOutVarsIdxsLemma(parameter: seq<Parameter>, idx: Idx, i: nat)
      requires i < |InOutVarsIdxs'(parameter, idx)|
      ensures InOutVarsIdxs'(parameter, idx)[i] < |parameter| + idx
    {
      if parameter != [] {
        if i != 0 {
          InOutVarsIdxsLemma(parameter[1..], idx + 1, i - 1);
        }
      }
    }

    function InOutArgsState(st: State): State
      requires |Parameters| <= |st|
    {
      seq(|InOutVarsIdxs()|, (i: nat) requires i < |InOutVarsIdxs()| => 
        InOutVarsIdxsLemma(Parameters, 0, i);
        st[InOutVarsIdxs()[i]])
    }

    predicate ValidBody() 
      requires Body.Some?
      reads this`Body
    {
      var body := Body.value;
      && body.ValidCalls()
      && body.IsDefinedOn(|Parameters| + NumInOutArgs())
      && body.JumpsDefinedOn(0)
      && body.ImmutableVars(OldVars())
    }

    predicate Valid() 
      reads this`Body
    {
      && (Body.Some? ==> ValidBody())
      && (forall e <- Pre :: e.IsDefinedOn(|Parameters|))
      && (forall e <- Post :: e.IsDefinedOn(|Parameters| + NumInOutArgs()))
    }

    function ProceduresCalled(): set<Procedure> 
      reads this`Body
    {
      if Body.Some? then Body.value.ProceduresCalled() else {}
    }

    function FunctionsCalled(): set<Function> 
      reads this`Body
    {
      if Body.Some? then Body.value.FunctionsCalled() + SeqExprFunctionsCalled(Pre) + SeqExprFunctionsCalled(Post) else {}
    }
  }

  function SeqSize(ss: seq<Stmt>): nat {
    if ss == [] then 0 else ss[0].Size() + SeqSize(ss[1..])
  }

  lemma SeqSizeSplitLemma(ss: seq<Stmt>)
    requires ss != []
    ensures SeqSize(ss) == ss[0].Size() + SeqSize(ss[1..])
  {  }

  function SeqDepth(ss: seq<Stmt>): nat 
    requires SeqValidCalls(ss)
  {
    if ss == [] then 0 else max(ss[0].Depth(), SeqDepth(ss[1..]))
  }

  predicate SeqIsDefinedOn(ss: seq<Stmt>, d: nat) 
    requires SeqValidCalls(ss)
    ensures SeqIsDefinedOn(ss, d) <==> SeqDepth(ss) <= d
  {
    if ss == [] then true else ss[0].IsDefinedOn(d) && SeqIsDefinedOn(ss[1..], d)
  }

  function SeqJumpDepth(ss: seq<Stmt>): nat {
    if ss == [] then 0 else max(ss[0].JumpDepth(), SeqJumpDepth(ss[1..]))
  }

  predicate SeqJumpsDefinedOn(ss: seq<Stmt>, d: nat) 
    ensures SeqJumpsDefinedOn(ss, d) <==> SeqJumpDepth(ss) <= d
  {
    if ss == [] then true else ss[0].JumpsDefinedOn(d) && SeqJumpsDefinedOn(ss[1..], d)
  }

  lemma SeqFunConcatLemmas(ss1: seq<Stmt>, ss2: seq<Stmt>)
    requires SeqValidCalls(ss1)
    requires SeqValidCalls(ss2)
    ensures SeqSize(ss1 + ss2) == SeqSize(ss1) + SeqSize(ss2)
    ensures SeqDepth(ss1 + ss2) == max(SeqDepth(ss1), SeqDepth(ss2))
    ensures SeqJumpDepth(ss1 + ss2) == max(SeqJumpDepth(ss1), SeqJumpDepth(ss2))
    ensures SeqFunctionsCalled(ss1 + ss2) == SeqFunctionsCalled(ss1) + SeqFunctionsCalled(ss2)
  {
    if ss1 == [] {
      assert ss1 + ss2 == ss2;
    } else {
      assert (ss1 + ss2)[0] == ss1[0];
      assert (ss1 + ss2)[1..] == ss1[1..] + ss2;
    }
  }

}