module Omni {
  import opened Utils
  import opened AST
  import opened State
  import opened Expr
  export
    provides Utils, AST, State, Expr,
      SeqLemma, SemNest, SemCons, SeqSemCons, SeqSemSingle, 
      RefSem, SeqRefSem, SemSoundProcs, 
      SemLoopWithCont, InvSem, VerifiedProcedureCalls, SeqVerifiedProcedureCalls,
      Continuation.Update0, SemConsDepthLemma, SemPostCheckLemma
    reveals 
      Sem, SeqSem, WP, SeqWP, SemSingle, 
      Continuation, Continuation.Update, Continuation.UpdateAndAdd, Continuation.head, 
      Continuation.Leq, Continuation.LeqDepth,
      Continuation.UpdateHead, PreservesInv, Continuation.Get, RefProcedureIsSound, ProcedureIsSound

  /**
  
  Loop(inv, body(x))
  ---
  cc

  check inv;
  x := *
  assume inv;
  body(x);
  check inv;
  ----
  cc
   */

  newtype Continuation = s: seq<iset<State>> | |s| > 0 witness [iset{}] {

    function Get(i: nat): iset<State> 
      requires i < |this|
    {
      this[i]
    }

    ghost const head : iset<State> := this[0]

    function Cons(post: iset<State>): Continuation {
      [post] + this
    }

    ghost function UpdateHead(post: iset<State>): Continuation {
      this[0 := post]
    }

    ghost function Update(variablesInScope: nat): Continuation 
      ensures |this| == |Update(variablesInScope)|
      ensures forall l: nat :: l < |this| ==> Update(variablesInScope)[l] == UpdateSet(variablesInScope, this[l])
    {
      var head' := UpdateSet(variablesInScope, head);
      if |this| == 1 then [head'] else [head'] + this[1..].Update(variablesInScope)
    }

    lemma Update0()
      ensures Update(0) == this
    {
      if |this| == 1 {
        assert UpdateSet(0, head) == head;
      } else {
        assert UpdateSet(0, head) == head;
        this[1..].Update0();
      }
    }

    ghost function UpdateAndAdd(variablesInScope: nat): Continuation {
      ([head] + this).Update(variablesInScope)
    }

    predicate Leq(cont2: Continuation) {
      && |this| == |cont2|
      && forall i: nat :: i < |this| ==> this[i] <= cont2[i]
    }

    predicate LeqDepth(cont2: Continuation, n: nat) {
      && |this| > n
      && |cont2| > n
      && forall i: nat :: i <= n ==> this[i] <= cont2[i]
    }

    lemma LeqUpdate(variablesInScope: nat, cont: Continuation) 
      requires Leq(cont) 
      ensures Update(variablesInScope).Leq(cont.Update(variablesInScope))
    {

    }

    lemma LeqDepthUpdate(variablesInScope: nat, cont: Continuation, n: nat)
      requires LeqDepth(cont, n)
      ensures Update(variablesInScope).LeqDepth(cont.Update(variablesInScope), n)
    {

    }

    lemma LeqUpdateAndAdd(variablesInScope: nat, cont: Continuation) 
      requires Leq(cont) 
      ensures UpdateAndAdd(variablesInScope).Leq(cont.UpdateAndAdd(variablesInScope))
    {
      ([head] + this).LeqUpdate(variablesInScope, [cont.head] + cont);
    }

    lemma LeqDepthUpdateAndAdd(variablesInScope: nat, cont: Continuation, n: nat)
      requires LeqDepth(cont, n)
      ensures UpdateAndAdd(variablesInScope).LeqDepth(cont.UpdateAndAdd(variablesInScope), n + 1)
    {
      ([head] + this).LeqDepthUpdate(variablesInScope, [cont.head] + cont, n + 1);
    }

    lemma LeqUpdateHead(post: iset<State>, cont: Continuation) 
      requires Leq(cont) 
      ensures UpdateHead(post).Leq(cont.UpdateHead(post))
    {
    }

    lemma LeqDepthUpdateHead(post: iset<State>, cont: Continuation, n: nat)
      requires LeqDepth(cont, n)
      ensures UpdateHead(post).LeqDepth(cont.UpdateHead(post), n)
    {
    }
  }

  /**
    wp ( (1 :: (1 :: 2 := A; exit(1)); 1 := B);) [post] st == 
    wp ((1 :: 2 := A; exit(1)); 1 := B) [Upd(post), Upd(post)] st ==
    wp (1 :: 2 := A; exit(1)) [Upd(post)[1/B], Upd(post)] st == 
    wp (2 := A; exit(1)) [Upd(Upd(post)[1/B]), Upd(Upd(post)[1/B]), Upd2(post)] st ==
    wp (exit(1)) [[Upd(Upd(post)[1/B])[2/A]], Upd(Upd(post)[1/B]), Upd2(post)] st ==
    st in Upd(Upd(post)[1/B])

   */ 

  ghost predicate SemSingle(s: Stmt, st: State, post: iset<State>) 
    requires s.Single()
  {
    match s
    case Check(e)       => 
      && e.IsDefinedOn(|st|) 
      && (e.HoldsOn(st) &&  st in post)
    case Assume(e)      => 
      && e.IsDefinedOn(|st|) 
      && (e.HoldsOn(st) ==> st in post)
    case Assign(x, v)   =>
        && x < |st|
        && v.IsDefinedOn(|st|)
        // TODO: We need typechecking for this
        && (v.Eval(st).Some? ==> st[x := v.Eval(st).value] in post)
    case Call(proc, args) =>
      && args.IsDefinedOn(|st|)
      && var callSt := args.Eval(st);
        && (forall e <- proc.Pre :: e.IsDefinedOn(|callSt|) && e.HoldsOn(callSt))
        && forall st': State :: (
          && st' in st.EqExcept(args.OutArgs())
          && var callSt' := args.Eval(st') + args.EvalOld(st);
            (forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && e.HoldsOn(callSt')))
              ==> st' in post
  }

  ghost predicate PreservesInv(inv: iset<State>, body: Stmt, posts: Continuation)
  { 
    forall st': State :: 
      st' in inv ==> Sem(body, st', posts.UpdateHead(inv))
  }

  ghost predicate Sem(s: Stmt, st: State, posts: Continuation) {
    if s.Single() then SemSingle(s, st, posts.head) else
    match s
    case Seq(ss)        => SeqSem(ss, st, posts)
    case Choice(s0, s1) => Sem(s0, st, posts) && Sem(s1, st, posts)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> Sem(s, st.Update(vs), posts.UpdateAndAdd(n))
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(_, body) => 
      exists inv: iset<State> :: 
        && st in inv
        && forall st': State :: 
          st' in inv ==> Sem(body, st', posts.UpdateHead(inv))
  }

  greatest predicate RefSem(s: Stmt, st: State, posts: Continuation) 
    reads *
  {
    match s
    case Check(e)       => 
      && e.IsDefinedOn(|st|) 
      && (e.HoldsOn(st) &&  st in posts.head)
    case Assume(e)      => 
      && e.IsDefinedOn(|st|) 
      && (e.HoldsOn(st) ==> st in posts.head)
    case Assign(x, v)   => 
      && x < |st|
      && v.IsDefinedOn(|st|) 
      && (v.Eval(st).Some? ==> st[x := v.Eval(st).value] in posts.head)
    case Call(proc, args) => 
      && RefProcedureIsSound(proc)
      && args.IsDefinedOn(|st|)
      && var callSt := args.Eval(st);
        && (forall e <- proc.Pre :: e.IsDefinedOn(|callSt|) && e.HoldsOn(callSt))
        && forall st': State :: (
          && st' in st.EqExcept(args.OutArgs())
          && var callSt' := args.Eval(st') + args.EvalOld(st);
            (forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && e.HoldsOn(callSt')))
              ==> st' in posts.head
    case Seq(ss)        => SeqRefSem(ss, st, posts)
    case Choice(s0, s1) => RefSem(s0, st, posts) && RefSem(s1, st, posts)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> RefSem(s, st.Update(vs), posts.UpdateAndAdd(n))
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(inv, body) => RefSem(Seq([body, Loop(inv, body)]), st, posts)
  }

  greatest predicate SeqRefSem(ss: seq<Stmt>, st: State, posts: Continuation) 
    reads *
  {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqRefSem(ss[1..], st, posts) ==> st in post') ==> RefSem(ss[0], st, posts.UpdateHead(post'))
  }

  greatest predicate RefProcedureIsSound(proc: Procedure) 
    reads *
  {
    proc.Body.Some? ==>
      forall st: State :: st in proc.PreSet() ==>
        RefSem(proc.Body.value, st, [proc.PostSet()])
  }

  ghost predicate ProcedureIsSound(proc: Procedure) 
    reads proc`Body
  {
    proc.Body.Some? ==>
      forall st: State :: st in proc.PreSet() ==>
        Sem(proc.Body.value, st, [proc.PostSet()])
  }

  ghost predicate VerifiedProcedureCalls(k: ORDINAL, s: Stmt)
    reads *
  {
    forall proc <- s.ProceduresCalled() :: RefProcedureIsSound#[k](proc)
  }

  ghost predicate SeqVerifiedProcedureCalls(k: ORDINAL, ss: seq<Stmt>)
    reads *
  {
    forall s <- ss :: VerifiedProcedureCalls(k, s)
  }

  lemma VerifiedProcedureCallsSeqLemma(k: ORDINAL, ss: seq<Stmt>)
    requires SeqVerifiedProcedureCalls(k, ss)
    ensures VerifiedProcedureCalls(k, Seq(ss))
    // reads *
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall proc <- SeqProceduresCalled(ss)
        ensures RefProcedureIsSound#[k](proc)
      {
        if proc in ss[0].ProceduresCalled() {
          assert ss[0] in ss;
        } else {
          VerifiedProcedureCallsSeqLemma(k, ss[1..]);
        }
      }
    }
  }

  lemma VerifiedProcedureCallsSeqLemma'(k: ORDINAL, s: Stmt, ss: seq<Stmt>)
    requires VerifiedProcedureCalls(k, Seq(ss))
    ensures SeqVerifiedProcedureCalls(k, ss)
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall s <- ss
        ensures VerifiedProcedureCalls(k, s)
      {
        forall proc <- s.ProceduresCalled()
          ensures RefProcedureIsSound#[k](proc)
        {
          SeqProceduresCalledLemma(ss, s, proc);
        }
      }
    }
  }
    

  ghost function WP(s: Stmt, posts: Continuation) : iset<State> {
    iset st: State | Sem(s, st, posts)
  }

  ghost predicate SeqSem(ss: seq<Stmt>, st: State, posts: Continuation) {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, posts) ==> st in post') ==> Sem(ss[0], st, posts.UpdateHead(post'))
  }

  ghost function SeqWP(ss: seq<Stmt>, cont: Continuation): iset<State> {
    iset st: State | SeqSem(ss, st, cont)
  }

  lemma SemCons(s: Stmt, st: State, posts: Continuation, posts': Continuation)
    requires Sem(s, st, posts)
    requires posts.Leq(posts')
    ensures Sem(s, st, posts')
  {
    match s
    case Seq(ss) => SeqSemCons(ss, st, posts, posts');
    case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
    case Loop(_, body) => forall inv { posts.LeqUpdateHead(inv, posts'); }
    case _ =>
  }

  lemma SeqSemCons(ss: seq<Stmt>, st: State, posts: Continuation, posts': Continuation)
    requires SeqSem(ss, st, posts)
    requires posts.Leq(posts')
    ensures SeqSem(ss, st, posts')
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall post': iset<State> | (forall st: State :: SeqSem(ss[1..], st, posts') ==> st in post') {
        SemCons(ss[0], st, posts.UpdateHead(post'), posts'.UpdateHead(post'));
      }
    }
  }

  lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
    requires Sem(s, st, posts.UpdateHead(SeqWP(ss, posts)))
    ensures SeqSem([s] + ss, st, posts)
  {
    forall post': iset<State> | (forall st: State :: SeqSem(ss, st, posts) ==> st in post') {
      SemCons(s, st, posts.UpdateHead(SeqWP(ss, posts)), posts.UpdateHead(post'));
    }
  }

  // lemma SemUnNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
  //   requires SeqSem([s] + ss, st, posts)
  //   ensures Sem(s, st, posts.UpdateHead(SeqWP(ss, posts)))
  // {
  //   // assert ([s] + ss)[0] == s;
  //   // assert ([s] + ss)[1..] == ss; 
  // }

  lemma SeqSemSingle(s: Stmt, st: State, posts: Continuation)
    requires SeqSem([s], st, posts)
    ensures Sem(s, st, posts)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
    assert posts == posts.UpdateHead(posts.head);
  }

  lemma SeqSemNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, posts: Continuation) 
    requires SeqSem(ss1 + ss2, st, posts)
    ensures SeqSem(ss1, st, posts.UpdateHead(SeqWP(ss2, posts)))
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
      assert forall post': iset<State> :: posts.UpdateHead(SeqWP(ss2, posts)).UpdateHead(post') == posts.UpdateHead(post');
    }
  }

  lemma SeqLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, posts: Continuation)
    requires Sem(Seq(ss1 + ss2), st, posts)
    ensures SeqSem([Seq(ss1)] + ss2, st, posts)
  {
    SeqSemNest(ss1, ss2, st, posts);
    SemNest(Seq(ss1), ss2, st, posts);
  }

  function StateSize(st: State): nat {
    |st|
  }

  lemma SemSeqLemma(ss: seq<Stmt>, st: State, posts: Continuation)
    requires SeqSem(ss, st, posts)
    ensures Sem(Seq(ss), st, posts)
  {

  }

  lemma SeqSemSingle'(s: Stmt, st: State, posts: Continuation)
    requires Sem(s, st, posts)
    ensures SeqSem([s], st, posts)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
    assert posts.UpdateHead(posts.head) == posts;
    forall post': iset<State> | (forall st: State :: SeqSem([], st, posts) ==> st in post') 
      ensures Sem(s, st, posts.UpdateHead(post')) {
      SemCons(s, st, posts, posts.UpdateHead(post'));
    }
  }

  lemma SemLoopLemma(inv: Expr, body: Stmt, st: State, posts: Continuation, inv': iset<State>)
    requires st in inv'
    requires forall st': State :: 
      st' in inv' ==> Sem(body, st', posts.UpdateHead(inv'))
    ensures Sem(Loop(inv, body), st, posts)
  {  }

  lemma PreservesInvLemma(inv: iset<State>, body: Stmt, posts: Continuation)
    requires PreservesInv(inv, body, posts)
    ensures forall st': State :: 
      st' in inv ==> Sem(body, st', posts.UpdateHead(inv))
  {  } 

  lemma SemLoopUnroll(s: Stmt, inv: Expr, body: Stmt, st: State, posts: Continuation)
    requires Sem(Loop(inv, body), st, posts)
    ensures Sem(Seq([body, Loop(inv, body)]), st, posts)
  {
    var invEx :| st in invEx && PreservesInv(invEx, body, posts);
    PreservesInvLemma(invEx, body, posts);
    SemNest(body, [Loop(inv, body)], st, posts) by {
      SemCons(body, st, posts.UpdateHead(invEx), posts.UpdateHead(SeqWP([Loop(inv, body)], posts))) by {
        forall st: State | st in invEx ensures SeqSem([Loop(inv, body)], st, posts) {
          SeqSemSingle'(Loop(inv, body), st, posts) by {
            SemLoopLemma(inv, body, st, posts, invEx);
          }
        }
      }
    }
  }

  lemma SemSound(k: ORDINAL, s: Stmt, st: State, posts: Continuation)
    requires Sem(s, st, posts)
    requires forall n :: n < k ==> VerifiedProcedureCalls(n, s)
    ensures RefSem#[k](s, st, posts)
  {
      if k.Offset != 0 {
      match s
      case Seq(ss) =>
        SeqSemSound(k - 1, ss, st, posts) by {
          forall n: ORDINAL | n < k - 1 {
            VerifiedProcedureCallsSeqLemma'(n, s, ss);
          }
        }
      case Loop(inv, body) => 
        SemLoopUnroll(s, inv, body, st, posts);
        SemSound(k - 1, Seq([body, Loop(inv, body)]), st, posts) by {
          forall n: ORDINAL | n < k - 1 
            ensures VerifiedProcedureCalls(n, Seq([body, Loop(inv, body)])) {
            assert VerifiedProcedureCalls(n, Seq([body, Loop(inv, body)])) by {
              VerifiedProcedureCallsSeqLemma(n, [body, Loop(inv, body)]);
            }
          }
        }
      case Call(proc, args) => assert RefProcedureIsSound#[k - 1](proc);
      case _ =>
    }
  }

  lemma SeqSemSound(k: ORDINAL, ss: seq<Stmt>, st: State, posts: Continuation)
    requires SeqSem(ss, st, posts)
    requires forall n: ORDINAL :: n < k ==> SeqVerifiedProcedureCalls(n, ss)
    ensures SeqRefSem#[k](ss, st, posts)
  {
    if k.Offset != 0 {
      if ss != [] {
        forall post': iset<State> | (forall st: State :: SeqRefSem#[k - 1](ss[1..], st, posts) ==> st in post') 
          ensures RefSem#[k - 1](ss[0], st, posts.UpdateHead(post')) {
          SemSound(k - 1, ss[0], st, posts.UpdateHead(post'));
        }
      }
    }
  } 

  lemma SemSoundProc(proc: Procedure, procs: set<Procedure>, k: ORDINAL)
    requires proc in procs
    requires forall proc <- procs :: proc.Valid()
    requires proc.ProceduresCalled() <= procs
    requires proc.Body.Some? ==> 
      forall n: ORDINAL :: n < k ==> VerifiedProcedureCalls(n, proc.Body.value)
    requires ProcedureIsSound(proc)
    ensures RefProcedureIsSound#[k](proc)
  {
    if k.Offset != 0 {
      if proc.Body.Some? {
        forall st: State | st in proc.PreSet()
          ensures RefSem#[k - 1](proc.Body.value, st, [proc.PostSet()]) {
          SemSound(k - 1, proc.Body.value, st, [proc.PostSet()]);
        }
      }
    }
  }

  lemma SemSoundProcsk(k: ORDINAL, procs: set<Procedure>)
    requires forall proc <- procs :: proc.Valid()
    requires forall proc <- procs :: ProcedureIsSound(proc)
    requires forall proc <- procs :: proc.ProceduresCalled() <= procs
    ensures  forall proc <- procs :: RefProcedureIsSound#[k](proc)
  {
    forall proc <- procs 
      ensures RefProcedureIsSound#[k](proc) {
      SemSoundProc(proc, procs, k) by {
        if proc.Body.Some? {
          forall n: ORDINAL | n < k
            ensures VerifiedProcedureCalls(n, proc.Body.value) {
            forall proc' <- proc.Body.value.ProceduresCalled()
              ensures RefProcedureIsSound#[n](proc') {
              assert proc' in procs;
              SemSoundProcsk(n, procs);
            } 
          }
        }
      }
    }
  }

  lemma SemSoundProcs(procs: set<Procedure>)
    requires forall proc <- procs :: proc.Valid()
    requires forall proc <- procs :: ProcedureIsSound(proc)
    requires forall proc <- procs :: proc.ProceduresCalled() <= procs
    ensures  forall proc <- procs :: RefProcedureIsSound(proc)
  {
    forall proc <- procs
      ensures RefProcedureIsSound(proc) {
      forall k: ORDINAL 
        ensures RefProcedureIsSound#[k](proc) {
        SemSoundProcsk(k, procs);
      }
    }
  }

  lemma SemLoopWithCont(inv: Expr, body: Stmt, cont: seq<Stmt>, st: State, posts: Continuation, inv': iset<State>)
    requires st in inv'
    requires forall st': State :: 
      st' in inv' ==> Sem(body, st', posts.UpdateHead(inv'))
    ensures SeqSem([Loop(inv, body)] + cont, st, posts)
  {
    SemNest(Loop(inv, body), cont, st, posts) by {
      SemLoopLemma(inv, body, st, posts.UpdateHead(SeqWP(cont, posts)), inv') by {
        assert posts.UpdateHead(SeqWP(cont, posts)).UpdateHead(inv') == posts.UpdateHead(inv');
      }
    }
  }
  
  lemma SemConsDepthLemma(s: Stmt, st: State, posts: Continuation, posts': Continuation, n: nat)
    requires Sem(s, st, posts)
    requires posts.LeqDepth(posts', n)
    requires s.JumpsDefinedOn(n)
    ensures Sem(s, st, posts')
  {
    match s
    case Seq(ss) => SeqSemConsDepthLemma(ss, st, posts, posts', n);
    case NewScope(m, s) => 
      forall vs: State | |vs| == m 
        ensures Sem(s, st.Update(vs), posts'.UpdateAndAdd(m)) {
        if s.JumpDepth() == 0 {
          SemConsDepthLemma(s, st.Update(vs), posts.UpdateAndAdd(m), posts'.UpdateAndAdd(m), 0);
        } else {
          posts.LeqDepthUpdateAndAdd(m, posts', n);
          SemConsDepthLemma(s, st.Update(vs), posts.UpdateAndAdd(m), posts'.UpdateAndAdd(m), n + 1);
        }
      }
    case Loop(_, body) => forall inv { posts.LeqDepthUpdateHead(inv, posts', n); }
    case _ =>
  }

  lemma SeqSemConsDepthLemma(ss: seq<Stmt>, st: State, posts: Continuation, posts': Continuation, n: nat)
    requires SeqSem(ss, st, posts)
    requires posts.LeqDepth(posts', n)
    requires SeqJumpsDefinedOn(ss, n)
    ensures SeqSem(ss, st, posts')
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall post': iset<State> | (forall st: State :: SeqSem(ss[1..], st, posts') ==> st in post') {
        SemConsDepthLemma(ss[0], st, posts.UpdateHead(post'), posts'.UpdateHead(post'), n);
      }
    }
  }

  lemma InvSem(inv: Expr, body: Stmt, st: State, posts: Continuation, stmt: Stmt)
    requires SeqSem([Assume(inv), body, Check(inv), stmt], st, posts)
    requires st in inv.Sem()
    ensures Sem(body, st, posts.UpdateHead(inv.Sem()))
  {
    SeqSemNest([Assume(inv)], [body, Check(inv), stmt], st, posts);
    SeqSemSingle(Assume(inv), st, posts.UpdateHead(SeqWP([body, Check(inv), stmt], posts)));
    assert SeqSem([body, Check(inv), stmt], st, posts);
    SeqSemNest([body], [Check(inv), stmt], st, posts);
    SeqSemSingle(body, st, posts.UpdateHead(SeqWP([Check(inv), stmt], posts)));
    SemCons(body, st, posts.UpdateHead(SeqWP([Check(inv), stmt], posts)), posts.UpdateHead(inv.Sem())) by {
      forall st': State | SeqSem([Check(inv), stmt], st', posts) ensures st' in inv.Sem() {
        SeqSemNest([Check(inv)], [stmt], st', posts);
        SeqSemSingle(Check(inv), st', posts.UpdateHead(SeqWP([stmt], posts)));
      }
    }
  }

  lemma SemPostCheck'Lemma(proc: Procedure, st: State, posts: Continuation, p: seq<Expr>)
    requires forall e <- p :: e.IsDefinedOn(|proc.Parameters| + proc.NumInOutArgs())
    requires SeqSem(proc.PostCheck'(p), st, posts)
    ensures forall e <- p :: e.IsDefinedOn(|st|) && e.HoldsOn(st)
  {
    if p != [] {
      forall e <- p 
        ensures e.IsDefinedOn(|st|) && e.HoldsOn(st) {
        SeqSemNest([Check(p[0])], proc.PostCheck'(p[1..]), st, posts) by {
          assert forall e <- p[1..] :: e in p;
        }
        if e in p[1..] {
          SemPostCheck'Lemma(proc, st, posts, p[1..]) by {
            forall e <- p[1..]
              ensures e.IsDefinedOn(|proc.Parameters| + proc.NumInOutArgs()) {
              assert e in p;
            }
          }
        }
      }
    }
  }

  lemma SemPostCheckLemma(proc: Procedure, st: State, posts: Continuation)
    requires proc.Valid()
    requires SeqSem(proc.PostCheck(), st, posts)
    ensures forall e <- proc.Post :: e.IsDefinedOn(|st|) && e.HoldsOn(st)
  {
    SemPostCheck'Lemma(proc, st, posts, proc.Post);
  }
}