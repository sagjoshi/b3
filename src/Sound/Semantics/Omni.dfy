module Omni {
  import opened Utils
  import opened State
  import M = Model
  import opened Expr
  import opened AST
  export
    provides Utils, AST, State, Expr,
      SeqLemma, SemNest, SemCons, SeqSemCons, SeqSemSingle, 
      RefSem, SeqRefSem, SemSoundProcs, SingleCont,
      SemLoopWithCont, InvSem,
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

  function SingleCont(post: iset<State>): Continuation {
    [post]
  }

  /**
    wp ( (1 :: (1 :: 2 := A; exit(1)); 1 := B);) [post] st == 
    wp ((1 :: 2 := A; exit(1)); 1 := B) [Upd(post), Upd(post)] st ==
    wp (1 :: 2 := A; exit(1)) [Upd(post)[1/B], Upd(post)] st == 
    wp (2 := A; exit(1)) [Upd(Upd(post)[1/B]), Upd(Upd(post)[1/B]), Upd2(post)] st ==
    wp (exit(1)) [[Upd(Upd(post)[1/B])[2/A]], Upd(Upd(post)[1/B]), Upd2(post)] st ==
    st in Upd(Upd(post)[1/B])

   */ 

  ghost predicate SemSingle(s: Stmt, st: State, post: iset<State>, m: M.Model) 
    requires s.Single()
    // reads *
  {
    match s
    case Check(e)       => 
      && e.IsDefinedOn(|st|) 
      && (e.HoldsOn(st, m) &&  st in post)
    case Assume(e)      => 
      && e.IsDefinedOn(|st|) 
      && (e.HoldsOn(st, m) ==> st in post)
    case Assign(x, v)   =>
        && x < |st|
        && v.IsDefinedOn(|st|)
        && (v.Eval(st, m).Some? ==> st[x := v.Eval(st, m).value] in post)
    case Call(proc, args) =>
      && args.IsDefinedOn(|st|)
      && var callSt := args.Eval(st);
        && (forall e <- proc.Pre :: e.IsDefinedOn(|callSt|) && e.HoldsOn(callSt, m))
        && forall st': State :: (
          && st' in st.EqExcept(args.OutArgs())
          && var callSt' := args.Eval(st') + args.EvalOld(st);
            (forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && e.HoldsOn(callSt', m)))
              ==> st' in post
  }

  ghost predicate PreservesInv(inv: iset<State>, body: Stmt, posts: Continuation, m: M.Model)
    // reads *
  { 
    forall st': State :: 
      st' in inv ==> Sem(body, st', posts.UpdateHead(inv), m)
  }

  ghost predicate Sem(s: Stmt, st: State, posts: Continuation, m: M.Model) 
    // reads *
  {
    if s.Single() then SemSingle(s, st, posts.head, m) else
    match s
    case Seq(ss)        => SeqSem(ss, st, posts, m)
    case Choice(s0, s1) => Sem(s0, st, posts, m) && Sem(s1, st, posts, m)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> Sem(s, st.Update(vs), posts.UpdateAndAdd(n), m)
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(_, body) => 
      exists inv: iset<State> :: 
        && st in inv
        && forall st': State :: 
          st' in inv ==> Sem(body, st', posts.UpdateHead(inv), m)
  }

  greatest predicate RefSem(s: Stmt, st: State, posts: Continuation, m: M.Model) 
    reads *
  {
    match s
    case Check(e)       => 
      e.RefHoldsOn(st, m) &&  st in posts.head
    case Assume(e)      =>  
      e.RefHoldsOn(st, m) ==> st in posts.head
    case Assign(x, v)   => 
      && x < st.Size()
      && (v.RefEval(st, (iset v | true), m) ==>
        v.RefEval(st, (iset v {:trigger} | st.UpdateAt(x, v) in posts.head), m))
    case Call(proc, args) => 
      && RefProcedureIsSound(proc, m)
      && args.IsDefinedOn(|st|)
      && var callSt := args.Eval(st);
        && (forall e <- proc.Pre :: e.RefHoldsOn(callSt, m))
        && forall st': State :: (
          && st' in st.EqExcept(args.OutArgs())
          && var callSt' := args.Eval(st') + args.EvalOld(st);
            (forall e <- proc.Post :: e.RefHoldsOn(callSt', m)))
              ==> st' in posts.head
    case Seq(ss)        => SeqRefSem(ss, st, posts, m)
    case Choice(s0, s1) => RefSem(s0, st, posts, m) && RefSem(s1, st, posts, m)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> RefSem(s, st.Update(vs), posts.UpdateAndAdd(n), m)
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(inv, body) => RefSem(Seq([body, Loop(inv, body)]), st, posts, m)
  }

  greatest predicate SeqRefSem(ss: seq<Stmt>, st: State, posts: Continuation, m: M.Model) 
    reads *
  {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqRefSem(ss[1..], st, posts, m) ==> st in post') ==> RefSem(ss[0], st, posts.UpdateHead(post'), m)
  }

  greatest predicate RefProcedureIsSound(proc: Procedure, m: M.Model) 
    reads *
  {
    proc.Body.Some? ==>
      forall st: State :: st in proc.PreSet(m) ==>
        RefSem(proc.Body.value, st, SingleCont(proc.PostSet(m)), m)
  }

  ghost predicate ProcedureIsSound(proc: Procedure, m: M.Model) 
    reads *
  {
    proc.Body.Some? ==>
      forall st: State :: st in proc.PreSet(m) ==>
        Sem(proc.Body.value, st, [proc.PostSet(m)], m)
  }
 
  ghost function WP(s: Stmt, posts: Continuation, m: M.Model) : iset<State> 
    reads *
  {
    iset st: State | Sem(s, st, posts, m)
  }

  ghost predicate SeqSem(ss: seq<Stmt>, st: State, posts: Continuation, m: M.Model) 
    // reads *
  {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, posts, m) ==> st in post') ==> Sem(ss[0], st, posts.UpdateHead(post'), m)
  }

  ghost function SeqWP(ss: seq<Stmt>, cont: Continuation, m: M.Model): iset<State> 
    // reads *
  {
    iset st: State | SeqSem(ss, st, cont, m)
  }

  lemma SemCons(s: Stmt, st: State, posts: Continuation, posts': Continuation, m: M.Model)
    requires Sem(s, st, posts, m)
    requires posts.Leq(posts')
    ensures Sem(s, st, posts', m)
  {
    match s
    case Seq(ss) => SeqSemCons(ss, st, posts, posts', m);
    case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
    case Loop(_, body) => forall inv { posts.LeqUpdateHead(inv, posts'); }
    case _ =>
  }

  lemma SeqSemCons(ss: seq<Stmt>, st: State, posts: Continuation, posts': Continuation, m: M.Model)
    requires SeqSem(ss, st, posts, m)
    requires posts.Leq(posts')
    ensures SeqSem(ss, st, posts', m)
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall post': iset<State> | (forall st: State :: SeqSem(ss[1..], st, posts', m) ==> st in post') {
        SemCons(ss[0], st, posts.UpdateHead(post'), posts'.UpdateHead(post'), m);
      }
    }
  }

  lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation, m: M.Model) 
    requires Sem(s, st, posts.UpdateHead(SeqWP(ss, posts, m)), m)
    ensures SeqSem([s] + ss, st, posts, m)
  {
    forall post': iset<State> | (forall st: State :: SeqSem(ss, st, posts, m) ==> st in post') {
      SemCons(s, st, posts.UpdateHead(SeqWP(ss, posts, m)), posts.UpdateHead(post'), m);
    }
  }

  // lemma SemUnNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
  //   requires SeqSem([s] + ss, st, posts)
  //   ensures Sem(s, st, posts.UpdateHead(SeqWP(ss, posts)))
  // {
  //   // assert ([s] + ss)[0] == s;
  //   // assert ([s] + ss)[1..] == ss; 
  // }

  lemma SeqSemSingle(s: Stmt, st: State, posts: Continuation, m: M.Model)
    requires SeqSem([s], st, posts, m)
    ensures Sem(s, st, posts, m)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
    assert posts == posts.UpdateHead(posts.head);
  }

  lemma SeqSemNest(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, posts: Continuation, m: M.Model) 
    requires SeqSem(ss1 + ss2, st, posts, m)
    ensures SeqSem(ss1, st, posts.UpdateHead(SeqWP(ss2, posts, m)), m)
  {
    if ss1 == [] {
      assert [] + ss2 == ss2;
    } else {
      assert ([ss1[0]] + (ss1[1..] + ss2))[0] == ss1[0];
      assert ss1 + ss2 == [ss1[0]] + (ss1[1..] + ss2); 
      assert forall post': iset<State> :: posts.UpdateHead(SeqWP(ss2, posts, m)).UpdateHead(post') == posts.UpdateHead(post');
    }
  }

  lemma SeqLemma(ss1: seq<Stmt>, ss2: seq<Stmt>, st: State, posts: Continuation, m: M.Model)
    requires Sem(Seq(ss1 + ss2), st, posts, m)
    ensures SeqSem([Seq(ss1)] + ss2, st, posts, m)
  {
    SeqSemNest(ss1, ss2, st, posts, m);
    SemNest(Seq(ss1), ss2, st, posts, m);
  }

  function StateSize(st: State): nat {
    |st|
  }

  lemma SemSeqLemma(ss: seq<Stmt>, st: State, posts: Continuation, m: M.Model)
    requires SeqSem(ss, st, posts, m)
    ensures Sem(Seq(ss), st, posts, m)
  {

  }

  lemma SeqSemSingle'(s: Stmt, st: State, posts: Continuation, m: M.Model)
    requires Sem(s, st, posts, m)
    ensures SeqSem([s], st, posts, m)
  {
    assert [s][0] == s;
    assert [s][1..] == [];
    assert posts.UpdateHead(posts.head) == posts;
    forall post': iset<State> | (forall st: State :: SeqSem([], st, posts, m) ==> st in post') 
      ensures Sem(s, st, posts.UpdateHead(post'), m) {
      SemCons(s, st, posts, posts.UpdateHead(post'), m);
    }
  }

  lemma SemLoopLemma(inv: Expr, body: Stmt, st: State, posts: Continuation, inv': iset<State>, m: M.Model)
    requires st in inv'
    requires forall st': State :: 
      st' in inv' ==> Sem(body, st', posts.UpdateHead(inv'), m)
    ensures Sem(Loop(inv, body), st, posts, m)
  {  }

  lemma PreservesInvLemma(inv: iset<State>, body: Stmt, posts: Continuation, m: M.Model)
    requires PreservesInv(inv, body, posts, m)
    ensures forall st': State :: 
      st' in inv ==> Sem(body, st', posts.UpdateHead(inv), m)
  {  } 

  lemma SemLoopUnroll(s: Stmt, inv: Expr, body: Stmt, st: State, posts: Continuation, m: M.Model)
    requires Sem(Loop(inv, body), st, posts, m)
    ensures Sem(Seq([body, Loop(inv, body)]), st, posts, m)
  {
    var invEx :| st in invEx && PreservesInv(invEx, body, posts, m);
    PreservesInvLemma(invEx, body, posts, m);
    SemNest(body, [Loop(inv, body)], st, posts, m) by {
      SemCons(body, st, posts.UpdateHead(invEx), posts.UpdateHead(SeqWP([Loop(inv, body)], posts, m)), m) by {
        forall st: State | st in invEx ensures SeqSem([Loop(inv, body)], st, posts, m) {
          SeqSemSingle'(Loop(inv, body), st, posts, m) by {
            SemLoopLemma(inv, body, st, posts, invEx, m);
          }
        }
      }
    }
  }

  greatest lemma SemSound(s: Stmt, st: State, posts: Continuation, procs: set<Procedure>, funs: set<Function>, m: M.Model)
    requires Sem(s, st, posts, m)
    requires s.ProceduresCalled() <= procs
    requires s.FunctionsCalled() <= funs
    requires forall p <- procs :: p.ProceduresCalled() <= procs
    requires forall p <- procs :: p.FunctionsCalled() <= funs
    requires forall f <- funs :: f.FunctionsCalled() <= funs
    requires forall p <- procs :: ProcedureIsSound(p, m)
    requires forall f <- funs :: f.IsSound(m)
    ensures RefSem(s, st, posts, m)
  {
      match s
      case Seq(ss) => SeqSemSound(ss, st, posts, procs, funs, m);
      case Loop(inv, body) => 
        SemLoopUnroll(s, inv, body, st, posts, m);
        SemSound(Seq([body, Loop(inv, body)]), st, posts, procs, funs, m) by {
          forall p <- SeqProceduresCalled([body, Loop(inv, body)])
            ensures p in s.ProceduresCalled()
          {
            calc {
              SeqProceduresCalled([body, Loop(inv, body)]);
              ==
              body.ProceduresCalled() + SeqProceduresCalled([Loop(inv, body)]);
              == 
              body.ProceduresCalled() + Loop(inv, body).ProceduresCalled() + SeqProceduresCalled([]);
            }
          }
          forall f <- SeqFunctionsCalled([body, Loop(inv, body)])
            ensures f in s.FunctionsCalled()
          {
            calc {
              SeqFunctionsCalled([body, Loop(inv, body)]);
              ==
              body.FunctionsCalled() + SeqFunctionsCalled([Loop(inv, body)]);
              == 
              body.FunctionsCalled() + Loop(inv, body).FunctionsCalled() + SeqFunctionsCalled([]);
            }
          }

        }
      case Call(proc, args) => 
        var callSt := args.Eval(st);
        forall e <- proc.Pre ensures e.RefHoldsOn(callSt, m) {
          e.HoldsOnSound(callSt, funs, m) by {
            SeqExprFunctionsCalledIn(proc.Pre, e);
          }
        }
        forall post <- proc.Post, st 
          ensures post.RefHoldsOn(st, m) == (post.IsDefinedOn(st.Size()) && post.HoldsOn(st, m))
        {
          post.HoldsOnSound(st, funs, m) by {
            SeqExprFunctionsCalledIn(proc.Post, post);
          }
        }
        assert ProcedureIsSound(proc, m);
        ProcedureIsSoundSound(proc, procs, funs, m);
      case Assume(e) => e.HoldsOnSound(st, funs, m);
      case Check(e) => e.HoldsOnSound(st, funs, m);
      case Assign(x, v) =>
        assert (v.RefEval(st, (iset v {:trigger} | true), m) ==>
        v.RefEval(st, (iset v {:trigger} | st.UpdateAt(x, v) in posts.head), m)) by {
          if v.RefEval(st, (iset v {:trigger} | true), m) {
            v.EvalComplete(st, (iset v {:trigger} | true), m);
            v.EvalSound(st, funs, (iset v {:trigger} | st.UpdateAt(x, v) in posts.head), m);
          }
        }
      case _ =>
  }

  greatest lemma ProcedureIsSoundSound(proc: Procedure, procs: set<Procedure>, funs: set<Function>, m: M.Model)
    requires ProcedureIsSound(proc, m)
    requires proc.ProceduresCalled() <= procs
    requires proc.FunctionsCalled() <= funs
    requires forall f <- funs :: f.IsSound(m)
    requires forall f <- funs :: f.FunctionsCalled() <= funs
    requires forall p <- procs :: p.ProceduresCalled() <= procs
    requires forall p <- procs :: ProcedureIsSound(p, m)
    requires forall p <- procs :: p.FunctionsCalled() <= funs
    ensures RefProcedureIsSound(proc, m)
  {
    if proc.Body.Some? {
      forall st: State | st in proc.PreSet(m)
        ensures RefSem(proc.Body.value, st, SingleCont(proc.PostSet(m)), m) {
        SemSound(proc.Body.value, st, SingleCont(proc.PostSet(m)), procs, funs, m);
      }
    }
  }

  greatest lemma SeqSemSound(ss: seq<Stmt>, st: State, posts: Continuation, procs: set<Procedure>, funs: set<Function>, m: M.Model)
    requires SeqSem(ss, st, posts, m)
    requires SeqProceduresCalled(ss) <= procs
    requires SeqFunctionsCalled(ss) <= funs
    requires forall p <- procs :: p.ProceduresCalled() <= procs
    requires forall f <- funs :: f.FunctionsCalled() <= funs
    requires forall p <- procs :: ProcedureIsSound(p, m)
    requires forall p <- procs :: p.FunctionsCalled() <= funs
    requires forall f <- funs :: f.IsSound(m)
    ensures SeqRefSem(ss, st, posts, m)
  {
    if ss != [] {
      forall post': iset<State> | (forall st: State :: SeqRefSem(ss[1..], st, posts, m) ==> st in post') 
        ensures RefSem(ss[0], st, posts.UpdateHead(post'), m) {
        SemSound(ss[0], st, posts.UpdateHead(post'), procs, funs, m);
      }
    }
  }

  lemma SemSoundProc(proc: Procedure, procs: set<Procedure>, funs: set<Function>, m: M.Model)
    requires proc in procs
    requires proc.ProceduresCalled() <= procs
    requires proc.FunctionsCalled() <= funs
    requires forall f <- funs :: f.IsSound(m)
    requires forall f <- funs :: f.FunctionsCalled() <= funs
    requires forall p <- procs :: p.ProceduresCalled() <= procs
    requires forall p <- procs :: p.FunctionsCalled() <= funs
    requires forall p <- procs :: ProcedureIsSound(p, m)
    ensures RefProcedureIsSound(proc, m)
  {
    if proc.Body.Some? {
      forall st: State | st in proc.PreSet(m)
        ensures RefSem(proc.Body.value, st, SingleCont(proc.PostSet(m)), m) {
        SemSound(proc.Body.value, st, SingleCont(proc.PostSet(m)), procs, funs, m);
      }
    }
  }

  lemma SemSoundProcs(procs: set<Procedure>, funcs: set<Function>, m: M.Model)
    requires forall proc <- procs :: proc.Valid()
    requires forall proc <- procs :: ProcedureIsSound(proc, m)
    requires forall func <- funcs :: func.IsSound(m)
    requires forall proc <- procs :: proc.ProceduresCalled() <= procs
    requires forall proc <- procs :: proc.FunctionsCalled() <= funcs
    requires forall func <- funcs :: func.FunctionsCalled() <= funcs
    ensures  forall proc <- procs :: RefProcedureIsSound(proc, m)
  {
    forall proc <- procs 
      ensures RefProcedureIsSound(proc, m) {
      SemSoundProc(proc, procs, funcs, m);
    }
  }

  lemma SemLoopWithCont(inv: Expr, body: Stmt, cont: seq<Stmt>, st: State, posts: Continuation, inv': iset<State>, m: M.Model)
    requires st in inv'
    requires forall st': State :: 
      st' in inv' ==> Sem(body, st', posts.UpdateHead(inv'), m)
    ensures SeqSem([Loop(inv, body)] + cont, st, posts, m)
  {
    SemNest(Loop(inv, body), cont, st, posts, m) by {
      SemLoopLemma(inv, body, st, posts.UpdateHead(SeqWP(cont, posts, m)), inv', m) by {
        assert posts.UpdateHead(SeqWP(cont, posts, m)).UpdateHead(inv') == posts.UpdateHead(inv');
      }
    }
  }
  
  lemma SemConsDepthLemma(s: Stmt, st: State, posts: Continuation, posts': Continuation, n: nat, m: M.Model)
    requires Sem(s, st, posts, m)
    requires posts.LeqDepth(posts', n)
    requires s.JumpsDefinedOn(n)
    ensures Sem(s, st, posts', m)
  {
    match s
    case Seq(ss) => SeqSemConsDepthLemma(ss, st, posts, posts', n, m);
    case NewScope(k, s) => 
      forall vs: State | |vs| == k
        ensures Sem(s, st.Update(vs), posts'.UpdateAndAdd(k), m) {
        if s.JumpDepth() == 0 {
          SemConsDepthLemma(s, st.Update(vs), posts.UpdateAndAdd(k), posts'.UpdateAndAdd(k), 0, m);
        } else {
          posts.LeqDepthUpdateAndAdd(k, posts', n);
          SemConsDepthLemma(s, st.Update(vs), posts.UpdateAndAdd(k), posts'.UpdateAndAdd(k), n + 1, m);
        }
      }
    case Loop(_, body) => forall inv { posts.LeqDepthUpdateHead(inv, posts', n); }
    case _ =>
  }

  lemma SeqSemConsDepthLemma(ss: seq<Stmt>, st: State, posts: Continuation, posts': Continuation, n: nat, m: M.Model)
    requires SeqSem(ss, st, posts, m)
    requires posts.LeqDepth(posts', n)
    requires SeqJumpsDefinedOn(ss, n)
    ensures SeqSem(ss, st, posts', m)
  {
    if ss != [] {
      assert ss == [ss[0]] + ss[1..];
      forall post': iset<State> | (forall st: State :: SeqSem(ss[1..], st, posts', m) ==> st in post') {
        SemConsDepthLemma(ss[0], st, posts.UpdateHead(post'), posts'.UpdateHead(post'), n, m);
      }
    }
  }

  lemma InvSem(inv: Expr, body: Stmt, st: State, posts: Continuation, stmt: Stmt, m: M.Model)
    requires SeqSem([Assume(inv), body, Check(inv), stmt], st, posts, m)
    requires st in inv.Sem(m)
    ensures Sem(body, st, posts.UpdateHead(inv.Sem(m)), m)
  {
    SeqSemNest([Assume(inv)], [body, Check(inv), stmt], st, posts, m);
    SeqSemSingle(Assume(inv), st, posts.UpdateHead(SeqWP([body, Check(inv), stmt], posts, m)), m);
    assert SeqSem([body, Check(inv), stmt], st, posts, m);
    SeqSemNest([body], [Check(inv), stmt], st, posts, m);
    SeqSemSingle(body, st, posts.UpdateHead(SeqWP([Check(inv), stmt], posts, m)), m);
    SemCons(body, st, posts.UpdateHead(SeqWP([Check(inv), stmt], posts, m)), posts.UpdateHead(inv.Sem(m)), m) by {
      forall st': State | SeqSem([Check(inv), stmt], st', posts, m) ensures st' in inv.Sem(m) {
        SeqSemNest([Check(inv)], [stmt], st', posts, m);
        SeqSemSingle(Check(inv), st', posts.UpdateHead(SeqWP([stmt], posts, m)), m);
      }
    }
  }

  lemma SemPostCheck'Lemma(proc: Procedure, st: State, posts: Continuation, p: seq<Expr>, m: M.Model)
    requires forall e <- p :: e.IsDefinedOn(|proc.Parameters| + proc.NumInOutArgs())
    requires SeqSem(proc.PostCheck'(p), st, posts, m)
    ensures forall e <- p :: e.IsDefinedOn(|st|) && e.HoldsOn(st, m)
  {
    if p != [] {
      forall e <- p 
        ensures e.IsDefinedOn(|st|) && e.HoldsOn(st, m) {
        SeqSemNest([Check(p[0])], proc.PostCheck'(p[1..]), st, posts, m) by {
          assert forall e <- p[1..] :: e in p;
        }
        if e in p[1..] {
          SemPostCheck'Lemma(proc, st, posts, p[1..], m) by {
            forall e <- p[1..]
              ensures e.IsDefinedOn(|proc.Parameters| + proc.NumInOutArgs()) {
              assert e in p;
            }
          }
        }
      }
    }
  }

  lemma SemPostCheckLemma(proc: Procedure, st: State, posts: Continuation, m: M.Model)
    requires proc.Valid()
    requires SeqSem(proc.PostCheck(), st, posts, m)
    ensures forall e <- proc.Post :: e.IsDefinedOn(|st|) && e.HoldsOn(st, m)
  {
    SemPostCheck'Lemma(proc, st, posts, proc.Post, m);
  }
}