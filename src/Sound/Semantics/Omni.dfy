module Omni {
  import opened Defs
  export
    provides Defs, SeqLemma, SemNest, WP, SemCons, SeqSemSingle
    reveals 
      Sem, SeqSem, SeqWP, SemSingle, 
      Continuation, Continuation.Update, Continuation.UpdateAndAdd, Continuation.head, Continuation.Leq,
      Continuation.UpdateHead

  // Q: how to overcome the type error here?
  // function Cons(post: iset<State>, posts: seq<iset<State>>): Continuation {
  //   var x: Continuation := [post] + posts;
  //   x
  // }

  newtype Continuation = s : seq<iset<State>> | |s| > 0 witness [iset{}] {

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

    ghost function UpdateAndAdd(variablesInScope: nat): Continuation {
      ([head] + this).Update(variablesInScope)
    }

    predicate Leq(cont2: Continuation) {
      && |this| == |cont2|
      && forall i: nat :: i < |this| ==> this[i] <= cont2[i]
    }

    lemma LeqUpdate(variablesInScope: nat, cont: Continuation) 
      requires Leq(cont) 
      ensures Update(variablesInScope).Leq(cont.Update(variablesInScope))
    {

    }

    lemma LeqUpdateAndAdd(variablesInScope: nat, cont: Continuation) 
      requires Leq(cont) 
      ensures UpdateAndAdd(variablesInScope).Leq(cont.UpdateAndAdd(variablesInScope))
    {
      ([head] + this).LeqUpdate(variablesInScope, [cont.head] + cont);
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

  greatest predicate SemSingle/*[nat]*/(s: Stmt, st: State, post: iset<State>) 
    requires s.Single()
  {
    match s
    case Check(e)       => 
      && e.IsDefinedOn(|st|) 
      && (st.Eval(e) &&  st in post)
    case Assume(e)      => 
      && e.IsDefinedOn(|st|) 
      && (st.Eval(e) ==> st in post)
    case Assign(x, v)   => 
      && x < |st|
      && v.IsDefinedOn(|st|) 
      && st[x := st.Eval(v)] in post
  }

  greatest predicate Sem/*[nat]*/(s: Stmt, st: State, posts: Continuation) {
    if s.Single() then SemSingle(s, st, posts.head) else
    match s
    case Seq(ss)        => SeqSem(ss, st, posts)
    case Choice(s0, s1) => Sem(s0, st, posts) && Sem(s1, st, posts)
    case NewScope(n, s) => 
      forall vs: State :: |vs| == n ==> Sem(s, st.Update(vs), posts.UpdateAndAdd(n))
    case Escape(l)      => |posts| > l && st in posts[l]
    case Loop(inv, body) => 
      && inv.IsDefinedOn(|st|)
      && st.Eval(inv)
      && Sem(Seq([body, Loop(inv, body)]), st, posts)
  }

  ghost function WP(s: Stmt, posts: Continuation) : iset<State> {
    iset st: State | Sem(s, st, posts)
  }

  greatest predicate SeqSem/*[nat]*/(ss: seq<Stmt>, st: State, posts: Continuation) {
    if ss == [] then st in posts.head else
    forall post': iset<State> :: 
      (forall st: State :: SeqSem(ss[1..], st, posts) ==> st in post') ==> Sem(ss[0], st, posts.UpdateHead(post'))
  }

  ghost function SeqWP(ss: seq<Stmt>, cont: Continuation): iset<State> {
    iset st: State | SeqSem(ss, st, cont)
  }

  greatest lemma SemCons/*[nat]*/(s: Stmt, st: State, posts: Continuation, posts': Continuation)
    requires Sem(s, st, posts)
    requires posts.Leq(posts')
    ensures Sem(s, st, posts')
  {
    match s
    case Seq(ss) => SeqSemCons(ss, st, posts, posts');
    case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
    case _ =>
  }

  greatest lemma SeqSemCons(ss: seq<Stmt>, st: State, posts: Continuation, posts': Continuation)
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

  greatest lemma SemNest(s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
    requires Sem(s, st, posts.UpdateHead(SeqWP(ss, posts)))
    ensures SeqSem([s] + ss, st, posts)
  {
    forall post': iset<State> | (forall st: State :: SeqSem(ss, st, posts) ==> st in post') {
      SemCons(s, st, posts.UpdateHead(SeqWP(ss, posts)), posts.UpdateHead(post'));
    }
  }

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

  greatest lemma SemSeqLemma(ss: seq<Stmt>, st: State, posts: Continuation)
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

  lemma SemSeqLemmak(k: ORDINAL, ss: seq<Stmt>, st: State, posts: Continuation)
    // requires k.Offset > 0
    requires SeqSem#[k](ss, st, posts)
    // ensures Sem#[k+1](Seq(ss), st, posts)
    ensures Sem#[k](Seq(ss), st, posts)
  {

  }

  ghost function SeqWPk(k: ORDINAL, ss: seq<Stmt>, cont: Continuation): iset<State> {
    iset st: State | SeqSem#[k](ss, st, cont)
  }

  lemma SemNestk(k: ORDINAL, s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
    requires Sem#[k](s, st, posts.UpdateHead(SeqWPk(k, ss, posts)))
    ensures SeqSem#[k]([s] + ss, st, posts)
  {
    // forall post': iset<State> | (forall st: State :: SeqSem(ss, st, posts) ==> st in post') {
    //   SemCons(s, st, posts.UpdateHead(SeqWP(ss, posts)), posts.UpdateHead(post'));
    // }
  }

  lemma SemConsk/*[nat]*/(k: ORDINAL, s: Stmt, st: State, posts: Continuation, posts': Continuation)
    requires Sem#[k](s, st, posts)
    requires posts.Leq(posts')
    ensures Sem#[k](s, st, posts')
  {
    // match s
    // case Seq(ss) => SeqSemCons(ss, st, posts, posts');
    // case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
    // case _ =>
  }

  lemma SeqSemSingle'k(k: ORDINAL, s: Stmt, st: State, posts: Continuation)
    requires Sem#[k](s, st, posts)
    ensures SeqSem#[k]([s], st, posts)
  {
    // assert [s][0] == s;
    // assert [s][1..] == [];
    // assert posts.UpdateHead(posts.head) == posts;
    // forall post': iset<State> | (forall st: State :: SeqSem([], st, posts) ==> st in post') 
    //   ensures Sem(s, st, posts.UpdateHead(post')) {
    //   SemCons(s, st, posts, posts.UpdateHead(post'));
    // }
  }
  /**
    (st, Loop(body)) ===> posts

    |-

    exists inv', 
      && forall st <- inv' :: Sem(body, st, posts.Cons(inv'))

  
  inv' := iset st': State | 
    exists n, 
      forall post', 
        SeqSem(SeqOf(n, body), st, posts.Cons(post')) ==> st' in post'
  
   */

  lemma SemLoopk(k: ORDINAL, inv: Expr, body: Stmt, st: State, posts: Continuation)
    requires forall st <- inv.Sem() :: Sem(body, st, posts.Cons(inv.Sem()))
    requires st in inv.Sem()
    ensures Sem#[k](Loop(inv, body), st, posts.Cons(inv.Sem()))
    decreases k
  {
    if k.Offset > 0 {
    assert inv.IsDefinedOn(StateSize(st)) && st.Eval(inv); 
    assert Sem#[k - 1](Seq([body, Loop(inv, body)]), st, posts.Cons(inv.Sem())) by {
      SemSeqLemmak(k - 1, [body, Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
        assert SeqSem#[k - 1]([body, Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
          assert [body] + [Loop(inv, body)] == [body, Loop(inv, body)];
          SemNestk(k - 1,body, [Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
            assert 
              posts.Cons(inv.Sem()).UpdateHead(SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem()))) ==
              posts.Cons(SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem())));
            assert inv.Sem() <= SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem())) by {
              forall st | st in inv.Sem() 
                ensures st in SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem())) {
                  SeqSemSingle'k(k - 1, Loop(inv, body), st, posts.Cons(inv.Sem())) by {
                    assert Sem#[k - 1](Loop(inv, body), st, posts.Cons(inv.Sem())) by {
                    SemLoopk(k - 1, inv, body, st, posts);
                  }
                }
              }
            }
            SemConsk(k - 1, body, st, posts.Cons(inv.Sem()), posts.Cons(SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem()))));
          }
        }
      }
    }
  }
  }

  // lemma SeqSemSingle'k(k: ORDINAL, s: Stmt, st: State, posts: Continuation)
  //   requires Sem#[k](s, st, posts)
  //   ensures SeqSem#[k]([s], st, posts)
  // {
  //   // SemNestk(k, s, [], st, posts);
  // }

  // lemma SemConsk/*[nat]*/(k: ORDINAL, s: Stmt, st: State, posts: Continuation, posts': Continuation)
  //   requires Sem#[k](s, st, posts)
  //   requires posts.Leq(posts')
  //   ensures Sem#[k](s, st, posts')
  // {
  //   // match s
  //   // case Seq(ss) => SeqSemConsk(k, ss, st, posts, posts');
  //   // case NewScope(n, s) => posts.LeqUpdateAndAdd(n, posts');
  //   // case _ =>
  // }

  // lemma SemSeqLemmak(k: ORDINAL, ss: seq<Stmt>, st: State, posts: Continuation)
  //   requires SeqSem#[k](ss, st, posts)
  //   ensures Sem#[k](Seq(ss), st, posts)
  // {

  // }

  // lemma SemNestk(k: ORDINAL, s: Stmt, ss: seq<Stmt>, st: State, posts: Continuation) 
  //   requires Sem#[k](s, st, posts.UpdateHead(SeqWPk(k, ss, posts)))
  //   ensures SeqSem#[k]([s] + ss, st, posts)
  // {
  //   forall post': iset<State> | (forall st: State :: SeqSem#[k](ss, st, posts) ==> st in post') {
  //     SemConsk(k, s, st, posts.UpdateHead(SeqWPk(k, ss, posts)), posts.UpdateHead(post'));
  //   }
  // }

  // ghost function SeqWPk(k: ORDINAL, ss: seq<Stmt>, cont: Continuation): iset<State> {
  //   iset st: State | SeqSem#[k](ss, st, cont)
  // }

  // greatest lemma InSeqWPLemma(k: ORDINAL, ss: seq<Stmt>, st: State, posts: Continuation)
  //   requires SeqSem#[k](ss, st, posts)
  //   ensures st in SeqWPk(k, ss, posts)
  // { 

  // }

  // lemma SemLoop(k: ORDINAL, inv: Expr, body: Stmt, st: State, posts: Continuation)
  //   requires forall st <- inv.Sem() :: Sem#[k](body, st, posts.Cons(inv.Sem()))
  //   requires st in inv.Sem()
  //   ensures Sem#[k](Loop(inv, body), st, posts.Cons(inv.Sem()))
  // {
  //   assert inv.IsDefinedOn(StateSize(st)) && st.Eval(inv); 
  //   assert Sem#[k - 1](Seq([body, Loop(inv, body)]), st, posts.Cons(inv.Sem())) by {
  //     SemSeqLemma#[k - 1]([body, Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //       // BUG: this is not working
  //       assert SeqSem#[k - 1]([body, Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //         assert [body] + [Loop(inv, body)] == [body, Loop(inv, body)];
  //         SemNestk(k - 1, body, [Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //           assert 
  //             posts.Cons(inv.Sem()).UpdateHead(SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem()))) ==
  //             posts.Cons(SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem())));
  //           assert inv.Sem() <= SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem())) by {
  //             forall st | st in inv.Sem() 
  //               ensures st in SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem())) {
  //               InSeqWPLemma(k - 1, [Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //                 SeqSemSingle'k(k - 1, Loop(inv, body), st, posts.Cons(inv.Sem())) by {
  //                   SemLoop(k - 1, inv, body, st, posts);
  //                 }
  //               }
  //             }
  //           }
  //           SemConsk(k - 1, body, st, posts.Cons(inv.Sem()), posts.Cons(SeqWPk(k - 1, [Loop(inv, body)], posts.Cons(inv.Sem()))));
  //         }
  //       }
  //     }
  //   }
  // }
  

  greatest lemma SemLoop(inv: Expr, body: Stmt, st: State, posts: Continuation)
    requires forall st <- inv.Sem() :: Sem(body, st, posts.Cons(inv.Sem())) // [inv.Sem()] + posts
    requires st in inv.Sem()
    ensures Sem(Loop(inv, body), st, posts.Cons(iset{}))
  // {
  //   assert inv.IsDefinedOn(StateSize(st)) && st.Eval(inv); 
  //   assert Sem(Seq([body, Loop(inv, body)]), st, posts.Cons(inv.Sem())) by {
  //     SemSeqLemma([body, Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //       // BUG: this is not working
  //       // assert SeqSem([body, Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //         assert [body] + [Loop(inv, body)] == [body, Loop(inv, body)];
  //         SemNest(body, [Loop(inv, body)], st, posts.Cons(inv.Sem())) by {
  //           assert 
  //             posts.Cons(inv.Sem()).UpdateHead(SeqWP([Loop(inv, body)], posts.Cons(inv.Sem()))) ==
  //             posts.Cons(SeqWP([Loop(inv, body)], posts.Cons(inv.Sem())));
  //           assert inv.Sem() <= SeqWP([Loop(inv, body)], posts.Cons(inv.Sem())) by {
  //             forall st | st in inv.Sem() 
  //               ensures st in SeqWP([Loop(inv, body)], posts.Cons(inv.Sem())) {
  //                 SeqSemSingle'(Loop(inv, body), st, posts.Cons(inv.Sem())) by {
  //                   assert Sem(Loop(inv, body), st, posts.Cons(inv.Sem())) by {
  //                   SemLoop(inv, body, st, posts);
  //                 }
  //               }
  //             }
  //           }
  //           SemCons(body, st, posts.Cons(inv.Sem()), posts.Cons(SeqWP([Loop(inv, body)], posts.Cons(inv.Sem()))));
  //         }
  //     }
  //   }
  // }

  // lemma SemLoop(inv: Expr, body: Stmt, st: State, posts: Continuation)
  //   ensures Sem(body, st, posts.UpdateHead(SeqWP([body, Loop(inv, body)], posts)))
  //   requires Sem(Loop(inv, body), st, posts)
  // // {

  // // }
  
}