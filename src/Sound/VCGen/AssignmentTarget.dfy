module AssignmentTarget {
  import opened Utils
  import opened AST
  import opened State
  import M = Model
  import Omni

  export
    provides Utils, AST, M, Omni, State, Process, Correct
    reveals PairToSet
  
  newtype VarsJumps = map<nat, set<Idx>> {

    ghost function Get(n: nat): iset<Idx> {
      iset i: Idx | In(i, n)
    }

    ghost predicate In(i: Idx, n: nat) 
    {
      n in Keys && i in this[n]
    }      

    function Merge(m1: VarsJumps): VarsJumps {
      map i: Idx | i in Keys + m1.Keys :: 
        if i in Keys then
          if i in m1.Keys then
            this[i] + m1[i]
          else this[i]
        else m1[i]
    }

    function Remove0(): VarsJumps {
      var s0 := if 0 in Keys then this[0] else {};
      map i: Idx | i in Keys - {0} :: this[i] + s0
    }

    opaque function SeqMerge(m: VarsJumps): VarsJumps {
      var s0 := if 0 in Keys then this[0] else {};
      map i: nat | i in (Keys - {0}) + m.Keys :: 
        if i in Keys then
          if i in m.Keys then
            this[i] + s0 + m[i]
          else this[i]
        else m[i] + s0
    }

    lemma SeqMergeKeys(m: VarsJumps)
      ensures SeqMerge(m).Keys == Keys - {0} + m.Keys
    {
      reveal SeqMerge(m);
    }

    lemma SeqMergeGet1(m: VarsJumps, i: Idx, k: nat)
      requires i in Get(0)
      requires k in m.Keys
      ensures i in SeqMerge(m).Get(k)
    {
      reveal SeqMerge(m);
    }

    lemma SeqMergeGet1'(m: VarsJumps, i: Idx, k: nat)
      requires i in Get(k)
      requires k in Keys
      requires k != 0
      ensures i in SeqMerge(m).Get(k)
    {
      reveal SeqMerge(m);
    }

    lemma SeqMergeGet2(m: VarsJumps, i: Idx, k: nat)
      requires i in m.Get(k)
      requires k in m.Keys
      ensures i in SeqMerge(m).Get(k)
    {
      reveal SeqMerge(m);
      var k' :| k' <= k && k' in m.Keys && i in m[k'];
    }

    function SubstractSet(n: nat, s: set<Idx>): set<Idx> 
      ensures forall i: Idx :: i + n in s ==> i in SubstractSet(n, s)
    {
      set i: Idx {:trigger i + n in s} | i <= Max'(s) - n && i + n in s 
    }

    opaque function Substract(n: nat): VarsJumps 
    {
      var m: VarsJumps := map i: nat {: trigger} | 
        && i <= Max'(Keys) + 1
        && i + 1 in Keys :: SubstractSet(n, this[i + 1]);
      if 0 in m.Keys && 0 in Keys then 
        m[0 := m[0] + SubstractSet(n, this[0])]
      else if 0 in Keys then 
        m[0 := SubstractSet(n, this[0])]
      else m
    }

    lemma SubstractPlusOne(n: nat, i: Idx)
      requires i + 1 in Keys
      ensures i in Substract(n).Keys
    {
      reveal Substract(n);
    }

    lemma SubstractZero(n: nat)
      requires 0 in Keys
      ensures 0 in Substract(n).Keys
    {
      reveal Substract(n);
    }

    lemma SubstractGetZero(n: nat, i: Idx)
      requires i + n in Get(0)
      requires 0 in Keys
      ensures i in Substract(n).Get(0)
    {
      SubstractZero(n);
      reveal Substract(n);
    }

    lemma SubstractGet(n: nat, i: Idx, k: nat)
      requires i + n in Get(k)
      requires k > 0
      ensures i in Substract(n).Get(k - 1) 
    {
      reveal Substract(n);
    }

    lemma SubstracOfPlusOne(n: nat, i: Idx)
      requires i + 1 in Keys
      requires i in Substract(n).Keys
      ensures Substract(n)[i] >= SubstractSet(n, this[i + 1])
    {
      reveal Substract(n);
    }

    ghost function ToEqs(st: State, posts: Omni.Continuation): Omni.Continuation 
    {
      seq(|posts|, (k : nat) requires k < |posts| => 
        if k !in Keys then iset{} else
        iset st' |
          && st' in posts[k]
          && |st'| == |st|
          && forall i: Idx :: i < |st| && !(i in Get(k)) ==> st[i] == st'[i]
      )
    }

    ghost function ToEqsAll(st: State): iset<State>
    {
        iset st' |
          && |st'| == |st|
          && forall i: Idx :: i < |st| && !(i in Get(0)) ==> st[i] == st'[i]
    }

    lemma GetLemma(n: nat)
      requires n in Keys
      requires n != 0
      ensures Get(n) <= Remove0().Get(n)
    {
      if 0 in Keys {
        forall i: Idx | i in Get(n) ensures i in Remove0().Get(n) {
          var k :| k <= n && k in Keys && i in this[k];
          if k != 0 {
            assert k in Remove0().Keys;
            assert this[k] <= Remove0()[k];
          } else {
            assert n in Remove0().Keys;
          }
        }
      } else {
        forall i: Idx | i in Get(n) ensures i in Remove0().Get(n) {
          var k :| k <= n && k in Keys && i in this[k];
          assert Remove0().Keys == Keys;
          assert k in Remove0().Keys;
        }
      }
    }
  }

  function Pred(n: nat): nat {
    if n == 0 then 0 else n - 1
  }
  
  function Process'(stmt: Stmt): VarsJumps 
    requires stmt.ValidCalls()
    ensures forall v <- Process'(stmt).Values, s <- v :: s < stmt.Depth()
    decreases stmt
  {
    match stmt
    case Seq(ss) => SeqProcess'(ss)
    case Choice(s0, s1) => 
      var vs0 := Process'(s0);
      var vs1 := Process'(s1);
      vs0.Merge(vs1)
    case NewScope(n, s) => 
      var vs := Process'(s);
      reveal vs.Substract(n);
      vs.Substract(n)
    case Escape(n) => map[n := {}]
    /**
      Loop
        (x++) + (y++; exit 1)
    We need to add all m[0] vars to other m[i] because 
    loop modify 0 vars in first few operations and then
    exit modify other vars
    */
    case Loop(inv, body) => Process'(body).Remove0()
    case Assign(x, _) => map[0 := {x}]
    case Call(proc, args) => 
      args.OutArgsDepthLemma();
      map[0 := args.OutArgs()]
    case _ => map[0 := {}]
  }

  function SeqProcess'(ss: seq<Stmt>): VarsJumps 
    requires SeqValidCalls(ss)
    ensures forall v <- SeqProcess'(ss).Values, s <- v :: s < SeqDepth(ss)
    decreases ss
  {
    if ss == [] then map[0 := {}] else
      var v0 := Process'(ss[0]);
      if 0 in v0.Keys then
        reveal v0.SeqMerge(SeqProcess'(ss[1..]));
        v0.SeqMerge(SeqProcess'(ss[1..]))
      else v0
  }

  lemma Process'Correct(stmt: Stmt, st: State, m: VarsJumps, posts: Omni.Continuation, md: M.Model) 
    requires stmt.ValidCalls()
    requires Process'(stmt) == m
    ensures forall v <- m.Values, s <- v :: s < stmt.Depth()
    requires Omni.Sem(stmt, st, posts, md)
    ensures Omni.Sem(stmt, st, m.ToEqs(st, posts), md)
  {
    match stmt 
    case Choice(s0, s1) =>
      var m0 := Process'(s0);
      var m1 := Process'(s1);
      Omni.SemCons(s0, st, m0.ToEqs(st, posts), m0.Merge(m1).ToEqs(st, posts), md) by {
        Process'Correct(s0, st, m0, posts, md);
      }
      Omni.SemCons(s1, st, m1.ToEqs(st, posts), m0.Merge(m1).ToEqs(st, posts), md) by {
        Process'Correct(s1, st, m1, posts, md);
      }
    case Loop(_, body) =>
      var inv :| 
        && st in inv
        && Omni.PreservesInv(inv, body, posts, md);
      var m' := Process'(body);
      var inv' := inv * m'.ToEqsAll(st);
      assert st in inv';
      forall st': State | st' in inv' ensures Omni.Sem(body, st', (m'.Remove0()).ToEqs(st, posts).UpdateHead(inv'), md) {
        Omni.SemCons(body, st', m'.ToEqs(st', posts.UpdateHead(inv)), (m'.Remove0()).ToEqs(st, posts).UpdateHead(inv'), md) by {
          Process'Correct(body, st', m', posts.UpdateHead(inv), md) by {
            assert Omni.PreservesInv(inv, body, posts, md);
          }
        }
      }
    case NewScope(n, s) => 
      forall vs: State | |vs| == n ensures Omni.Sem(s, st.Update(vs), m.ToEqs(st, posts).UpdateAndAdd(n), md) {
        var m' := Process'(s);
        Omni.SemCons(s, st.Update(vs), m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(n)), m.ToEqs(st, posts).UpdateAndAdd(n), md) by {
          Process'Correct(s, st.Update(vs), m', posts.UpdateAndAdd(n), md);
          forall i: Idx | i < |posts| + 1 
            ensures m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(n))[i] <=
              m'.Substract(n).ToEqs(st, posts).UpdateAndAdd(n)[i]
          {
            forall st': State | st' in m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(n))[i] 
              ensures st' in m'.Substract(n).ToEqs(st, posts).UpdateAndAdd(n)[i] {
              assert st' in posts.UpdateAndAdd(n)[i];
              if i == 0 {
                assert st'[n..] in m'.Substract(n).ToEqs(st, posts).head by {
                  assert forall i: Idx :: i < |st| + n && !(i in m'.Get(0)) ==> st.Update(vs)[i] == st'[i];
                  if 0 in m'.Keys {
                    assert 0 in m'.Substract(n).Keys by { m'.SubstractZero(n); }
                    assert st'[n..] in m'.Substract(n).ToEqs(st, posts).head by {
                      forall i: Idx | i < |st| && !(i in m'.Substract(n).Get(0)) 
                        ensures st[i] == st'[n..][i] {
                        assert !(i + n in m'.Get(0)) by {
                          if i + n in m'.Get(0) {
                            m'.SubstractGetZero(n, i); 
                          }
                        }
                      }
                    }
                  }
                }
              } else {
                assert st'[n..] in m'.Substract(n).ToEqs(st, posts)[i - 1] by {
                  if i in m'.Keys {
                    assert st'[n..] in posts[i - 1] by {
                      calc {
                        st'[n..] in posts[i - 1];
                        { assert Tail(n, st') == st'[n..]; }
                        st' in posts.UpdateAndAdd(n)[i];
                      }
                    }
                    assert forall j: Idx :: j < |st| + n && !(j in m'.Get(i)) ==> st.Update(vs)[j] == st'[j];
                    assert (i - 1) in m'.Substract(n).Keys by {
                      m'.SubstractPlusOne(n, i - 1);
                    }
                    forall j: Idx | j < |st| && !(j in m'.Substract(n).Get(i - 1)) 
                      ensures st[j] == st'[j + n] {
                      assert !(j + n in m'.Get(i)) by {
                        if j + n in m'.Get(i) {
                          m'.SubstractGet(n, j, i);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    case Seq(ss) => SeqProcess'Correct(ss, st, m, posts, md);
    case Call(proc, args) => 
      forall st': State |
        && st' in st.EqExcept(args.OutArgs())
        && var callSt' := args.Eval(st') + args.EvalOld(st);
          (forall e <- proc.Post :: e.IsDefinedOn(|callSt'|) && e.HoldsOn(callSt', md))
        ensures st' in m.ToEqs(st, posts).head
      { assert |st'| == |st|; }
    case _ =>
  }

  lemma SeqProcess'Correct(ss: seq<Stmt>, st: State, m: VarsJumps, posts: Omni.Continuation, md: M.Model) 
    requires SeqValidCalls(ss)
    requires SeqProcess'(ss) == m
    ensures forall v <- m.Values, s <- v :: s < SeqDepth(ss)
    requires Omni.SeqSem(ss, st, posts, md)
    ensures Omni.SeqSem(ss, st, m.ToEqs(st, posts), md)
  {
    if ss != [] {
      Omni.SemNest(ss[0], ss[1..], st, m.ToEqs(st, posts), md) by {
        assert Omni.Sem(ss[0], st, m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..],  m.ToEqs(st, posts), md)), md) by {
          assert Omni.Sem(ss[0], st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)), md);
          var m' := Process'(ss[0]);
          var m'' := SeqProcess'(ss[1..]);
          Process'Correct(ss[0], st, m', posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)), md);
          assert Omni.Sem(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md))), md);
          Omni.SemCons(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md))), 
            m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md)), md) by {
            assert m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md))).Leq(
              m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md))) by {
              if 0 in m'.Keys {
                forall i: Idx | i < |posts| 
                  ensures m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)))[i] <=
                        m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md))[i]
                {
                  forall st': State | st' in m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)))[i] 
                    ensures st' in m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md))[i]
                  {
                    if i == 0 {
                      assert forall j: Idx :: j < |st| && !(j in m'.Get(0)) ==> st[j] == st'[j];
                      SeqProcess'Correct(ss[1..], st', m'', posts, md);
                      Omni.SeqSemCons(ss[1..], st', m''.ToEqs(st', posts), m'.SeqMerge(m'').ToEqs(st, posts), md) by {
                        forall i: Idx | i < |posts| 
                          ensures m''.ToEqs(st', posts)[i] <= m'.SeqMerge(m'').ToEqs(st, posts)[i]
                        {
                          forall st'': State | st'' in m''.ToEqs(st', posts)[i]
                            ensures st'' in m'.SeqMerge(m'').ToEqs(st, posts)[i] {
                            if i in m''.Keys {
                              m'.SeqMergeKeys(m'');
                              forall j: Idx | j < |st| && !(j in m'.SeqMerge(m'').Get(i))
                                ensures st[j] == st''[j] {
                                calc {
                                  st[j];
                                == { if j in m'.Get(0) { m'.SeqMergeGet1(m'', j, i); } }
                                  st'[j];
                                == { if j in m''.Get(i) { m'.SeqMergeGet2(m'', j, i); } }
                                  st''[j];
                                }
                              }
                            } 
                          }
                        }
                      }
                      assert Omni.SeqSem(ss[1..], st', m.ToEqs(st, posts), md);
                    } else {
                      assert st' in m'.SeqMerge(m'').ToEqs(st, posts)[i] by {
                        if i in m'.Keys {
                          m'.SeqMergeKeys(m'');
                          forall j: Idx | j < |st| && !(j in m'.SeqMerge(m'').Get(i))
                            ensures st[j] == st'[j] {
                            if j in m'.Get(i) {
                              m'.SeqMergeGet1'(m'', j, i);
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  function Process(stmt: Stmt): set<Idx> 
    requires stmt.ValidCalls()
    ensures forall v <- Process(stmt) :: v < stmt.Depth()
  {
    var vs := Process'(stmt);
    if 0 in vs.Keys then vs[0] else {}
  } 

  function PairToSet(p: (set<Idx>, bool)): set<Idx> {
    if p.1 then p.0 else {}
  }



  lemma Correct'(stmt: Stmt, st: State, vars: set<Idx>, posts: Omni.Continuation, md: M.Model) 
    requires stmt.ValidCalls()
    requires forall v <- vars :: v < |st|
    requires Omni.Sem(stmt, st, posts, md)
    requires Process(stmt) == vars
    ensures Omni.Sem(stmt, st, posts.UpdateHead(posts.head * st.EqExcept(vars)), md)
  {
    Process'Correct(stmt, st, Process'(stmt), posts, md);
    Omni.SemCons(stmt, st, Process'(stmt).ToEqs(st, posts), posts.UpdateHead(posts.head * st.EqExcept(vars)), md);
  }

  lemma Correct(stmt: Stmt, st: State, st': State, vars: set<Idx>, posts: Omni.Continuation, post: iset<State>, md: M.Model) 
    requires stmt.ValidCalls()
    requires forall v <- vars :: v < |st'|
    requires Omni.Sem(stmt, st, posts.UpdateHead(post), md)
    requires Process(stmt) == vars
    requires st in st'.EqExcept(vars)
    ensures Omni.Sem(stmt, st, posts.UpdateHead(post * st'.EqExcept(vars)), md)
  {
    Correct'(stmt, st, vars, posts.UpdateHead(post), md);
    assert posts.UpdateHead(post).UpdateHead(posts.UpdateHead(post).head * st.EqExcept(vars)) == posts.UpdateHead(post * st.EqExcept(vars));
    Omni.SemCons(stmt, st, posts.UpdateHead(post * st.EqExcept(vars)), posts.UpdateHead(post * st'.EqExcept(vars)), md);
  }
}