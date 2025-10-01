// module AssignmentTarget'' {
  // import opened Defs
  // import Omni

  // export
  //   provides Defs, Omni, Process, Correct
  //   reveals PairToSet, EqsTo
  
  // predicate ShiftedIn(s: set<Idx>, n: nat, i: Idx) {
  //   i + n in s
  // }

  // newtype VarsJumps = map<Idx, nat> {
  //   function Update(n: nat): VarsJumps {
  //     map i: Idx | i in Keys :: if i == 0 then n else Pred(this[i])
  //   }

  //   function Merge(m1: VarsJumps): VarsJumps {
  //     map i: Idx | i in Keys + m1.Keys :: 
  //       if i in Keys then
  //         if i in m1.Keys then
  //           min(this[i], m1[i])
  //         else this[i]
  //       else m1[i]
  //   }

  //   function Substract(n: nat): VarsJumps {
  //     if Keys == {} then map[] else
  //     map i: Idx {:trigger Pred(this[i + n])} | 
  //       && i <= Max(Keys) - n
  //       && i + n in Keys :: Pred(this[i + n])
  //   }

  //   ghost function ToEqs(st: State, j: nat, posts: Omni.Continuation): Omni.Continuation 
  //   {
  //     seq(|posts|, k requires k < |posts| => 
  //       if k < j then 
  //         iset{}
  //       else 
  //         (iset st' |
  //           && st' in posts[k]
  //           && |st'| == |st|
  //           && forall i: Idx :: i < |st| && !(i in Keys && this[i] <= k) ==> st[i] == st'[i]))
  //   }
  // }

  // function Pred(n: nat): nat {
  //   if n == 0 then 0 else n - 1
  // }

  // function Process'(stmt: Stmt): (VarsJumps, nat) 
  //   ensures forall v <- Process'(stmt).0.Keys :: v < stmt.Depth()
  //   decreases stmt
  // {
  //   match stmt
  //   case Seq(ss) => SeqProcess'(ss)
  //   case Choice(s0, s1) => 
  //     var (vs0, b0) := Process'(s0);
  //     var (vs1, b1) := Process'(s1);
  //     (vs0.Merge(vs1), min(b0, b1))
  //   case NewScope(n, s) => 
  //     var (vs, b) := Process'(s);
  //     (vs.Substract(n), Pred(b))
  //   case Escape(n) => (map[], n)
  //   case Loop(inv, body) => Process'(body)
  //   case Assign(x, _) => (map[x := 0], 0)
  //   case _ => (map[], 0)
  // }

  // function SeqProcess'(ss: seq<Stmt>): (VarsJumps, nat) 
  //   ensures forall v <- SeqProcess'(ss).0.Keys :: v < SeqDepth(ss)
  //   decreases ss
  // {
  //   if ss == [] then (map[], 0) else
  //     var (v0, b0) := Process'(ss[0]);
  //     if b0 == 0 then
  //       var (v1, b1) := SeqProcess'(ss[1..]);
  //       (v0.Update(b1).Merge(v1), b1)
  //     else
  //       (v0, b0)
  // }

  // ghost function AllStatesN(n: nat): Omni.Continuation 
  //   requires n > 0
  // {
  //   seq(n, i => AllStates)
  // }

  // lemma Process'Correct(stmt: Stmt, st: State, m: VarsJumps, n: nat, posts: Omni.Continuation) 
  //   requires Process'(stmt) == (m, n)
  //   ensures forall v <- m.Keys :: v < stmt.Depth()
  //   requires Omni.Sem(stmt, st, posts)
  //   ensures Omni.Sem(stmt, st, m.ToEqs(st, n, posts))
  // {
  //   match stmt
  //   case Choice(s0, s1) => 
  //     var (m0, n0) := Process'(s0);
  //     var (m1, n1) := Process'(s1);
  //     Omni.SemCons(s0, st, m0.ToEqs(st, n0, posts), m0.Merge(m1).ToEqs(st, min(n0, n1), posts)) by {
  //       assert m0.ToEqs(st, n0, posts).Leq(m0.Merge(m1).ToEqs(st, min(n0, n1), posts));
  //       Process'Correct(s0, st, m0, n0, posts);
  //     }
  //     Omni.SemCons(s1, st, m1.ToEqs(st, n1, posts), m0.Merge(m1).ToEqs(st, min(n0, n1), posts)) by {
  //       assert m1.ToEqs(st, n1, posts).Leq(m0.Merge(m1).ToEqs(st, min(n0, n1), posts));
  //       Process'Correct(s1, st, m1, n1, posts);
  //     }
  //   case Loop(_, body) => 
  //     var inv :| 
  //       && st in inv
  //       && Omni.PreservesInv(inv, body, posts);
  //     var inv' := inv * m.ToEqs(st, 0, posts.UpdateHead(inv)).head;
  //     assert st in inv';
  //     forall st': State | st' in inv' ensures Omni.Sem(body, st', m.ToEqs(st, n, posts).UpdateHead(inv')) {
  //       Omni.SemCons(body, st', m.ToEqs(st, n, posts.UpdateHead(inv')), m.ToEqs(st, n, posts).UpdateHead(inv')) by {
  //         assert Omni.Sem(body, st', m.ToEqs(st', n, posts.UpdateHead(inv'))) by {
  //           Omni.SemCons(body, st', m.ToEqs(st', n, posts.UpdateHead(inv)), m.ToEqs(st', n, posts.UpdateHead(inv'))) by {
  //             Process'Correct(body, st', m, n, posts.UpdateHead(inv)) by {
  //               assert Omni.PreservesInv(inv, body, posts);
  //             }
  //             assert m.ToEqs(st', n, posts.UpdateHead(inv)).Leq(m.ToEqs(st', n, posts.UpdateHead(inv')));
  //           }
  //         }
  //         Omni.SemCons(body, st', m.ToEqs(st', n, posts.UpdateHead(inv')), m.ToEqs(st, n, posts.UpdateHead(inv')));
  //       }
  //     }
  //   case NewScope(k, body) =>
  //     forall vs: State | |vs| == k ensures Omni.Sem(body, st.Update(vs), m.ToEqs(st, n, posts).UpdateAndAdd(k)) {
  //       var (m', n') := Process'(body);
  //       Omni.SemCons(body, st.Update(vs), m'.ToEqs(st.Update(vs), n', posts.UpdateAndAdd(k)), m.ToEqs(st, n, posts).UpdateAndAdd(k)) by {
  //         Process'Correct(body, st.Update(vs), m', n', posts.UpdateAndAdd(k));
  //         assert m'.ToEqs(st.Update(vs), n', posts.UpdateAndAdd(k)).Leq(m'.Substract(k).ToEqs(st, Pred(n'), posts).UpdateAndAdd(k)) by {
  //           forall i: Idx | i < |posts| + 1 
  //             ensures m'.ToEqs(st.Update(vs), n', posts.UpdateAndAdd(k))[i] <=
  //                   m'.Substract(k).ToEqs(st, Pred(n'), posts).UpdateAndAdd(k)[i]
  //           {
  //             if i >= n' {
  //               forall st': State | 
  //                 && st' in posts.UpdateAndAdd(k)[i]
  //                 && |st'| == |st| + k
  //                 && forall j: Idx :: j < |st| + k && !(j in m'.Keys && m'[j] <= i) ==> st.Update(vs)[j] == st'[j]
  //                 ensures
  //                   st' in m'.Substract(k).ToEqs(st, Pred(n'), posts).UpdateAndAdd(k)[i]
  //               {
  //                 if i == 0 {
  //                   assert st'[k..] in m'.Substract(k).ToEqs(st, 0, posts).head by {
  //                     assert st'[k..] in posts.head by {
  //                       assert st' in posts.UpdateAndAdd(k)[0];
  //                       assert posts.UpdateAndAdd(k)[0] == UpdateSet(k, posts.head);
  //                     }
  //                     forall j: Idx | j < |st| && !(j in m'.Substract(k).Keys && m'.Substract(k)[j] <= 0) 
  //                       ensures st[j] == st'[j + k]
  //                     {
  //                       if j + k in m'.Keys && m'[j + k] <= 0 {
  //                         MaxLemma(m'.Keys, j, k);
  //                         assert j in m'.Substract(k).Keys && m'.Substract(k)[j] <= 0;
  //                       }
  //                       assert !(j + k in m'.Keys && m'[j + k] <= 0);
  //                     }
  //                   }
  //                 } else {
  //                   assert st'[k..] in m'.Substract(k).ToEqs(st, 0, posts)[i - 1] by {
  //                     assert st'[k..] in posts[i - 1] by {
  //                       assert st' in posts.UpdateAndAdd(k)[i];
  //                       assert posts.UpdateAndAdd(k)[i] == UpdateSet(k, posts[i - 1]);
  //                     }
  //                     forall j: Idx | j < |st| && !(j in m'.Substract(k).Keys && m'.Substract(k)[j] <= i - 1) 
  //                       ensures st[j] == st'[j + k]
  //                     {
  //                       if j + k in m'.Keys && m'[j + k] <= i {
  //                         MaxLemma(m'.Keys, j, k);
  //                         assert j in m'.Substract(k).Keys && m'.Substract(k)[j] <= i - 1;
  //                       }
  //                       assert !(j + k in m'.Keys && m'[j + k] <= i);
  //                     }
  //                   }
  //                 }
  //               }
  //             }
  //           }
  //         }
  //       }
  //     }
  //   case Seq(ss) => SeqProcess'Correct(ss, st, m, n, posts);
  //   case _ =>
  // }

  // lemma SeqProcess'Correct(ss: seq<Stmt>, st: State, m: VarsJumps, n: nat, posts: Omni.Continuation) 
  //   requires SeqProcess'(ss) == (m, n)
  //   ensures forall v <- m.Keys :: v < SeqDepth(ss)
  //   requires Omni.SeqSem(ss, st, posts)
  //   ensures Omni.SeqSem(ss, st, m.ToEqs(st, n, posts))
  // {
  //   if ss != [] {
  //     Omni.SemNest(ss[0], ss[1..], st, m.ToEqs(st, n, posts)) by {
  //       assert Omni.Sem(ss[0], st, m.ToEqs(st, n, posts).UpdateHead(Omni.SeqWP(ss[1..],  m.ToEqs(st, n, posts)))) by {
  //         assert Omni.Sem(ss[0], st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts)));
  //         var (m', n') := Process'(ss[0]);
  //         Process'Correct(ss[0], st, m', n', posts.UpdateHead(Omni.SeqWP(ss[1..], posts)));
  //         assert Omni.Sem(ss[0], st, m'.ToEqs(st, n', posts.UpdateHead(Omni.SeqWP(ss[1..], posts))));
  //         if n' != 0 {
  //           Omni.SemCons(ss[0], st, m'.ToEqs(st, n', posts.UpdateHead(Omni.SeqWP(ss[1..], posts))), 
  //             m.ToEqs(st, n, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, n, posts))));
  //         } else {
  //           var (m'', n'') := SeqProcess'(ss[1..]);
  //           assert m == m'.Update(n'').Merge(m'');
  //           assert n == n'';
  //           // ???
  //           // forall st' | Omni.SeqSem(ss[1..], st', posts) { SeqProcess'Correct(ss[1..], st', m'', n'', posts); }
  //           Omni.SemCons(ss[0], st, m'.ToEqs(st, n', posts.UpdateHead(Omni.SeqWP(ss[1..], posts))), 
  //             m.ToEqs(st, n, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, n, posts)))) by 
  //           {
  //             forall i: Idx | i < |posts| 
  //               ensures m'.ToEqs(st, n', posts.UpdateHead(Omni.SeqWP(ss[1..], posts)))[i] <= 
  //                     m.ToEqs(st, n, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, n, posts)))[i] 
  //             {
  //               if i >= n' {
  //                 forall st': State | st' in m'.ToEqs(st, n', posts.UpdateHead(Omni.SeqWP(ss[1..], posts)))[i] 
  //                   ensures st' in m.ToEqs(st, n, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, n, posts)))[i] 
  //                 {
  //                   if i == 0 {
  //                     assert Omni.SeqSem(ss[1..], st', posts);
  //                     SeqProcess'Correct(ss[1..], st', m'', n'', posts);
  //                     Omni.SeqSemCons(ss[1..], st', m''.ToEqs(st', n'', posts), m.ToEqs(st, n, posts));
  //                     assert Omni.SeqSem(ss[1..], st', m.ToEqs(st, n, posts));
  //                   } else {
  //                     assert |st'| == |st|;
  //                     assert st' in posts[i];
  //                     assert forall j: Idx :: j < |st| && !(j in m'.Keys && m'[j] <= i) ==> st[j] == st'[j];
  //                     assert st' in m.ToEqs(st, n, posts)[i] by {
  //                       assert n' == 0;
  //                       assert n == n'';
  //                       forall j: Idx | j < |st| && !(j in m.Keys && m[j] <= i) 
  //                         ensures st[j] == st'[j]
  //                       {
  //                         assume false;
  //                       }
  //                     }
  //                   }
  //                 }
  //               }
  //             }
  //           }
  //         }
  //       }
  //     }
  //   }
  // }

  // function Process(stmt: Stmt): set<Idx> 
  //   ensures forall v <- Process(stmt) :: v < stmt.Depth()
  // {
  //   var (vs, n) := Process'(stmt);
  //   if n == 0 then set i | i in vs.Keys && vs[i] == 0 else {}
  // } 



  // // function Process(stmt: Stmt): (set<Idx>, bool) 
  // //   ensures forall v <- Process(stmt).0 :: v < stmt.Depth()
  // //   decreases stmt
  // // {
  // //   match stmt
  // //   case Seq(ss) => SeqProcess(ss)
  // //   case Choice(s0, s1) => 
  // //     var (vs0, b0) := Process(s0);
  // //     var (vs1, b1) := Process(s1);
  // //     (vs0 + vs1, b0 || b1)
  // //   case NewScope(n, s) => 
  // //     var (vs, b) := Process(s);
  // //     (Substract(vs, n), b)
  // //   case Escape(_) => ({}, false)
  // //   case Loop(inv, body) => Process(body)
  // //   case Assign(x, _) => ({x}, true)
  // //   case _ => ({}, true)
  // // }

  // // function SeqProcess(ss: seq<Stmt>): (set<Idx>, bool) 
  // //   ensures forall v <- SeqProcess(ss).0 :: v < SeqDepth(ss)
  // //   decreases ss
  // // {
  // //   if ss == [] then ({}, true) else
  // //     var (v0, b0) := Process(ss[0]);
  // //     if b0 then
  // //       var (v1, b1) := SeqProcess(ss[1..]);
  // //       (v0 + v1, b0 || b1)
  // //     else
  // //       (v0, b0)
  // // }

  // function PairToSet(p: (set<Idx>, bool)): set<Idx> {
  //   if p.1 then p.0 else {}
  // }

  // ghost function EqsTo(vars: set<Idx>, st: State): iset<State> 
  //   requires forall v <- vars :: v < |st|
  // {
  //   iset st': State | 
  //     && |st'| == |st|
  //     && forall i: Idx :: i < |st| && i !in vars ==> st'[i] == st[i]
  // }


  // lemma Correct'(stmt: Stmt, st: State, vars: set<Idx>, posts: Omni.Continuation, b : bool) 
  //   requires forall v <- vars :: v < |st|
  //   requires Omni.Sem(stmt, st, posts)
  //   requires Process(stmt) == vars
  //   ensures Omni.Sem(stmt, st, posts.UpdateHead(posts.head * EqsTo(vars, st)))

  // lemma Correct(stmt: Stmt, st: State, st': State, vars: set<Idx>, posts: Omni.Continuation, post: iset<State>) 
  //   requires forall v <- vars :: v < |st'|
  //   requires Omni.Sem(stmt, st, posts.UpdateHead(post))
  //   requires Process(stmt) == vars
  //   requires st in EqsTo(vars, st')
  //   ensures Omni.Sem(stmt, st, posts.UpdateHead(post * EqsTo(vars, st')))
    
// }