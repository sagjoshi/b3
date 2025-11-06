module Block {
  import opened Defs
  
  datatype Point = Point(cont: seq<Stmt>, varsInScope: nat)

  newtype Continuation = seq<Point> {
    function Update(cont: seq<Stmt>, varsInScope: nat): Continuation {
      [Point(cont, varsInScope)] + this
    }

    function VarsInScope(l: nat): nat 
      requires l <= |this|
    {
      if l == 0 then 0 else this[0].varsInScope + this[1..].VarsInScope(l - 1)
    }

    function AllVarsInScope(): nat {
      if this == [] then 0 else this[0].varsInScope + this[1..].AllVarsInScope()
    }

    lemma VarsInScopeLeqAll(l: nat)
      requires l <= |this|
      ensures VarsInScope(l) + this[l..].AllVarsInScope() == AllVarsInScope()
    {

    }

    lemma VarsInScopeSuffix(l: nat)
      requires l <= |this|
      ensures VarsInScope(l) == this[..l].AllVarsInScope()
    {
      if l != 0 {
        calc {
          VarsInScope(l);
        ==
          this[0].varsInScope + this[1..].VarsInScope(l - 1);
        == { this[1..].VarsInScopeSuffix(l - 1);
             assert this[1..][..l - 1] == this[1..l]; }
          this[0].varsInScope + this[1..l].AllVarsInScope();
        == { assert this[..l][1..] == this[1..l]; }
          this[..l].AllVarsInScope();
        }

      }
    }

    function Size(): nat {
      if this == [] then 0 else SeqSize(this[0].cont) + 1 + this[1..].Size()
    }

    lemma UpdateSize(cont: seq<Stmt>, varsInScope: nat)
      ensures Update(cont, varsInScope).Size() == SeqSize(cont) + Size() + 1
    {

    }

    lemma SizePrefix(l: nat)
      requires l <= |this|
      ensures this[l..].Size() <= Size()
    {
      assert this[..l] + this[l..] == this;
      SizeConcat(this[..l], this[l..]);
    }

    predicate IsDefinedOn(d: nat) {
      AllVarsInScope() <= d
    }

    predicate JumpsDefined() {
      if this == [] then true else
        SeqJumpsDefinedOn(this[0].cont, |this[1..]|) && this[1..].JumpsDefined()
    }

    predicate VarsDefined(n: nat) 
      requires IsDefinedOn(n)
    {
      if this == [] then true else
        SeqIsDefinedOn(this[0].cont, n - this[0].varsInScope) && this[1..].VarsDefined(n - this[0].varsInScope)
    }

    lemma VarsDefinedTransitivity(n1: nat, n2: nat)
      requires IsDefinedOn(n1)
      requires VarsDefined(n1)
      requires n1 <= n2
      ensures VarsDefined(n2)
    {

    }

    lemma AllVarsInScopeSuffixSucc(l: nat)
      requires l < |this|
      ensures this[..l + 1].AllVarsInScope() == this[..l].AllVarsInScope() + this[l].varsInScope
      // ensures AllVarsInScope() == this[..l + 1].AllVarsInScope()
    {
      VarsInScopeSuffix(l);
      VarsInScopeLeqAll(l);
      VarsInScopeLeqAll(l + 1);
      VarsInScopeSuffix(l + 1);
    }

    lemma DefinedPrefix''(l: nat, n: nat)
      requires l <= |this|
      requires IsDefinedOn(n)
      ensures n >= this[..l].AllVarsInScope()
    {
      VarsInScopeSuffix(l);
      VarsInScopeLeqAll(l);
    }

    lemma DefinedPrefix'(l: nat, n: nat)
      requires l < |this|
      requires JumpsDefined()
      requires IsDefinedOn(n)
      requires VarsDefined(n)
      ensures SeqJumpsDefinedOn(this[l].cont, |this[l + 1..]|) 
      ensures n >= this[..l + 1].AllVarsInScope()
      ensures SeqIsDefinedOn(this[l].cont, n - this[..l + 1].AllVarsInScope())
      // ensures SeqIsDefinedOn(this[l].cont, 1000) /*SOUNDNESS BUG:*/
    {
      DefinedPrefix''(l + 1, n);
      if this != [] {
        if l != 0 {
          assert this[1..][l - 1] == this[l];
          assert this[1..][l - 1..] == this[l..];
          assert this[1..][..l] == this[1..l + 1];
          this[1..].DefinedPrefix'(l - 1, n - this[0].varsInScope);
          assert SeqIsDefinedOn(this[l].cont, n - this[0].varsInScope - this[1..l + 1].AllVarsInScope());
          assert SeqIsDefinedOn(this[l].cont, n - this[..l + 1].AllVarsInScope());
        }
      }
    }

    lemma DefinedPrefix(l: nat, n: nat)
      requires l <= |this|
      requires JumpsDefined()
      requires IsDefinedOn(n)
      requires VarsDefined(n)
      ensures this[l..].JumpsDefined()
      ensures n >= this[..l].AllVarsInScope()
      ensures this[l..].IsDefinedOn(n - this[..l].AllVarsInScope())
      ensures this[l..].VarsDefined(n - this[..l].AllVarsInScope())
      decreases |this| - l
    {
      if l != 0 {
        if |this| != l {
          assert this[l + 1..] == this[l..][1..];
          assert this[1..][..l - 1] == this[1..l];
          assert this[1..][..l] == this[1..l + 1];
          assert this[l..][0] == this[l];
          DefinedPrefix(l + 1, n);
          DefinedPrefix'(l, n);
          assert n >= this[..l+1].AllVarsInScope();
          assert this[..l+1].AllVarsInScope() == this[..l].AllVarsInScope() + this[l].varsInScope by {
            AllVarsInScopeSuffixSucc(l);
          }
          calc {
            this[l..].IsDefinedOn(n - this[..l].AllVarsInScope());
            { VarsInScopeLeqAll(l + 1); }
            SeqIsDefinedOn(this[l].cont, n - this[..l].AllVarsInScope()) && 
              this[l+1..].IsDefinedOn(n - this[..l].AllVarsInScope() - this[l].varsInScope);
            true;
          }
          var m := n - this[..l].AllVarsInScope();
          calc {
            this[l..].VarsDefined(m);
            SeqIsDefinedOn(this[l].cont, n - this[..l + 1].AllVarsInScope()) && 
            this[l + 1..].VarsDefined(n - this[..l + 1].AllVarsInScope());
            SeqIsDefinedOn(this[l].cont, n - this[..l + 1].AllVarsInScope());
            true;
          }
        } else {
          VarsInScopeLeqAll(|this|);
          VarsInScopeSuffix(|this|);
        }
      }
    }
  }

    lemma SizeConcat(cont1: Continuation, cont2: Continuation)
      ensures (cont1 + cont2).Size() == cont1.Size() + cont2.Size()
    {
      if cont1 == [] {
        assert cont1 + cont2 == cont2;
      } else {
        assert (cont1 + cont2)[0] == cont1[0];
        assert (cont1 + cont2)[1..] == cont1[1..] + cont2;
        SizeConcat(cont1[1..], cont2);
      }
    }

}