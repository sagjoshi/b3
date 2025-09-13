// This module defines two predicates that are used during resolution:
//     * NameAlignment
//     * LinearForm
// along with some useful lemmas about these.

module NamesAndLinearForms {
  import Ast

  export
    reveals NameAlignment, LinearForm
    provides LinearFormValues, LinearFormL2R, LinearFormR2L, NewNamePreservesLinearForm
    provides DistinctConcat
    provides Ast

  ghost predicate NameAlignment(xMap: map<string, Ast.NamedDecl>) {
    forall name <- xMap :: xMap[name].Name == name
  }

  ghost predicate LinearForm<X>(xMap: map<string, X>, xs: seq<X>) {
    (set name <- xMap :: xMap[name]) == set x <- xs
  }

  lemma LinearFormValues<X>(xMap: map<string, X>, xs: seq<X>)
    requires LinearForm(xMap, xs)
    ensures xMap.Values == set x <- xs
  {
  }

  lemma LinearFormL2R<X>(name: string, xMap: map<string, X>, xs: seq<X>)
    requires LinearForm(xMap, xs) && name in xMap
    ensures xMap[name] in xs
  {
    var lhs := set name <- xMap :: xMap[name];
    var rhs := set x <- xs;
    assert xMap[name] in lhs;
    assert xMap[name] in rhs;
  }

  lemma LinearFormR2L<X>(x: X, xMap: map<string, X>, xs: seq<X>) returns (name: string)
    requires LinearForm(xMap, xs) && x in xs
    ensures name in xMap && xMap[name] == x
  {
    var lhs := set name <- xMap :: xMap[name];
    var rhs := set x <- xs;
    assert x in rhs;
    assert x in lhs;
    name :| name in xMap && xMap[name] == x;
  }

  lemma NewNamePreservesLinearForm(name: string, decl: Ast.NamedDecl, xMap: map<string, Ast.NamedDecl>, xs: seq<Ast.NamedDecl>)
    requires NameAlignment(xMap)
    requires LinearForm(xMap, xs)
    requires name !in xMap
    requires decl.Name == name
    ensures forall i :: 0 <= i < |xs| ==> xs[i].Name != name
    ensures LinearForm(xMap[name := decl], xs + [decl])
  {
    forall i | 0 <= i < |xs|
      ensures xs[i].Name != name
    {
      // From the definition of LinearForm:
      var lhs := set xName <- xMap :: xMap[xName];
      var rhs := set x <- xs;
      assert lhs == rhs; // by LinearForm(xMap, xs)

      var x := xs[i];
      assert x in xs;
      assert x in rhs;
      assert x in lhs;
      var xName :| xName in xMap && xMap[xName] == x;
      assert xMap[xName].Name == xName;
      assert xName != name; // since "xName in xMap" and "name !in xMap"
    }

    var xMap', xs' := xMap[name := decl], xs + [decl];
    var n := |xs|;
    calc {
      (set xName <- xMap' :: xMap'[xName]);
      (set xName <- xMap :: xMap'[xName]) + {xMap'[name]};
      { assert name !in xMap; }
      (set xName <- xMap :: xMap[xName]) + {decl};
      { assert LinearForm(xMap, xs); }
      (set x <- xs) + {decl};
      { assert xs == xs'[..n] && xs'[n] == decl; }
      (set x <- xs'[..n]) + {xs'[n]};
      (set x <- xs');
    }
  }

  lemma DistinctConcat(xMap: map<string, Ast.NamedDecl>, xs: seq<Ast.NamedDecl>, yMap: map<string, Ast.NamedDecl>, ys: seq<Ast.NamedDecl>)
    requires LinearForm(xMap, xs) && LinearForm(yMap, ys)
    requires NameAlignment(xMap) && NameAlignment(yMap)
    requires xMap.Keys !! yMap.Keys
    requires Ast.NamedDecl.Distinct(xs) && Ast.NamedDecl.Distinct(ys)
    ensures Ast.NamedDecl.Distinct(xs + ys)
  {
    var decls := xs + ys;
    forall i, j | 0 <= i < j < |decls|
      ensures decls[i].Name != decls[j].Name
    {
      var n := |xs|;
      assert decls[..n] == xs && decls[n..] == ys;
      if j < n {
        assert decls[i] in xs && decls[j] in xs;
      } else if n <= i {
        assert decls[i] in ys && decls[j] in ys;
      } else {
        assert decls[i].Name in xMap by {
          var name := LinearFormR2L(decls[i], xMap, xs);
          assert xMap[name].Name == name; // by NameAlignment
        }
        assert decls[j].Name in yMap by {
          var name := LinearFormR2L(decls[j], yMap, ys);
          assert yMap[name].Name == name; // by NameAlignment
        }
      }
    }
  }
}