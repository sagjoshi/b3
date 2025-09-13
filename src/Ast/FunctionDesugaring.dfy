// This module is responsible for
//   * turning injective function parameters into inverse functions and their corresponding axioms
//   * creating a tag constant (nullary function) for every tagged function, along with its definition axiom
//   * declaring a tag axiom for each tagged function
//   * turning each function definition (body) into an axiom

module FunctionDesugaring {
  import opened Ast
  import opened Std.Wrappers
  import opened Basics
  import Raw = RawAst

  export
    provides CreateInverseAndTagFunctions, DefinitionAxiom
    reveals ValidFunctionsAndAxioms
    provides Ast, Wrappers

  ghost predicate ValidFunctionsAndAxioms(functions: seq<Function>, axioms: seq<Axiom>)
    reads functions
  {
    && (forall func <- functions :: func.WellFormed())
    && (forall axiom <- axioms :: axiom.WellFormed())
  }

  method CreateInverseAndTagFunctions(func: Function) returns (functions: seq<Function>, axioms: seq<Axiom>)
    requires forall i, j :: 0 <= i < j < |func.Parameters| ==> func.Parameters[i].name != func.Parameters[j].name
    requires func.Tag.Some? ==> var tagger := func.Tag.value; |tagger.Parameters| == 1 && tagger.Parameters[0].typ == func.ResultType
    modifies func`ExplainedBy
    ensures ValidFunctionsAndAxioms(functions, axioms)
    ensures fresh(functions) && fresh(axioms)
  {
    functions, axioms := CreateInverseFunctions(func);
    if func.Tag.Some? {
      var ff, aa := CreateFunctionTag(func);
      functions := functions + ff;
      axioms := axioms + aa;
    }
  }


  method CreateInverseFunctions(func: Function) returns (functions: seq<Function>, axioms: seq<Axiom>)
    requires forall i, j :: 0 <= i < j < |func.Parameters| ==> func.Parameters[i].name != func.Parameters[j].name
    modifies func`ExplainedBy
    ensures ValidFunctionsAndAxioms(functions, axioms)
    ensures fresh(functions) && fresh(axioms)
  {
    functions, axioms := [], [];

    for j := 0 to |func.Parameters|
      invariant forall f <- functions :: exists i :: 0 <= i < j && f.Name == CombineNames(func.Name, func.Parameters[i].name)
      invariant ValidFunctionsAndAxioms(functions, axioms)
      invariant fresh(functions) && fresh(axioms)
    {
      var param := func.Parameters[j];
      if param.injective {
        var name := CombineNames(func.Name, param.name);
        forall f <- functions
          ensures f.Name != name
        {
          var i :| 0 <= i < j && f.Name == CombineNames(func.Name, func.Parameters[i].name);
          var prefixLen := |func.Name| + 1;
          assert f.Name[prefixLen..] == func.Parameters[i].name != func.Parameters[j].name == name[prefixLen..];
        }

        Raw.SurelyLegalVariableName("subject");
        var parameter := new FParameter("subject", false, func.ResultType);
        var inverseFunction := new Function(name, [parameter], param.typ, None);
        assert inverseFunction.WellFormed();

        functions := functions + [inverseFunction];

        // injectivity axiom:
        //
        // axiom explains F
        //   forall x: X, y: Y pattern F(x, y)
        //     F.x(F(x, y)) == x
        var boundVars, pattern, lhs := GenerateAxiomPieces(func, Some(inverseFunction), false);
        var rhs := IdExpr(boundVars[j]);
        var axiom := AssembleAxiom(func, boundVars, pattern, None, lhs, rhs);
        assert axiom.WellFormed();
        axioms := axioms + [axiom];
      }
    }
  }

  method CreateFunctionTag(func: Function) returns (functions: seq<Function>, axioms: seq<Axiom>)
    requires func.Tag.Some? && var tagger := func.Tag.value; |tagger.Parameters| == 1 && tagger.Parameters[0].typ == func.ResultType
    modifies func`ExplainedBy
    ensures ValidFunctionsAndAxioms(functions, axioms)
    ensures fresh(functions) && fresh(axioms)
  {
    functions, axioms := [], [];

    var name := CombineNames(func.Name, "tag");

    // function F.tag(): tag { %tag }
    var Ftag := new Function(name, [], TagType, None);
    Ftag.Definition := Some(FunctionDefinition([], CustomLiteral("%tag", TagType)));
    functions := functions + [Ftag];

    // tag declarations, here shown for function F(x: X, y: Y): S tag G
    // axiom explains F
    //   forall x: X, y: Y pattern F(x, y)
    //     G(F(x, y)) == F.tag()
    var boundVars, pattern, lhs := GenerateAxiomPieces(func, Some(func.Tag.value), false);
    var rhs := FunctionCallExpr(Ftag, []);
    var axiom := AssembleAxiom(func, boundVars, pattern, None, lhs, rhs);
    axioms := axioms + [axiom];
  }

  // Given "func" as "function F(x: X, y: Y): S when W { Body }", generate
  //
  //     axiom explains F
  //       forall x: X, y: Y
  //         pattern F(x, y)
  //         W ==>
  //         F(x, y) == Body
  //
  // and add this axiom to func.ExplainedBy.
  method DefinitionAxiom(func: Function) returns (axiom: Axiom)
    requires func.WellFormed() && func.Definition.Some?
    modifies func`ExplainedBy
    ensures axiom.WellFormed()
    ensures fresh(axiom)
  {
    var def := func.Definition.value;

    var boundVars, pattern, lhs := GenerateAxiomPieces(func, None, true);
    var antecedent: Option<Expr> := None;
    for i := 0 to |def.when|
      invariant antecedent.Some? ==> antecedent.value.WellFormed()
    {
      var when := def.when[i];
      antecedent := Some(
        match antecedent
        case None => when
        case Some(a) => OperatorExpr(Operator.LogicalAnd, [a, when]));
    }
    axiom := AssembleAxiom(func, boundVars, pattern, antecedent, lhs, def.body);
  }

  // Given "func" as "function F(x: X, y: Y): S", generate
  //     * boundVars -- a list of fresh bound variables:  x: X, y: Y
  //     * pattern -- pattern F(x, y)
  //     * lhs -- wrapper(F(x, y))
  method GenerateAxiomPieces(func: Function, wrapper: Option<Function>, useFunctionParametersAsBoundVars: bool) returns (boundVars: seq<Variable>, pattern: Pattern, lhs: Expr)
    requires wrapper.Some? ==> |wrapper.value.Parameters| == 1
    ensures |boundVars| == |func.Parameters| && pattern.WellFormed() && lhs.WellFormed()
  {
    if useFunctionParametersAsBoundVars {
      boundVars := func.Parameters;
    } else {
      boundVars := [];
      for n := 0 to |func.Parameters|
        invariant |boundVars| == n
      {
        var param := func.Parameters[n];
        var v := new LocalVariable(param.name, false, param.typ);
        boundVars := boundVars + [v];
      }
    }

    var Fxy := FunctionCallExpr(func, SeqMap(boundVars, (v: Variable) => IdExpr(v)));
    pattern := Pattern([Fxy]);
    if wrapper == None {
      lhs := Fxy;
    } else {
      lhs := FunctionCallExpr(wrapper.value, [Fxy]);
    }
  }

  // Generate:
  //
  //     axiom explains func
  //       forall boundVars
  //         pattern
  //         antecedent ==>
  //         lhs == rhs
  //
  // and add this axiom to func.ExplainedBy.
  method AssembleAxiom(func: Function, boundVars: seq<Variable>, pattern: Pattern, antecedent: Option<Expr>, lhs: Expr, rhs: Expr) returns (axiom: Axiom)
    requires pattern.WellFormed()
    requires antecedent.Some? ==> antecedent.value.WellFormed()
    requires lhs.WellFormed() && rhs.WellFormed()
    modifies func`ExplainedBy
    ensures fresh(axiom) && axiom.WellFormed()
  {
    var body := OperatorExpr(Operator.Eq, [lhs, rhs]);
    if antecedent.Some? {
      body := OperatorExpr(Operator.LogicalImp, [antecedent.value, body]);
    }
    var q;
    if |boundVars| == 0 {
      q := body;
    } else {
      q := QuantifierExpr(true, boundVars, [pattern], body);
    }

    axiom := new Axiom([func], q);
    func.ExplainedBy := func.ExplainedBy + [axiom];
  }

  function CombineNames(base: string, member: string): string {
    base + "." + member
  }
}