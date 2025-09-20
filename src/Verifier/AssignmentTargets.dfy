module AssignmentTargets {
  import Ast
  import opened Basics

  export
    provides Compute
    provides Ast

  function Compute(stmt: Ast.Stmt): (targets: seq<Ast.Variable>) {
    var StmtInformation(targets, vv, cc) := StmtTargets(stmt);
    if Normal in cc then Prune(targets, vv) else []
  }

  type Target = Ast.Variable

  datatype StmtInformation = StmtInformation(targets: seq<Target>, targetSet: set<Target>, cpoints: set<ContinuationPoint>)
  {
    static const EmptyNormal := StmtInformation([], {}, {Normal})

    ghost predicate Valid() {
      forall target <- targetSet :: target in targets
    }

    function Add(v: Target): (info: StmtInformation)
      requires Valid()
      ensures info.Valid()
    {
      if v in targetSet then
        this
      else
        StmtInformation(targets + [v], targetSet + {v}, cpoints)
    }

    function Remove(v: Target): (info: StmtInformation)
      requires Valid()
      ensures info.Valid()
    {
      // v stays in the sequence (it is later pruned away by Compute)
      StmtInformation(targets, targetSet - {v}, cpoints)
    }

    function AddOutgoingArguments(args: seq<Ast.CallArgument>): (info: StmtInformation)
      requires Valid()
      ensures info.Valid()
      decreases args
    {
      if args == [] then
        this
      else if args[0].OutgoingArgument? then
        Add(args[0].v).AddOutgoingArguments(args[1..])
      else
        AddOutgoingArguments(args[1..])
    }
  }

  datatype ContinuationPoint =
    | Normal
    | Abrupt(lbl: Ast.Label)

  // Return the set of free variables that are syntactically assigned anywhere in `stmt`,
  // except in those places where control flow is syntactically impossible.
  // To accomplish the latter, the function also returns the set of possible continuation
  // points of `stmt`.
  function StmtTargets(stmt: Ast.Stmt): (info: StmtInformation)
    ensures info.Valid()
  {
    match stmt
    case VarDecl(v, _, body) =>
      var info := StmtTargets(body);
      info.Remove(v)
    case Assign(lhs, _) =>
      StmtInformation([lhs], {lhs}, {Normal})
    case Block(stmts) =>
      BlockTargets(stmts)
    case Call(_, args) =>
      StmtInformation.EmptyNormal.AddOutgoingArguments(args)
    case Check(_) => StmtInformation.EmptyNormal
    case Assume(_) => StmtInformation.EmptyNormal
    case Assert(_) => StmtInformation.EmptyNormal
    case AForall(_, _) => StmtInformation.EmptyNormal
    case Choose(branches) =>
      ChooseTargets(branches)
    case Loop(_, body) =>
      var info := StmtTargets(body);
      info.(cpoints := info.cpoints - {Normal})
    case LabeledStmt(lbl, body) =>
      var info := StmtTargets(body);
      if Abrupt(lbl) in info.cpoints then
        info.(cpoints := info.cpoints - {Abrupt(lbl)} + {Normal})
      else
        info
    case Exit(lbl) =>
      StmtInformation([], {}, {Abrupt(lbl)})
    case Probe(_) => StmtInformation.EmptyNormal
  }

  function BlockTargets(stmts: seq<Ast.Stmt>): (info: StmtInformation)
    ensures info.Valid()
  {
    if stmts == [] then
      StmtInformation.EmptyNormal
    else
      var info := StmtTargets(stmts[0]);
      if Normal in info.cpoints then
        var info' := BlockTargets(stmts[1..]);
        StmtInformation(
          info.targets + info'.targets,
          info.targetSet + info'.targetSet,
          info.cpoints - {Normal} + info'.cpoints)
      else
        info
  }

  function ChooseTargets(stmts: seq<Ast.Stmt>): (info: StmtInformation)
    ensures info.Valid()
  {
    if stmts == [] then
      StmtInformation([], {}, {})
    else
      var info := StmtTargets(stmts[0]);
      var info' := ChooseTargets(stmts[1..]);
      StmtInformation(
        info.targets + info'.targets,
        info.targetSet + info'.targetSet,
        info.cpoints + info'.cpoints)
  }
}