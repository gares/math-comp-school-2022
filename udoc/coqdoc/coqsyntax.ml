(*s Coq keywords *)

let build_table l =
  let h = Hashtbl.create 101 in
  List.iter (fun key ->Hashtbl.add h  key ()) l;
  function s -> try Hashtbl.find h s; true with Not_found -> false

let is_keyword =
  build_table
    [ "About"; "AddPath"; "Axiom"; "Abort"; "Chapter"; "Check"; "Coercion"; "Compute"; "CoFixpoint";
      "CoInductive"; "Corollary"; "Defined"; "Definition"; "End"; "Eval"; "Example";
      "Export"; "Fact"; "Fix"; "Fixpoint"; "Function"; "Generalizable"; "Global"; "Grammar";
      "Guarded"; "Goal"; "Hint"; "Debug"; "On";
      "Hypothesis"; "Hypotheses";
      "Resolve"; "Unfold"; "Immediate"; "Extern"; "Constructors"; "Rewrite";
      "Implicit"; "Import"; "Inductive";
      "Infix"; "Lemma"; "Let"; "Load"; "Local"; "Ltac";
      "Module"; "Module Type"; "Declare Module"; "Include";
      "Mutual"; "Parameter"; "Parameters"; "Print"; "Printing"; "All"; "Proof"; "Proof with"; "Qed";
      "Record"; "Recursive"; "Remark"; "Require"; "Save"; "Scheme"; "Assumptions"; "Axioms"; "Universes";
      "Induction"; "for"; "Sort"; "Section"; "Show"; "Structure"; "Syntactic"; "Syntax"; "Tactic"; "Theorem";
      "Search"; "SearchAbout"; "SearchHead"; "SearchPattern"; "SearchRewrite";
      "Set"; "Types"; "Undo"; "Unset"; "Variable"; "Variables"; "Context";
      "Notation"; "Reserved Notation"; "Tactic Notation";
      "Delimit"; "Bind"; "Open"; "Scope"; "Inline";
      "Implicit Arguments"; "Add"; "Strict";
      "Typeclasses"; "Instance"; "Global Instance"; "Class"; "Instantiation";
      "subgoal"; "subgoals"; "vm_compute";
      "Opaque"; "Transparent"; "Time";
      "Extraction"; "Extract";
      "Variant";
      (* Program *)
      "Program Definition"; "Program Example"; "Program Fixpoint"; "Program Lemma";
      "Obligation"; "Obligations"; "Solve"; "using"; "Next Obligation"; "Next";
      "Program Instance"; "Equations"; "Equations_nocomp";
      (*i (* coq terms *) *)
      "forall"; "match"; "as"; "in"; "return"; "with"; "end"; "let"; "fun";
      "if"; "then"; "else"; "Prop"; "Set"; "Type"; ":="; "where"; "struct"; "wf"; "measure";
      "fix"; "cofix";
      (* Ltac *)
      "before"; "after"; "constr"; "ltac"; "goal"; "context"; "beta"; "delta"; "iota"; "zeta"; "lazymatch";
      (* Notations *)
      "level"; "associativity"; "no"
       ]

let is_tactic =
  build_table
    [ "intro"; "intros"; "apply"; "rewrite"; "refine"; "case"; "clear"; "injection";
      "elimtype"; "progress"; "setoid_rewrite"; "left"; "right"; "constructor"; 
      "econstructor"; "decide equality"; "abstract"; "exists"; "cbv"; "simple destruct";
      "info"; "fourier"; "field"; "specialize"; "evar"; "solve"; "instanciate";
      "quote"; "eexact"; "autorewrite";
      "destruct"; "destruction"; "destruct_call"; "dependent"; "elim"; "extensionality";
      "f_equal"; "generalize"; "generalize_eqs"; "generalize_eqs_vars"; "induction"; "rename"; "move"; "omega";
      "set"; "assert"; "do"; "repeat";
      "cut"; "assumption"; "exact"; "split"; "subst"; "try"; "discriminate";
      "simpl"; "unfold"; "red"; "compute"; "at"; "in"; "by";
      "reflexivity"; "symmetry"; "transitivity";
      "replace"; "setoid_replace"; "inversion"; "inversion_clear";
      "pattern"; "intuition"; "congruence"; "fail"; "fresh";
      "trivial"; "tauto"; "firstorder"; "ring";
      "clapply"; "program_simpl"; "program_simplify"; "eapply"; "auto"; "eauto";
      "change"; "fold"; "hnf"; "lazy"; "simple"; "eexists"; "debug"; "idtac"; "first"; "type of"; "pose";
      "eval"; "instantiate"; "until" ]
