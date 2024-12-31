searchState.loadedDescShard("egg", 0, "<code>egg</code> (<strong>e</strong>-<strong>g</strong>raphs <strong>g</strong>ood) is a e-graph library optimized for …\nThe target analysis to transate into.\nArbitrary data associated with an <code>EClass</code>.\nThe righthand side of a <code>Rewrite</code>.\nA simple <code>CostFunction</code> that counts maximum AST depth.\nA simple <code>CostFunction</code> that counts total AST size.\nA <code>RewriteScheduler</code> that implements exponentional rule …\nAttempting to parse an operator into a value of type <code>L</code> …\nAn error occurred while parsing the s-expression itself, …\nA condition to check in a <code>ConditionalApplier</code>.\nA <code>Condition</code> that checks if two terms are equivalent.\nAn <code>Applier</code> that checks a <code>Condition</code> before applying.\nJustification by congruence.\nThe <code>Cost</code> type. It only requires <code>PartialOrd</code> so you can use …\nA cost function that can be used by an <code>Extractor</code>.\nThe per-<code>EClass</code> data for this analysis.\nResult of <code>Analysis::merge</code> indicating which of the inputs …\nType representing the cases of this language.\nA wrapper for an <code>EGraph</code> that can output GraphViz for …\nAn equivalence class of enodes.\nA data structure to keep track of equalities between …\nAn enode from the underlying <code>Language</code>\nThe language of <code>Pattern</code>s.\nAn empty s-expression was found. Usually this is caused by …\nContains the error value\nThe error type returned by <code>from_op</code> if its arguments do not …\nA data structure representing an explanation that two …\nExtracting a single <code>RecExpr</code> from an <code>EGraph</code>.\nFlatExplanation are the simpler, expanded representation …\nA single term in an flattened explanation. After the first …\nA trait for parsing e-nodes. This is implemented …\nA generic error for failing to parse an operator. This is …\nA list was found where an operator was expected. This is …\nA key to identify <code>EClass</code>es within an <code>EGraph</code>.\nData generated by running a <code>Runner</code> one iteration.\nCustom data to inject into the <code>Iteration</code>s recorded by a …\nThe iteration limit was hit. The data is the iteration …\nA justification for a union, either via a rule or …\nThe target language to translate into.\nTrait that defines a Language whose terms will be in the …\nA marker that defines acceptable children types for …\nTranslates <code>EGraph&lt;L, A&gt;</code> into <code>EGraph&lt;L2, A2&gt;</code>. For common …\nA cost function to be used by an <code>LpExtractor</code>.\nA structure to perform extraction using integer linear …\nA set of open expressions bound to variables.\nAn error raised when parsing a <code>MultiPattern</code>\nThe enode limit was hit. The data is the enode limit.\nContains the success value\nSome other reason to stop.\nA pattern that can function as either a <code>Searcher</code> or <code>Applier</code>…\nOne of the clauses in the multipattern wasn’t of the …\nA <code>RecExpr</code> that represents a <code>Pattern</code>.\nOne of the patterns in the multipattern failed to parse.\nA recursive expression from a user-defined <code>Language</code>.\nAn error type for failures when attempting to parse an …\nA report containing data about an entire <code>Runner</code> run.\nA rewrite that searches for the lefthand side and applies …\nA way to customize how a <code>Runner</code> runs <code>Rewrite</code>s.\nJustification by a rule with this name.\nFaciliates running rewrites over an <code>EGraph</code>.\nDescribes the limits that would stop a <code>Runner</code>.\nType alias for the result of a <code>Runner</code>.\nThe egraph saturated, i.e., there was an iteration where we\nThe result of searching a <code>Searcher</code> over one eclass.\nThe lefthand side of a <code>Rewrite</code>.\nAn implementation of <code>LanguageMapper</code> that can convert an …\nA very simple <code>RewriteScheduler</code> that runs every rewrite …\nError returned by <code>Runner</code> when it stops.\nA substitution mapping <code>Var</code>s to eclass <code>Id</code>s.\nAn interned string.\nA simple language used for testing.\nThe time limit was hit. The data is the time limit in …\nExplanation trees are the compact representation showing …\nAn explanation for a term and its equivalent children. …\nA vector of equalities based on enode ids. Each entry …\nA variable for use in <code>Pattern</code>s or <code>Subst</code>s.\nA pattern variable\nOne of the variables failed to parse.\nAdds an enode to the <code>EGraph</code>.\nAdds a given enode to this <code>RecExpr</code>. The enode’s children …\nAdds a <code>RecExpr</code> to the <code>EGraph</code>, returning the id of the …\nSimilar to <code>add_expr</code> but the <code>Id</code> returned may not be …\nAdds a <code>Pattern</code> and a substitution to the <code>EGraph</code>, returning …\nSimilar to <code>add</code> but the <code>Id</code> returned may not be canonical\nReturns true if the predicate is true on all children. …\nReturns true if the predicate is true on all children. …\nWhether or not e-matching should allow finding cycles.\nWhether or not e-matching should allow finding cycles.\nReturns a new <code>PatternAst</code> with the variables renames …\nReturns a new <code>PatternAst</code> with the variables renames …\nThe <code>Analysis</code> given when creating this <code>EGraph</code>.\nReturns true if the predicate is true on any children. …\nReturns true if the predicate is true on any children. …\nA map from rule name to number of times it was <em>newly</em> …\nThe applier (right-hand side) of the rewrite.\nThe inner <code>Applier</code> to call once <code>condition</code> passes.\nCall <code>apply_matches</code> on the <code>Applier</code>.\nApply many substitutions.\nApply many substitutions.\nApply a single substitution.\nA hook allowing you to customize rewrite application …\nA hook allowing you to customize rewrite application …\nSeconds spent applying rules in this iteration.\nCheck if explanations are enabled.\nReturns a mutable slice of the children <code>Id</code>s.\nReturns a slice of the children <code>Id</code>s.\nConvert this symbol into the string in the static, global …\nIf this variable was created from a u32, get it back out.\nAsserts that the childless enodes in this eclass are …\nThe actual pattern as a <code>RecExpr</code>\nOptionally, an ast for the matches used in proof …\nA rule rewriting this TreeTerm’s initial term back to …\nA rule rewriting this FlatTerm back to the last FlatTerm.\nBuild a <code>RecExpr</code> from an e-node.\nBuild a <code>RecExpr</code> from an e-node.\nChecks if n is an acceptable number of children for this …\nWhether or not the <code>Runner</code> is allowed to say it has …\nWhether or not the <code>Runner</code> is allowed to say it has …\nCheck a condition.\nPanic if the given eclass doesn’t contain the given …\nCheck if the <code>Runner</code> should stop based on the limits.\nCheck the validity of the explanation with respect to the …\nA list of child proofs, each transforming the initial term …\nReturns the children of this e-node.\nThe children of this FlatTerm.\nThe enode’s children <code>Id</code>s\nReturns a mutable slice of the children of this e-node.\nReturns an iterator over the eclasses in the egraph.\nReturns an iterator over the eclasses that contain a given …\nReturns an mutating iterator over the eclasses in the …\nWhether or not reading operation are allowed on this …\nThe <code>Condition</code> to <code>check</code> before calling <code>apply_one</code> on <code>applier</code>.\nA list of strings to be output top part of the dot file.\nMake a copy of the egraph with the same nodes, but no …\nCalculates the cost of an enode whose children are <code>Cost</code>s.\nCalculates the total cost of a <code>RecExpr</code>.\nCalculates the total cost of a <code>RecExpr</code>.\nThe analysis data associated with this eclass.\nThe user provided annotation for this iteration\nA macro to easily create a <code>Language</code>.\nReturn the <code>Discriminant</code> of this node.\nNever ban a particular rule.\nCreates a <code>Dot</code> to visualize this egraph. See <code>Dot</code>.\nReturns a more debug-able representation of the egraph.\nThe eclass id that these matches were found in.\nThe <code>EGraph</code> used.\nThe number of eclasses in the egraph at the start of this …\nA intersection algorithm between two egraphs. The …\nThe number of enodes in the egraph at the start of this …\nPerforms the union between two egraphs.\nChecks whether two <code>RecExpr</code>s are equivalent. Returns a list …\nCalls <code>EGraph::explain_equivalence</code>.\nWhen explanations are enabled, this function produces an …\nEquivalent to calling <code>explain_equivalence</code><code>(</code><code>id_to_expr</code><code>(left),</code>\nGet an explanation for why an expression matches a pattern.\nGet an explanation for why an expression matches a pattern.\nThe tree representation of the explanation.\nCanonicalizes an eclass id.\nFind the cheapest (lowest cost) represented <code>RecExpr</code> in the …\nFind the cost of the term that would be extracted from …\nFind the cheapest e-node in the given e-class.\nConstruct the <code>FlatExplanation</code> for this TreeTerm.\nFolds over the children, given an initial accumulator.\nFolds over the children, given an initial accumulator.\nRuns a given function on each child <code>Id</code>.\nRuns a given function on each child <code>Id</code>.\nRun some function on each matching e-node in this class.\nRuns a given function on each child <code>Id</code>, allowing mutation …\nRuns a given function on each child <code>Id</code>, allowing mutation …\nA rule rewriting the last TreeTerm’s final term to this …\nA rule rewriting the last FlatTerm to this FlatTerm.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nParse an e-node with operator <code>op</code> and children <code>children</code>.\nCreate a new variable from a u32.\nCreate an instance of this type from a <code>Vec&lt;Id&gt;</code>, with the …\nRetrieve a <code>Var</code>, returning <code>None</code> if not present.\nGet the number of nodes in the egraph used for …\nGet each flattened term in the explanation as an …\nGet each term in the explanation as a string. See …\nGet a FlatTerm representing the first term in this proof.\nGet a FlatTerm representing the final term in this proof.\nGet the number of congruences between nodes in the egraph. …\nFor patterns, return the ast directly as a reference\nFor patterns, return the ast directly as a reference\nFor patterns, get the ast directly as a reference.\nFor patterns, get the ast directly as a reference.\nConvert this FlatTerm to a RecExpr.\nGet each the tree-style explanation as an s-expression …\nConvert this FlatTerm to an S-expression. See …\nGet the tree-style explanation as an s-expression string …\nGet the size of this explanation tree in terms of the …\nGet all the unions ever found in the egraph in terms of …\nChecks if this term or any child has a <code>backward_rule</code>.\nChecks if this term or any child has a <code>forward_rule</code>.\nSeconds spent running hooks.\nThe hooks added by the <code>with_hook</code> method, in insertion …\nThis eclass’s id.\nPick a representative term for a given Id.\nLike <code>id_to_expr</code> but only goes one layer deep\nLike <code>id_to_expr</code>, but creates a pattern instead of a term. …\nReturns an iterator over the <code>Id</code>s in this expression.\nInsert something, returning the old <code>Id</code> if present.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nChecks if this expr is a DAG, i.e. doesn’t have any back …\nChecks if there are no children.\nChecks if there are no children.\nReturns <code>true</code> if the <code>eclass</code> is empty.\nReturns <code>true</code> if the egraph is empty\nReturns true if this enode has no children.\nReturns true if this enode has no children.\nReturns an iterator over the <code>Id</code>s and enodes of this …\nReturns an iterator over the <code>Id</code>s and enodes of this …\nIterates over the enodes in this eclass.\nData accumulated over each <code>Iteration</code>.\nThe number of iterations this runner performed.\nMake a <code>RecExpr</code> by mapping this enodes children to other …\nMake a <code>RecExpr</code> by mapping this enodes children to other …\nCreate childless enode with the given string\nIterates over the childless enodes in this eclass.\nReturns the number of children.\nReturns the number of the children this enode has.\nReturns the number of the children this enode has.\nReturns the number of enodes in this eclass.\nLookup the eclass of the given enode.\nLookup the eclass of the given <code>RecExpr</code>.\nLookup the eclasses of all the nodes in the given <code>RecExpr</code>.\nMakes a new <code>Analysis</code> data for a given e-node.\nGiven the current <code>Runner</code>, make the data to be put in this …\nConstruct the flat representation of the explanation and …\nTranslate an analysis of type <code>A</code> into an analysis of <code>A2</code>.\nCreates a new enode with children determined by the given …\nCreates a new enode with children determined by the given …\nTranslate <code>A::Data</code> into <code>A2::Data</code>.\nTranslate <code>L::Discriminant</code> into <code>L2::Discriminant</code>\nTranslate an <code>EClass</code> over <code>L</code> into an <code>EClass</code> over <code>L2</code>.\nTranslate an <code>EClass</code> over <code>L</code> into an <code>EClass</code> over <code>L2</code>.\nMap an <code>EGraph</code> over <code>L</code> into an <code>EGraph</code> over <code>L2</code>.\nMap an <code>EGraph</code> over <code>L</code> into an <code>EGraph</code> over <code>L2</code>.\nTranslate a node of <code>L</code> into a node of <code>L2</code>.\nReturns true if this enode matches another enode. This …\nDefines how to merge two <code>Data</code>s when their containing <code>EClass</code>…\nA utility for implementing <code>Analysis::merge</code> when the <code>Data</code> …\nA utility for implementing <code>Analysis::merge</code> when the <code>Data</code> …\nA utility for implementing <code>Analysis::merge</code> when the <code>Data</code> …\nA hook that allows the modification of the <code>EGraph</code>.\nA hook that allows the modification of the <code>EGraph</code>.\nA macro to easily make <code>Rewrite</code>s using <code>MultiPattern</code>s.\nReturns the number of matches in the e-graph\nReturns the number of matches in the e-graph\nThe number of rebuild iterations done after this iteration …\nThe name of the rewrite.\nIntern a string into the global symbol table.\nConstruct a new explanation given its tree representation.\nCreate an <code>LpExtractor</code> using costs from the given …\nCreate a new <code>Runner</code> with the given analysis and default …\nCreates a new, empty <code>EGraph</code> with the given <code>Analysis</code>\nConstruct a new TreeTerm given its node and child_proofs.\nConstruct a new FlatTerm given a node and its children.\nCreate a new <code>Extractor</code> given an <code>EGraph</code> and a <code>CostFunction</code>.\nCreate a new <code>FromOpError</code> representing a failed call …\nCreate an enode with the given string and children\nCreates a new multipattern, binding the given patterns to …\nCreates a new pattern from the given pattern ast.\nCreate a new <code>Rewrite</code>. You typically want to use the …\nCreate a new <code>ConditionEqual</code> condition given two patterns.\nA node representing this TreeTerm’s operator. The …\nThe node representing this FlatTerm’s operator. The …\nReturns the cost of the given e-node.\nExposes the actual nodes in the egraph.\nThe equivalent enodes in this equivalence class.\nReturns the number of eclasses in the egraph.\nThe operator for an enode\nIterates over the non-canonical ids of parent enodes of …\nCreate a ConditionEqual by parsing two pattern strings.\nAn optional hook that allows inspection before a <code>union</code> …\nAn optional hook that allows inspection before a <code>union</code> …\nPretty print with a maximum line length.\nPretty print this pattern as a sexp with the given width\nPrints some information about a runners run.\nRestores the egraph invariants of congruence and enode …\nSeconds spent <code>rebuild</code>ing the egraph in this iteration.\nRemove the rewrite annotation from this flatterm, if any.\nCreates a <code>Report</code> summarizing this <code>Runner</code>s run.\nRewrite the FlatTerm by matching the lhs and substituting …\nA macro to easily make <code>Rewrite</code>s.\nGet the root node of this expression. When adding a new …\nThe roots of expressions added by the <code>with_expr</code> method, in …\nSet the initial ban length for a rule.\nSet the initial match limit for a rule.\nInvokes some program with the given arguments, piping this …\nRun this <code>Runner</code> until it stops. After this, the field …\nInvokes <code>dot</code> with the given arguments, piping this formatted\nSearch the whole <code>EGraph</code>, returning a list of all the …\nSearch the whole <code>EGraph</code>, returning a list of all the …\nCall <code>search</code> on the <code>Searcher</code>.\nSearch one eclass, returning None if no matches can be …\nSearch one eclass, returning None if no matches can be …\nSimilar to <code>search_eclass</code>, but return at most <code>limit</code> many …\nA hook allowing you to customize rewrite searching …\nA hook allowing you to customize rewrite searching …\nA hook allowing you to customize rewrite searching behavior\nA hook allowing you to customize rewrite searching behavior\nSeconds spent searching in this iteration.\nSimilar to <code>search</code>, but return at most <code>limit</code> many matches.\nSimilar to <code>search</code>, but return at most <code>limit</code> many matches.\nCall <code>search_with_limit</code> on the <code>Searcher</code>.\nThe searcher (left-hand side) of the rewrite.\nUpdate the analysis data of an e-class.\nExtract a single rooted term.\nExtract (potentially multiple) roots\nWhy the <code>Runner</code> stopped. This will be <code>None</code> if it hasn’t …\nIf the runner stopped on this iterations, this is the …\nThe substitutions for each match.\nUtility to make a test proving expressions equivalent\nSet the cbc timeout in seconds.\nWrites the <code>Dot</code> to a .dot file with the given filename. …\nRenders the <code>Dot</code> to a .pdf file with the given filename. …\nRenders the <code>Dot</code> to a .png file with the given filename. …\nRenders the <code>Dot</code> to a .svg file with the given filename. …\nIterates over the classes, returning the total number of …\nReturns the number of enodes in the <code>EGraph</code>.\nTotal time spent in this iteration, including data …\nSame as <code>Language::build_recexpr</code>, but fallible.\nSame as <code>Language::build_recexpr</code>, but fallible.\nRuns a falliable function on each child, stopping if the …\nRuns a falliable function on each child, stopping if the …\nA Guide-level Explanation of <code>egg</code>\nUnions two eclasses given their ids.\nGiven two patterns and a substitution, add the patterns …\nUnions two e-classes, using a given reason to justify it.\nRuns a given function to replace the children.\nRuns a given function to replace the children.\nWhether or not to anchor the edges in the output. True by …\nReturns a list of the variables bound by this Searcher\nReturns a list of variables that this Applier assumes are …\nReturns a list of variables that this Applier assumes are …\nReturns a list of variables that this Condition assumes …\nReturns a list of variables that this Condition assumes …\nReturns a list of the <code>Var</code>s in this pattern.\nSet whether or not to anchor the edges in the output.\nSet the initial ban length. Default: 5 iterations\nCreate a <code>Subst</code> with the given initial capacity\nAdds a line to the dot output. Indentation and a newline …\nReplace the <code>EGraph</code> of this <code>Runner</code>.\nBy default, egg runs a greedy algorithm to reduce the size …\nBy default, egg runs a greedy algorithm to reduce the size …\nDisable explanations for this runner’s egraph.\nDisable explanations for this <code>EGraph</code>.\nEnable explanations for this runner’s egraph. This …\nEnable explanations for this <code>EGraph</code>. This allows the …\nAdd an expression to the egraph to be run.\nAdd a hook to instrument or modify the behavior of a <code>Runner</code>…\nSet the initial match limit after which a rule will be …\nSets the iteration limit. Default: 30\nSets the egraph size limit (in enodes). Default: 10,000\nChange out the <code>RewriteScheduler</code> used by this <code>Runner</code>. The …\nSets the runner time limit. Default: 5 seconds\nBy default, egg runs a greedy algorithm to reduce the size …\nBy default, egg runs a greedy algorithm to reduce the size …\nConcepts: e-graphs and equality saturation\nMy first <code>egg</code> 🐣\nExplanations")