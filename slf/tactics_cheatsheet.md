

- `xwp` : initialize the proof by formatting the hoare triple
- `xapp` : reason about the appication of a function. This can be pointer reads/writes, assignments, etc. It may modify the precondition to reflect variable updates.
- `xapp H` : apply a lemma `H`. This is normally used to
  progress a SL triple using `H`, as to `xchange` acting as vanilla `apply` for heap entailment
- `xsimpl` : like simpl, but works on SLF proofs
- `xsimpl n m ...` : provide concrete arguments for matching. Use `__` istead of `_` for leaving holes.
- `xsimpl*` : perform `xsimpl` and then `auto` immediately
- `math` : `lia` for SLF
- `xval` : if the code returns a value, try to find the relationship between the value and the postcondition

- `induction_wf IH: R x` : perform well-founded recursion wrt `x`, assuming a well-founded relation `R` and set the induction hypothesis as `IH`

- `xif` : reason about the branches of an if statement.
- `gen` : `generalize dependent/revert` for SLF.


- `xpull` to extract pure facts and quantifiers from the LHS of `==>`.
- `xchange E` for exploiting a lemma `E` with a conclusion of the form `H1 ==> H2` or `H1 = H2`.
Assume an entailment goal of the form `H1 \* H2 \* H3 ==> H4`. Assume an entailment assumption `M`, say `H2 ==> H2'`. Then `xchange M` turns the goal into `H1 \* H2' \* H3 ==> H4`, effectively replacing `H2` with `H2'`.
- `xchange <- E` :  for exploiting an entailment `H2 ==> H1` in the case
- `xchanges*` do `xchanges` and then perform eauto. `E` is a lemma with a conclusion of the form `H1 = H2`.
- `xchanges` is a shorthand for `xchange` followed with `xsimpl`.
- `xfun` to reason about function definitions.
  `xfun (fun (g: val) => spec)` lets you define a custom spec for the function body `g` 

- `xtriple` convert a `triple () ()` into a pre-code-post format that x-tactics are admitted on.
- `introv` (a TLC tactic) like `intros` but takes as arguments only the name of the hypotheses, not of all variables.
- `rew_list` (a TLC tactic) to normalize list expressions.

- `Global Opaque X.` : tell coq that X is not possible for unfolding. This even makes manually trying `unfold X` fail.
- ``Global Transparent X.`` : undos the above command


- `hnf` : unfolds head constants

- `lets H: L x y` introduces an hypothesis named `H`, whose statement
is the specialization of the lemma `L` on the arguments `x` and `y`.
It is equivalent to `generalize (L _ _ .. _ x _ _ .. _ _ y); intros H`,
for the appropriate number of underscore symbols.
- `forwards H: L x y` is very similar to `lets`, except that it attempts
to instantiate all arguments of `L`. It is equivalent to
`generalize (L _ _ .. _ x _ _ .. _ _ y _ _ .. _ _); intros H`.
- `specializes H x y` specializes an existing hypothesis `H` in place.
It is equivalent to `lets H2: H x y; clear H; rename H2 into H`.