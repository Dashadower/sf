

- `xwp` : initialize the proof by formatting the hoare triple
- `xapp` : reason about the appication of a function. This can be pointer reads/writes, assignments, etc. It may modify the precondition to reflect variable updates.
- `xapp H` : apply a lemma `H`.
- `xsimpl` : like simpl, but works on SLF proofs
- `xsimpl*` : perform `xsimpl` and then `auto` immediately
- `math` : `lia` for SLF
- `xval` : if the code returns a value, try to find the relationship between the value and the postcondition

- `induction_wf IH: R x` : perform well-founded recursion wrt `x`, assuming a well-founded relation `R` and set the induction hypothesis as `IH`

- `xif` : reason about the branches of an if statement.
- `gen` : `generalize dependent/revert` for SLF.


- `xpull` to extract pure facts and quantifiers from the LHS of [==>].
- `xchange E` for exploiting a lemma `E` with a conclusion of the form `H1 ==> H2` or `H1 = H2`.
- `xchange <- E` :  for exploiting an entailment `H2 ==> H1` in the case
- `xchanges*` do `xchanges` and then perform eauto.
`E` is a lemma with a conclusion of the form [H1 = H2].
- `xchanges` is a shorthand for `xchange` followed with `xsimpl`.
- `xfun` to reason about function definitions.
- `xtriple` to establish specifications for abstract functions.
- `introv` (a TLC tactic) like `intros` but takes as arguments only the name of the hypotheses, not of all variables.
- `rew_list` (a TLC tactic) to normalize list expressions.

- `Global Opaque X.` : tell coq that X is not possible for unfolding. This even makes manually trying `unfold X` fail.
- ``Global Transparent X.`` : undos the above command