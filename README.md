# TT Semantics

Various experiments in computer-oriented natural language semantics.
They comprise attempts to formalize various language phenomena in computer
languages such as Agda, Coq, Racket — in any case along the lines of
type-theoretical semantics (A.Ranta, Z.Luo, and others).

## Agda

* [`MontagueTT`](Agda/MontagueTT/) — Montague-like
  type-theoretical natural language semantics.
* [`Contexts`](Agda/Contexts) — Contexts in natural language semantics. Records and modules.
* [`IntensionalLogic`](Agda/IntensionalLogic) — Monads in intensional logic.
* [`FuzzyTT`](Agda/FuzzyTT/) — A variant of P.Martin-Löf ’s intuitionistic type theory with
  fuzzy type membership.
* [`Experiments`](Agda/Experiments/) — Various experiments.

## Coq

* `Edelberg.v` — `Coq` formalization of illustrative cases from
  'W.Edelberg, A Perspectivalist Semantics for the Attitudes (1995)'.
* `Edelberg-counterpart.v` — `Coq` formalization of illustrative cases from
  'W.Edelberg, A Perspectivalist Semantics for the Attitudes (1995)'
  using Counterpart relation.
* `Ralph.v` — `Coq` formalization of Quine's sentence 'Ralph belives
  that someone is a spy' using `Record` types.
* `Ralph-counterpart.v` — `Coq` formalization of Quine's sentence
  'Ralph belives that someone is a spy' using `Record` types and
  Counterpart relation.
* `Ralph-classes.v` — `Coq` formalization of Quine's sentence 'Ralph
  belives that someone is a spy' using `typeclasses`.  Simple try, in
  fact contradictory.
