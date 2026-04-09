# ShotUn

**ShotUn** adapts the higher-order unification algorithm developed in the
library [_HOL_](https://hexdocs.pm/hol/readme.html) to the data structures and
semantics of [_ShotDs_](https://hexdocs.pm/shot_ds/readme.html).

This package was developed at the
[University of Bamberg](https://www.uni-bamberg.de/en/) with the
[Chair for AI Systems Engineering](https://www.uni-bamberg.de/en/aise/).

## Higher-order Unification

Higher-order unification is the task of determining the common instances of two
given higher-order terms, i.e., a complete set of unifiers (substitutions) that
represent solutions to the given unification problem. However,
[Goldfarb (1981)](https://doi.org/10.1016/0304-3975(81)90040-2) has shown that
unification is already undecidable for second-order logic.

### Unification Problems

Generally, there are three configurations of unification problems for two given
higher-order terms:

- _rigid-rigid_: The head symbols of both terms are constant.
- _flex-rigid_: One head symbol is variable, the other constant.
- _flex-flex_: The head symbols of both terms are variable.

### Pre-unification

Higher-order pre-unification
[(Huet, 1975)](https://doi.org/10.1016/0304-3975(75)90011-0) describes a
semi-decision procedure for this problem by not unifying _flex-flex_ pairs and
instead returning them as constraints (there are infinitely many common
instances). The semi-decidability stems from _flex-rigid_ pairs. Certain
terms might require a very complex composition of _imitation_ and
_projection_ bindings, while for others we might only be certain no solution
exists after exhausting this infinite search space. Without a depth bound, there
is hence no termination guarantee.

### Imitation and Projection Bindings

When the algorithm encounters a _flex-rigid_ equation, it takes the form:

$$F(s_1, \dots, s_n) \overset{?}{=} h(t_1, \dots, t_m)$$

where $F$ is a free variable with arity $n$ (the flexible head) and $h$ is a
constant or bound variable of arity $m$ (the rigid head).

To solve this, the algorithm must generate a partial substitution for $F$ of the
form $\lambda X_1 \dots X_n. e / F$, where $e$ is an expression that constructs
the required output. We branch the search space into two specific strategies:

In imitation, we guess that the flexible variable $F$ directly produces the
rigid head $h$. We substitute $F$ with a $\lambda$-abstraction that explicitly
calls $h$, passing fesh variables $H_1 \dots H_m$ to represent the unknown
arguments that $h$ will need. Note that imitation is only valid if $h$ is a
constant, not a bound variable. Otherwise, we could have a variable capture
error.

In projection, we guess that the flexible variable $F$ doesn't construct $h$
itself, but rather relies on one of its own arguments $s_i$ to eventually
produce the required structure. We substitute $F$ with a $\lambda$-abstraction
that returns its $i$-th argument. If $s_i$ is itself a function taking $k$
arguments, we must supply it with fresh variables. The algorithm will branch and
attempt projection for every argument $s_i$ whose return type matches the goal
type.

## Installation

The package can be installed by adding `shot_un` to your list of dependencies in
`mix.exs`:

```elixir
def deps do
  [
    {:shot_un, "~> 0.1"}
  ]
end
```
