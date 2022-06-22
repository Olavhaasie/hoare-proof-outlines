{-# OPTIONS --safe --without-K #-}
module Everything where


{-
  These two modules define store predicates and Hoare triple
  postconditions over any type of store. They also define some common
  syntax commonly used in separation logic.
-}
import Relation.Hoare.StorePredicate
import Relation.Hoare.PostCondition

{-
  Defines an interface for the pointsto (_↦_) predicate in separation
  logic.  Also defines derived predicates from the pointsto predicate.
-}
import Relation.Hoare.Pointsto


{-
  Defines a Hoare Triple and Separation Logic Triple and structural
  rules.  The relation is polymorphic over terms that evaluate to
  values and any Store that implements `Relation.Hoare.Store.IsStore`.
-}
import Relation.Hoare

{-
  Contains a Store interface that defines operations on stores.
  Polymorhpic over any type of locations and values.
-}
import Relation.Hoare.Structures.Store

{-
  Defines a bundle for store definitions.
-}
import Relation.Hoare.Bundles


-------------------------------------------------------------
-- Ternary Constructs

{-
  A functional map with a domain to generate fresh locations.  In
  order to generate fresh locations to insert new values the map has
  an ordering on its keys, such that there always exists a key that is
  free.
-}
import Relation.Ternary.Construct.DomainMap

{-
  Defines a separating relation on `Data.List.Fresh`, aka a
  "FreshList".  A fresh list has the same structure as a normal list,
  but it also carries a proof that every element follows a binary
  relation with every other element in the list.
-}
import Relation.Ternary.Construct.FreshList

{-
  Defines a separating relation on an ordered list. An ordered list
  has the same structure as a normal list, but it also carries a proof
  that every element follows a binary relation with the following
  element in the list.
-}
import Relation.Ternary.Construct.OrderedList


-------------------------------------------------------------
-- Hoare Constructs

{-
  Implements `IsStore` for `Relation.Ternary.Construct.DomainMap`.
-}
import Relation.Hoare.Construct.DomainMap

{-
  Implements `IsStore` for `Relation.Ternary.Construct.FreshList.
  In this construct we choose the natural numbers as locations and an
  inequality relation as the relation on locations in the list. This
  means that a list can only be constructed with unique
  locations. This is useful for implementing the `IsStore` interface,
  since that requires stores to not have aliased locations.
-}
import Relation.Hoare.Construct.FreshList


-------------------------------------------------------------
-- Ternary Solvers

{-
  Defines a record that all type of monoid solvers can use to solve
  predicate expressions. This record serves as an interface for
  solvers and is used by the Hoare triple syntax to choose a solver.
-}
import Relation.Ternary.Tactic.Core

{-
  Convenient bundles used by the solver to construct proofs on
  predicate monoid expressions with a unique empty predicate.
-}
import Relation.Ternary.Tactic.Bundles

{-
  Reflection terms that are used by all solvers.
-}
import Relation.Ternary.Tactic.Reflection

{-
  Expression representation of separation logic predicates.
-}
import Relation.Ternary.Tactic.Expression

{-
  Defines how to evaluate an expression and normal form in an
  environment of predicates. Furhtermore, defines homomorphisms
  between evaluating normal forms and expressions.
-}
import Relation.Ternary.Tactic.Expression.Properties

{-
  Implements the solver interface to solve equalities on predicates in
  a ternary monoid.
-}
import Relation.Ternary.Tactic.MonoidSolver

{-
  Implements the solver interface to solve equalities on predicates in
  a ternary commutative monoid.
-}
import Relation.Ternary.Tactic.CommutativeMonoidSolver


-------------------------------------------------------------
-- Languages

{-
  Defines inductive data type and semantics for an untyped imperative
  toy language. The language is defined over an abstract memory
  location type. The big-step semantics are substitution free and
  instead use delayed substitution with an environment and
  variables. Variable naming is implemented with De Bruijn indexing.
-}
import Data.Lang.Lang
import Data.Lang.Semantics
import Data.Lang.Hoare

{-
  Defines a tactic for automatically constructing lookup of a variable
  in an environment. Makes outlines more readable and less cumbersome.
-}
import Data.Lang.Reflection
import Data.Lang.Tactic

{-
  Work in progress:
  Defines a semantics-preserving transformation of PCF to
  Administrative Normal Form. Can be used to write outlines in ANF and
  then automatically derive a triple that is not ANF but has the same
  semantics.

  import Data.PCF.Rename
  import Data.PCF.Anf
-}

-------------------------------------------------------------
-- Examples (case studies)

{-
  Some examples of abstract Hoare proof outlines. Uses the syntax from
  `Relation.Hoare` module.
-}
import HoareOutlines

{-
  Examples of proofs of simple short programs that show all features
  PCF has.
-}
import LangHoareOutlines.CopyList
import LangHoareOutlines.DoubleRef
import LangHoareOutlines.ModifyVal
import LangHoareOutlines.Swap

{-
  Examples of using the `Ternary.Relation.Tactic.MonoidSolver`.
-}
import Solver
import Bench
