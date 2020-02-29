------------------------------------------------------------------------
-- Application of substitutions
------------------------------------------------------------------------

-- Given an operation which applies a substitution to a term, subject
-- to some conditions, more operations and lemmas are defined/proved.

-- (This module reexports various other modules.)

open import Data.Universe.Indexed

module deBruijn.Substitution.Data.Application
  {i u e} {Uni : IndexedUniverse i u e} where

import deBruijn.Substitution.Data.Application.Application
open deBruijn.Substitution.Data.Application.Application
  {_} {_} {_} {Uni} public
import deBruijn.Substitution.Data.Application.Application21
open deBruijn.Substitution.Data.Application.Application21
  {_} {_} {_} {Uni} public
import deBruijn.Substitution.Data.Application.Application22
open deBruijn.Substitution.Data.Application.Application22
  {_} {_} {_} {Uni} public
import deBruijn.Substitution.Data.Application.Application1
open deBruijn.Substitution.Data.Application.Application1
  {_} {_} {_} {Uni} public
