------------------------------------------------------------------------
-- A library for working with dependently typed syntax
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- This library is leaning heavily on two of Conor McBride's papers:
--
-- * Type-Preserving Renaming and Substitution.
--
-- * Outrageous but Meaningful Coincidences: Dependent type-safe
--   syntax and evaluation.

-- This module gives a brief overview of the modules in the library.

module README where

------------------------------------------------------------------------
-- The library

-- Contexts, variables, context morphisms, context extensions, etc.

import deBruijn.Context

-- Parallel substitutions (defined using an inductive family).

import deBruijn.Substitution.Data.Basics

-- A map function for the substitutions.

import deBruijn.Substitution.Data.Map

-- Some simple substitution combinators. (Given a term type which
-- supports weakening and transformation of variables to terms various
-- substitutions are defined and various lemmas proved.)

import deBruijn.Substitution.Data.Simple

-- Given an operation which applies a substitution to a term,
-- satisfying some properties, more operations and lemmas are
-- defined/proved.
--
-- (This module reexports various other modules.)

import deBruijn.Substitution.Data.Application

-- A module which repackages (and reexports) the development under
-- deBruijn.Substitution.Data.

import deBruijn.Substitution.Data

-- Some modules mirroring the development under
-- deBruijn.Substitution.Data, but using substitutions defined as
-- functions rather than data.
--
-- The functional version of substitutions is in some respects easier
-- to work with than the one based on data, but in other respects more
-- awkward. I maintain both developments so that they can be compared.

import deBruijn.Substitution.Function.Basics
import deBruijn.Substitution.Function.Map
import deBruijn.Substitution.Function.Simple

-- The two definitions of substitutions are isomorphic (assuming
-- extensionality).

import deBruijn.Substitution.Isomorphic

------------------------------------------------------------------------
-- An example showing how the library can be used

-- A well-typed representation of a dependently typed language.

import README.DependentlyTyped.Term

-- Normal and neutral terms.

import README.DependentlyTyped.NormalForm

-- Instantiation of deBruijn.Substitution.Data for terms.

import README.DependentlyTyped.Term.Substitution

-- Instantiation of deBruijn.Substitution.Data for normal and neutral
-- terms.

import README.DependentlyTyped.NormalForm.Substitution

-- Normalisation by evaluation (one key property remains to be
-- proved).

import README.DependentlyTyped.NBE

-- An observation: There is a term without a corresponding syntactic
-- type (given some assumptions).

import README.DependentlyTyped.Term-without-type

-- TODO: Add an untyped example.
