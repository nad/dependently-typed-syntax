------------------------------------------------------------------------
-- Contexts, variables, context morphisms, context extensions, etc.
------------------------------------------------------------------------

-- The contexts, variables, etc. are parametrised by a universe.

open import Universe

module deBruijn.Context
  {i u e} (Uni : Indexed-universe i u e) where

-- Contexts, variables, context morphisms, etc.

import deBruijn.Context.Basics as Basics
open Basics Uni public

-- Context extensions with the rightmost element in the outermost
-- position.

import deBruijn.Context.Extension.Right as Right
open Right Uni public

-- Context extensions with the leftmost element in the outermost
-- position.

import deBruijn.Context.Extension.Left as Left
open Left Uni public

-- The two definitions of context extensions are isomorphic.

import deBruijn.Context.Extension.Isomorphic as Isomorphic
open Isomorphic Uni public

-- An abstraction: term-like things.

import deBruijn.Context.Term-like as Term-like
open Term-like Uni public
