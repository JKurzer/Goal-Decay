import Lake
open Lake DSL

package goaldecay where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

@[default_target]
lean_lib GoalDecay where
