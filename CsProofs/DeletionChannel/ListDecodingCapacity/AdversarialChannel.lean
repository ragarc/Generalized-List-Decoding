import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CsProofs.InformationTheory.Types.Defs

/--
    X is the input alphabet, Y is the output alphabet.
-/
structure Channel (n : Nat) (X S Y : Type)
[Fintype X] [Fintype Y] [Fintype S] where
    channelRule : X × S → Y
    inputConstraints : Set (NType n X)
    noiseConstraints : Set (NType n S)
