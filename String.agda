module _ where

open import Agda.Builtin.String public

_++_ = primStringAppend
_==_ = primStringEquality   -- sometimes not working with "",
                            -- defined differently in stdlib (with _==_ on Nat)
toList = primStringToList
fromList = primStringFromList


infix 3 _++_
infix 2 _==_

