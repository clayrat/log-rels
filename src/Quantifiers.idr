module Quantifiers

import Data.List.Elem
import Data.List.Quantifiers

%default total

-- TODO change Data.List.Quantifiers.indexAll to `public export`
public export
indexAllPub : Elem x xs -> All p xs -> p x
indexAllPub  Here     (p::_  ) = p
indexAllPub (There e) ( _::ps) = indexAllPub e ps