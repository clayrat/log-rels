module Path

%default total

public export
data Path : (t -> t -> Type) -> t -> t -> Type where
  Nil  : Path e i i
  (::) : {0 i, j, k : t} -> e i j -> Path e j k -> Path e i k

export
joinPath : Path e i j -> Path e j k -> Path e i k
joinPath []        jk = jk
joinPath (eij::ij) jk = eij :: joinPath ij jk

export
snocPath : Path e i j -> e j k -> Path e i k
snocPath []      ejk = [ejk]
snocPath (e::ij) ejk = e :: snocPath ij ejk

export
lengthPath : Path e i j -> Nat
lengthPath []     = Z
lengthPath (e::p) = S $ lengthPath p

export
mapPath : {0 et : t -> t -> Type} -> {0 eu : u -> u -> Type} -> {0 f : t -> u}
       -> ({0 i, j : t} ->      et i j ->      eu (f i) (f j))
       ->  {0 i, j : t} -> Path et i j -> Path eu (f i) (f j)
mapPath g []     = []
mapPath g (e::p) = g e :: mapPath g p

export
foldPath : {0 et : t -> t -> Type} -> {0 eu : u -> u -> Type} -> {0 f : t -> u}
        -> ({0 i, j, k : t} ->      et i j -> eu (f j) (f k) -> eu (f i) (f k))
        ->  {0 i, j, k : t} -> Path et i j -> eu (f j) (f k) -> eu (f i) (f k)
foldPath g []     ujk = ujk
foldPath g (e::p) ujk = g e (foldPath {eu} g p ujk)

export
foldlPath : {0 et : t -> t -> Type} -> {0 eu : u -> u -> Type} -> {0 f : t -> u}
        -> ({0 i, j, k : t} -> eu (f i) (f j) ->      et j k -> eu (f i) (f k))
        ->  {0 i, j, k : t} -> eu (f i) (f j) -> Path et j k -> eu (f i) (f k)
foldlPath     g uij []     = uij
foldlPath {u} g uij (e::p) = foldlPath {eu} g (g uij e) p