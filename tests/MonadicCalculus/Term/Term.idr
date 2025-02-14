import Syntax.MonadicCalculus.Term

%default total

data BaseType = Loc | Bit

MemMan : Syntax BaseType
MemMan = `[
    read : Loc -> T Bit
    write : Loc -> Bit -> T ()
    alloc : Bit -> T Loc
    true : Bit
    false : Bit
  ]

t : Term MemMan [<] `(T (Bit, Bit))
t = Bind "a" (PrimApp (There (There Here)) (PrimApp Here MkUnit))
    (Bind "b" (PrimApp (There (There Here)) (PrimApp Here MkUnit))
    (Bind "" (PrimApp (There (There (There Here))) (MkPair (Var (There Here)) (PrimApp (There Here) MkUnit)))
    (Bind "x" (PrimApp (There (There (There (There Here)))) (Var (There (There Here))))
    (Bind "y" (PrimApp (There (There (There (There Here)))) (Var (There (There Here))))
    (Pure (MkPair (Var (There Here)) (Var Here)))))))

t' : Term MemMan [<] `(T (Bit, Bit))
t' = `(do
    a <- alloc (false ())
    b <- alloc (false ())
    write (a, (true ()))
    x <- read a
    y <- read b
    pure (x, y)
  )

t'' : Term MemMan [<] `(T (Bit, Bit))
t'' = `(do
    a <- alloc false
    b <- alloc false
    write (a, true)
    x <- read a
    y <- read b
    pure (x, y)
  )

tsEq : (Main.t = Main.t', Main.t = Main.t'')
tsEq = (Refl, Refl)

t2 : Term MemMan `[xy : (Bit, Loc)] `((Loc, Bit))
t2 = Let "x" (Fst (Var Here))
    (Let "y" (Snd (Var (There Here)))
    (MkPair (Var Here) (Var (There Here))))

t2' : Term MemMan `[xy : (Bit, Loc)] `((Loc, Bit))
t2' = `(do
    let x = fst xy
    let y = snd xy
    (y, x)
  )

t2sEq : Main.t2 = Main.t2'
t2sEq = Refl

failing #"Can't find an implementation for NVar [<("x" :! Base Bit)] "x" (Base Loc)."#
    badTerm : Term MemMan `[x : Bit] `(Loc)
    badTerm = `(x)
