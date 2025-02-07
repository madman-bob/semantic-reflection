import Syntax.STLC.Term

%default total

data BaseType = Number | Boolean

t : Term [<] `(Number -> Number)
t = Lam "x" (Base Number) (Var Here)

t' : Term [<] `(Number -> Number)
t' = `(\x => x)

tsEq : Main.t = Main.t'
tsEq = Refl

failing #"Can't find an implementation for NVar [<("x" :! Base Number)] "x" (Base Boolean)."#
    badTerm : Term [<] `(Number -> Boolean)
    badTerm = `(\x => x)

t2 : Term {t = BaseType} [<] ?
t2 = Lam "x" (Base Boolean) (Var Here)

t2' : Term {t = BaseType} [<] ?
t2' = `(\x : Boolean => x)

t2sEq : Main.t2 = Main.t2'
t2sEq = Refl

BaseOps : Context (Ty BaseType)
BaseOps = `[
    (+) : Number -> Number -> Number
    (-) : Number -> Number -> Number
    (*) : Number -> Number -> Number
    (/) : Number -> Number -> Number

    (==) : Number -> Number -> Boolean
    (>) : Number -> Number -> Boolean
    not : Boolean -> Boolean
    ifThenElse : Boolean -> Number -> Number -> Number
  ]

t3 : Term BaseOps `(Number -> Number -> Number)
t3 = Lam "x" (Base Number) (Lam "y" (Base Number)
    (App (App (App (Var (There (There Here)))
        (App (App (Var (There (There (There (There Here))))) (Var (There Here))) (Var Here)))
        (Var (There Here)))
        (Var Here)))

t3' : Term BaseOps `(Number -> Number -> Number)
t3' = `(\x, y => ifThenElse (x > y) x y)

t3sEq : Main.t3 = Main.t3'
t3sEq = Refl

t4 : Term BaseOps `(Number -> Number -> Number)
t4 = Lam "x" (Base Number) (Lam "y" (Base Number)
    (App (Lam "x2" (Base Number)
        (App (Lam "y2" (Base Number)
            (App (App (Var (There (There (There (There (There (There (There (There (There (There (There Here)))))))))))) (Var (There Here))) (Var Here)))
        (App (App (Var (There (There (There (There (There (There (There (There Here))))))))) (Var (There Here))) (Var (There Here)))))
    (App (App (Var (There (There (There (There (There (There (There Here)))))))) (Var (There Here))) (Var (There Here)))))

t4' : Term BaseOps `(Number -> Number -> Number)
t4' = `(\x, y => do
    let x2 = x * x
    let y2 = y * y
    x2 + y2
  )

t4sEq : Main.t4 = Main.t4'
t4sEq = Refl
