{-
  Forma simple de definir listas heterogeneas. Seria equivalente a utilizar tipos existenciales en Haskell 
 -}

%default total

data HList : Type where
    Nil : HList
    (::) : {A : Type} -> (x : A) -> HList -> HList
        
hListExample : HList
hListExample = [1,"2"]
