{-
  En este archivo se va a intentar dar una definicion en Idris de Attribute Grammars, utilizando records extensibles:
  http://foswiki.cs.uu.nl/foswiki/pub/Center/AspectAG/paper-icfp.pdf
-}
module AttributeGrammar

import Data.Vect
import Extensible_Records

%default total


-- Doodles

-- El DSL deberia comportarse de esta forma
{-
asp_min = synthethise smin at {Tree}
          use (\a b -> min a b) at {Node}
          define at Leaf = i
          
asp_ival = inherit ival at {Tree}
           copy at {Node}
           define at Root.tree = tree.smin
           
asp_sres = syntethise sres at {Root, Tree}
           use Node (Leaf 0) at {Node}
           define at Root = tree.sres
                     Leaf = Leaf lhs.ival

-}


-- DDG "transformation"
type DDG = In [Record "inherited del padre"] (Functor "sintetizado de lo hijos") ->
         Out [Record "sintetizado en el padre"] (Functor "inherited en los hijos")
 
-- Aspects 
data AspectType = Inh | Syn
data Aspect : Type where
  MkAspect : (at : AspectType) -> Algo de las reglas semanticas -> Aspect at algoMas
  
-- Aspect composition
(<+>) : Aspect Inh -> Aspect Syn -> Aspect Syn
        Aspect Syn -> Aspect Inh -> Aspect Inh (ambos tipos)

-- "Evaluador" de un functor t (como Tree t)
sem_Root : Aspect at -> Functor t -> ....

namespace Example
  data TreeF : Type -> Type where
    Leaf : t -> TreeF t
    Node : TreeF t -> TreeF t -> TreeF t
  
  type Tree = TreeF Int
  
  type RootF t = RootF (TreeF t)
  type Root = RootF Int
  
  repmin = sem_Root $ asp_smin <+> asp_ival <+> asp_sres
  repavg = sem_Root $ asp_avg <+> asp_ival <+> asp_sres
