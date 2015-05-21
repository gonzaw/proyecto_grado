# Proyecto de Grado
Gonzalo Waszczuk, Facultad de Ingenieria, UDELAR, 2015

## Introduccion
Este repositorio contiene codigo y archivos relacionados a mi proyecto de grado. El proyecto es "Desarrollo de DSLs en lenguajes con tipos dependientes" y se puede visualizar aqui: [Proyecto](https://eva.fing.edu.uy/mod/data/view.php?d=72&rid=822)

## Estructura

### HList
Codigo relacionado a la investigacion de listas hereogeneas en Idris

* **HList_Dynamic.idr:** Implementacion similar a la forma de hacerlo en Haskell con el tipo `Dynamic`.
* **HList_Existentials.idr:** Implementacion similar a la forma de hacerlo en Haskell con *tipos existenciales*.
* **HList_Structured.idr:** Implementacion que utiliza un predicado de tipos para definir la estructura interna de cada elemento de la lista heterogenea.
* **HList_HVect.idr:** Implementacion que utiliza el tipo `HVect` nativo de las librerias de Idris. En este archivo se encuentran ejemplos, discusiones, y algunos casos de uso posibles.
* **HList_HVect_Pruebas.idr:** Varias pruebas que se realizaron sobre listas heterogeneas de HVect, pero que fallaron por algun motivo u otro.
* **Extensible_Records.idr:** Implementacion de un tipo de records extensibles, utilizando tecnicas similares a HVect, pero con una estructura distinta.

### Compiler
Codigo relacionado al desarrollo del compilador correcto descrito por el paper *"A type-correct, stack-safe, provably correct expression compiler in Epigram"* en Idris

* **Compiler.idr:** Implementacion original del paper, traducida a Idris.
* **Compiler_UpdatePruebas.idr:** Implementacion modificada, donde la prueba del teorema del paper esta codificada, "silenciosamente", en los tipos de cada estructura.
