# Proyecto de Grado
Gonzalo Waszczuk, Facultad de Ingeniería, UDELAR, 2015

## Introducción
Este repositorio contiene código y archivos relacionados a mi proyecto de grado. El proyecto es "Desarrollo de DSLs en lenguajes con tipos dependientes" y se puede visualizar aquí: [Proyecto](https://eva.fing.edu.uy/mod/data/view.php?d=72&rid=822)

## Estructura

## ExtensibleRecords
Código relacionado a la investigación de records extensibles en Idris

* **Extensible_Records.idr:** Implementación de records extensibles similar a la de HList de Haskell vista [aquí](https://hackage.haskell.org/package/HList), y en el paper *"Strongly Typed Heterogeneous Collections"*.
* **Extensible_Records_Vect.idr:** Implementación de records extensibles vieja, utilizando "Vect n" en vez de "List".
* **Extensible_Records_Examples.idr:** Ejemplos de funcionalidades de records extensibles.

### HList
Código relacionado a la investigación de listas hereogéneas en Idris

* **HList_Dynamic.idr:** Implementación similar a la forma de hacerlo en Haskell con el tipo `Dynamic`.
* **HList_Existentials.idr:** Implementación similar a la forma de hacerlo en Haskell con *tipos existenciales*.
* **HList_Structured.idr:** Implementación que utiliza un predicado de tipos para definir la estructura interna de cada elemento de la lista heterogénea.
* **HList_HVect.idr:** Implementación que utiliza el tipo `HVect` nativo de las librerias de Idris. En este archivo se encuentran ejemplos, discusiones, y algunos casos de uso posibles.
* **HList_HVect_Pruebas.idr:** Varias pruebas que se realizaron sobre listas heterogéneas de HVect, pero que fallaron por algún motivo u otro.

### Compiler
Código relacionado al desarrollo del compilador correcto descrito por el paper *"A type-correct, stack-safe, provably correct expression compiler in Epigram"* en Idris

* **Compiler.idr:** Implementación original del paper, traducida a Idris.
* **Compiler_UpdatePruebas.idr:** Implementación modificada, donde la prueba del teorema del paper está codificada, "silenciosamente", en los tipos de cada estructura.

### Informe
Archivos LaTeX y otros utilizados para la creación del informe final.
