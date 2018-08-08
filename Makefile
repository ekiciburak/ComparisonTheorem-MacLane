
all: Imports.vo Categories.vo Functor.vo NaturalTransformation.vo Monads.vo Adjunctions.vo Comparison.vo UseCase.vo

Imports.vo : Imports.v
	coqc Imports.v

Categories.vo : Categories.v Imports.vo
	coqc Categories.v

Functor.vo : Functor.v Categories.vo Imports.vo
	coqc Functor.v
	
NaturalTransformation.vo : NaturalTransformation.v Functor.vo Categories.vo Imports.vo
	coqc NaturalTransformation.v

Monads.vo : Monads.v NaturalTransformation.vo Functor.vo Categories.vo Imports.vo
	coqc Monads.v

Adjunctions.vo : Adjunctions.v Monads.vo NaturalTransformation.vo Functor.vo Categories.vo Imports.vo
	coqc Adjunctions.v

Comparison.vo : Comparison.v Adjunctions.vo Monads.vo NaturalTransformation.vo Functor.vo Categories.vo Imports.vo
	coqc Comparison.v

UseCase.vo : UseCase.v Comparison.v Adjunctions.vo Monads.vo NaturalTransformation.vo Functor.vo Categories.vo Imports.vo
	coqc UseCase.v

clean:
	-rm -f *.vo *.glob .*.aux
