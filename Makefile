
all: Imports.vo Category.vo Functor.vo NaturalTransformation.vo Monad.vo Adjunction.vo Comparison.vo UseCase.vo

Imports.vo : Imports.v
	coqc Imports.v

Category.vo : Category.v Imports.vo
	coqc Category.v

Functor.vo : Functor.v Category.vo Imports.vo
	coqc Functor.v
	
NaturalTransformation.vo : NaturalTransformation.v Functor.vo Category.vo Imports.vo
	coqc NaturalTransformation.v

Monad.vo : Monad.v NaturalTransformation.vo Functor.vo Category.vo Imports.vo
	coqc Monad.v

Adjunction.vo : Adjunction.v Monad.vo NaturalTransformation.vo Functor.vo Category.vo Imports.vo
	coqc Adjunction.v

Comparison.vo : Comparison.v Adjunction.vo Monad.vo NaturalTransformation.vo Functor.vo Category.vo Imports.vo
	coqc Comparison.v

UseCase.vo : UseCase.v Comparison.v Adjunction.vo Monad.vo NaturalTransformation.vo Functor.vo Category.vo Imports.vo
	coqc UseCase.v

clean:
	-rm -f *.vo *.glob .*.aux
