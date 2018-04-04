
all: imports.vo AExp.vo BExp.vo ASM.vo Star.vo Com.vo Big_Step.vo Small_Step.vo Compiler.vo

imports.vo : imports.v
	coqc imports.v

AExp.vo : AExp.v imports.vo
	coqc AExp.v

BExp.vo : BExp.v AExp.vo imports.vo
	coqc BExp.v

ASM.vo : ASM.v AExp.vo imports.vo
	coqc ASM.v

Star.vo : Star.v imports.vo
	coqc Star.v

Com.vo : Com.v BExp.vo AExp.vo imports.vo
	coqc Com.v

Big_Step.vo : Big_Step.v Com.vo
	coqc Big_Step.v

Small_Step.vo : Small_Step.v Big_Step.vo Star.vo Com.vo
	coqc Small_Step.v

Compiler.vo : Compiler.v Big_Step.vo Star.vo Com.vo
	coqc Compiler.v

clean:
	-rm -f *.vo *.glob .*.aux
