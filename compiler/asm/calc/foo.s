.data
L_fmt:
	.ascii "%d\n\0"
.text
.globl _main
_main:
	pushq %rbp
	movq  %rsp, %rbp
	movl  $3, %ecx
	movl  $4, %edx
	addl  %edx, %ecx
	leaq L_fmt(%rip), %rdi
	movslq %ecx, %rsi
	movb $0, %al
	call  _printf
	leave
	ret
