# File generated by CompCert 3.8
# Command line: -c /home/stites/git/ProbCompCert/./stanfrontend/tests/simple/simple.stan
	.comm	flips, 400, 8
	.comm	mu, 8, 8
	.text
	.align	16
	.globl set_state
set_state:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	set_state, @function
	.size	set_state, . - set_state
	.text
	.align	16
	.globl get_state
get_state:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	get_state, @function
	.size	get_state, . - get_state
	.text
	.align	16
	.globl propose
propose:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	propose, @function
	.size	propose, . - propose
	.text
	.align	16
	.globl generated_quantities
generated_quantities:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	generated_quantities, @function
	.size	generated_quantities, . - generated_quantities
	.text
	.align	16
	.globl model
model:
	.cfi_startproc
	subq	$40, %rsp
	.cfi_adjust_cfa_offset	40
	leaq	48(%rsp), %rax
	movq	%rax, 0(%rsp)
	movq	%rbx, 8(%rsp)
	xorpd	%xmm0, %xmm0
	movsd	%xmm0, 16(%rsp)
	movsd	mu(%rip), %xmm0
	call	expit
	xorpd	%xmm2, %xmm2
	movsd	.L100(%rip), %xmm11 # 1
	mulsd	%xmm0, %xmm11
	addsd	%xmm11, %xmm2
	movsd	%xmm2, 24(%rsp)
	movsd	mu(%rip), %xmm0
	call	expit
	movsd	.L100(%rip), %xmm10 # 1
	movapd	%xmm10, %xmm8
	mulsd	%xmm0, %xmm8
	subsd	%xmm0, %xmm10
	addsd	%xmm10, %xmm8
	movsd	16(%rsp), %xmm7
	addsd	%xmm8, %xmm7
	movsd	%xmm7, 32(%rsp)
	movsd	24(%rsp), %xmm0
	call	expit
	xorpd	%xmm3, %xmm3
	movsd	.L100(%rip), %xmm12 # 1
	mulsd	%xmm0, %xmm12
	addsd	%xmm12, %xmm3
	movsd	%xmm3, 16(%rsp)
	movsd	16(%rsp), %xmm0
	call	expit
	movsd	.L100(%rip), %xmm2 # 1
	xorpd	%xmm1, %xmm1
	movapd	%xmm2, %xmm9
	mulsd	%xmm0, %xmm9
	movapd	%xmm2, %xmm13
	subsd	%xmm0, %xmm13
	addsd	%xmm13, %xmm9
	movsd	32(%rsp), %xmm3
	addsd	%xmm9, %xmm3
	movsd	%xmm3, 24(%rsp)
	movsd	16(%rsp), %xmm0
	call	uniform_lpdf
	movsd	24(%rsp), %xmm4
	addsd	%xmm0, %xmm4
	movsd	%xmm4, 24(%rsp)
	xorl	%ebx, %ebx
.L101:
	leaq	flips(%rip), %rsi
	movslq	%ebx, %rcx
	movl	0(%rsi,%rcx,4), %edi
	movsd	16(%rsp), %xmm0
	call	bernoulli_lpmf
	movsd	%xmm0, 16(%rsp)
	movsd	24(%rsp), %xmm5
	movsd	16(%rsp), %xmm6
	addsd	%xmm6, %xmm5
	movsd	%xmm5, 24(%rsp)
	leal	1(%ebx), %ebx
	cmpl	$100, %ebx
	jl	.L101
	movsd	24(%rsp), %xmm0
	movq	8(%rsp), %rbx
	addq	$40, %rsp
	ret
	.cfi_endproc
	.type	model, @function
	.size	model, . - model
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L100:	.quad	0x3ff0000000000000
	.text
	.align	16
	.globl transformed_parameters
transformed_parameters:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	transformed_parameters, @function
	.size	transformed_parameters, . - transformed_parameters
	.text
	.align	16
	.globl parameters
parameters:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	movsd	.L102(%rip), %xmm0 # 0.5
	movsd	%xmm0, mu(%rip)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	parameters, @function
	.size	parameters, . - parameters
	.section	.rodata.cst8,"aM",@progbits,8
	.align	8
.L102:	.quad	0x3fe0000000000000
	.text
	.align	16
	.globl transformed_data
transformed_data:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	transformed_data, @function
	.size	transformed_data, . - transformed_data
	.text
	.align	16
	.globl data
data:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
	leaq	16(%rsp), %rax
	movq	%rax, 0(%rsp)
	xorl	%eax, %eax
.L103:
	leaq	flips(%rip), %rcx
	movslq	%eax, %rsi
	xorl	%edx, %edx
	movl	%edx, 0(%rcx,%rsi,4)
	leal	1(%eax), %eax
	cmpl	$100, %eax
	jl	.L103
	addq	$8, %rsp
	ret
	.cfi_endproc
	.type	data, @function
	.size	data, . - data
