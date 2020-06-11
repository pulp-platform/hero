
seq.elf:     file format elf64-littleaarch64


Disassembly of section .init:

00000000004008b8 <_init>:
  4008b8:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  4008bc:	910003fd 	mov	x29, sp
  4008c0:	9400006c 	bl	400a70 <call_weak_fn>
  4008c4:	a8c17bfd 	ldp	x29, x30, [sp], #16
  4008c8:	d65f03c0 	ret

Disassembly of section .plt:

00000000004008d0 <.plt>:
  4008d0:	a9bf7bf0 	stp	x16, x30, [sp, #-16]!
  4008d4:	b0000090 	adrp	x16, 411000 <__FRAME_END__+0xfa08>
  4008d8:	f947fe11 	ldr	x17, [x16, #4088]
  4008dc:	913fe210 	add	x16, x16, #0xff8
  4008e0:	d61f0220 	br	x17
  4008e4:	d503201f 	nop
  4008e8:	d503201f 	nop
  4008ec:	d503201f 	nop

00000000004008f0 <exit@plt>:
  4008f0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4008f4:	f9400211 	ldr	x17, [x16]
  4008f8:	91000210 	add	x16, x16, #0x0
  4008fc:	d61f0220 	br	x17

0000000000400900 <fputc@plt>:
  400900:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400904:	f9400611 	ldr	x17, [x16, #8]
  400908:	91002210 	add	x16, x16, #0x8
  40090c:	d61f0220 	br	x17

0000000000400910 <clock_gettime@plt>:
  400910:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400914:	f9400a11 	ldr	x17, [x16, #16]
  400918:	91004210 	add	x16, x16, #0x10
  40091c:	d61f0220 	br	x17

0000000000400920 <fclose@plt>:
  400920:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400924:	f9400e11 	ldr	x17, [x16, #24]
  400928:	91006210 	add	x16, x16, #0x18
  40092c:	d61f0220 	br	x17

0000000000400930 <fopen@plt>:
  400930:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400934:	f9401211 	ldr	x17, [x16, #32]
  400938:	91008210 	add	x16, x16, #0x20
  40093c:	d61f0220 	br	x17

0000000000400940 <malloc@plt>:
  400940:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400944:	f9401611 	ldr	x17, [x16, #40]
  400948:	9100a210 	add	x16, x16, #0x28
  40094c:	d61f0220 	br	x17

0000000000400950 <__libc_start_main@plt>:
  400950:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400954:	f9401a11 	ldr	x17, [x16, #48]
  400958:	9100c210 	add	x16, x16, #0x30
  40095c:	d61f0220 	br	x17

0000000000400960 <calloc@plt>:
  400960:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400964:	f9401e11 	ldr	x17, [x16, #56]
  400968:	9100e210 	add	x16, x16, #0x38
  40096c:	d61f0220 	br	x17

0000000000400970 <strerror@plt>:
  400970:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400974:	f9402211 	ldr	x17, [x16, #64]
  400978:	91010210 	add	x16, x16, #0x40
  40097c:	d61f0220 	br	x17

0000000000400980 <fgetc_unlocked@plt>:
  400980:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400984:	f9402611 	ldr	x17, [x16, #72]
  400988:	91012210 	add	x16, x16, #0x48
  40098c:	d61f0220 	br	x17

0000000000400990 <__gmon_start__@plt>:
  400990:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400994:	f9402a11 	ldr	x17, [x16, #80]
  400998:	91014210 	add	x16, x16, #0x50
  40099c:	d61f0220 	br	x17

00000000004009a0 <abort@plt>:
  4009a0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4009a4:	f9402e11 	ldr	x17, [x16, #88]
  4009a8:	91016210 	add	x16, x16, #0x58
  4009ac:	d61f0220 	br	x17

00000000004009b0 <free@plt>:
  4009b0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4009b4:	f9403211 	ldr	x17, [x16, #96]
  4009b8:	91018210 	add	x16, x16, #0x60
  4009bc:	d61f0220 	br	x17

00000000004009c0 <fwrite@plt>:
  4009c0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4009c4:	f9403611 	ldr	x17, [x16, #104]
  4009c8:	9101a210 	add	x16, x16, #0x68
  4009cc:	d61f0220 	br	x17

00000000004009d0 <fputc_unlocked@plt>:
  4009d0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4009d4:	f9403a11 	ldr	x17, [x16, #112]
  4009d8:	9101c210 	add	x16, x16, #0x70
  4009dc:	d61f0220 	br	x17

00000000004009e0 <printf@plt>:
  4009e0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4009e4:	f9403e11 	ldr	x17, [x16, #120]
  4009e8:	9101e210 	add	x16, x16, #0x78
  4009ec:	d61f0220 	br	x17

00000000004009f0 <__assert_fail@plt>:
  4009f0:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  4009f4:	f9404211 	ldr	x17, [x16, #128]
  4009f8:	91020210 	add	x16, x16, #0x80
  4009fc:	d61f0220 	br	x17

0000000000400a00 <__errno_location@plt>:
  400a00:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400a04:	f9404611 	ldr	x17, [x16, #136]
  400a08:	91022210 	add	x16, x16, #0x88
  400a0c:	d61f0220 	br	x17

0000000000400a10 <fprintf@plt>:
  400a10:	d0000090 	adrp	x16, 412000 <exit@GLIBC_2.17>
  400a14:	f9404a11 	ldr	x17, [x16, #144]
  400a18:	91024210 	add	x16, x16, #0x90
  400a1c:	d61f0220 	br	x17

Disassembly of section .text:

0000000000400a20 <_start>:
  400a20:	d280001d 	mov	x29, #0x0                   	// #0
  400a24:	d280001e 	mov	x30, #0x0                   	// #0
  400a28:	aa0003e5 	mov	x5, x0
  400a2c:	f94003e1 	ldr	x1, [sp]
  400a30:	910023e2 	add	x2, sp, #0x8
  400a34:	910003e6 	mov	x6, sp
  400a38:	d2e00000 	movz	x0, #0x0, lsl #48
  400a3c:	f2c00000 	movk	x0, #0x0, lsl #32
  400a40:	f2a00800 	movk	x0, #0x40, lsl #16
  400a44:	f281da00 	movk	x0, #0xed0
  400a48:	d2e00003 	movz	x3, #0x0, lsl #48
  400a4c:	f2c00003 	movk	x3, #0x0, lsl #32
  400a50:	f2a00803 	movk	x3, #0x40, lsl #16
  400a54:	f2827703 	movk	x3, #0x13b8
  400a58:	d2e00004 	movz	x4, #0x0, lsl #48
  400a5c:	f2c00004 	movk	x4, #0x0, lsl #32
  400a60:	f2a00804 	movk	x4, #0x40, lsl #16
  400a64:	f2828704 	movk	x4, #0x1438
  400a68:	97ffffba 	bl	400950 <__libc_start_main@plt>
  400a6c:	97ffffcd 	bl	4009a0 <abort@plt>

0000000000400a70 <call_weak_fn>:
  400a70:	b0000080 	adrp	x0, 411000 <__FRAME_END__+0xfa08>
  400a74:	f947f000 	ldr	x0, [x0, #4064]
  400a78:	b4000040 	cbz	x0, 400a80 <call_weak_fn+0x10>
  400a7c:	17ffffc5 	b	400990 <__gmon_start__@plt>
  400a80:	d65f03c0 	ret

0000000000400a84 <deregister_tm_clones>:
  400a84:	d0000080 	adrp	x0, 412000 <exit@GLIBC_2.17>
  400a88:	9102a001 	add	x1, x0, #0xa8
  400a8c:	d0000080 	adrp	x0, 412000 <exit@GLIBC_2.17>
  400a90:	9102a000 	add	x0, x0, #0xa8
  400a94:	eb00003f 	cmp	x1, x0
  400a98:	54000140 	b.eq	400ac0 <deregister_tm_clones+0x3c>  // b.none
  400a9c:	d10043ff 	sub	sp, sp, #0x10
  400aa0:	b0000001 	adrp	x1, 401000 <main+0x130>
  400aa4:	f9422c21 	ldr	x1, [x1, #1112]
  400aa8:	f90007e1 	str	x1, [sp, #8]
  400aac:	b4000061 	cbz	x1, 400ab8 <deregister_tm_clones+0x34>
  400ab0:	910043ff 	add	sp, sp, #0x10
  400ab4:	d61f0020 	br	x1
  400ab8:	910043ff 	add	sp, sp, #0x10
  400abc:	d65f03c0 	ret
  400ac0:	d65f03c0 	ret

0000000000400ac4 <register_tm_clones>:
  400ac4:	d0000080 	adrp	x0, 412000 <exit@GLIBC_2.17>
  400ac8:	9102a001 	add	x1, x0, #0xa8
  400acc:	d0000080 	adrp	x0, 412000 <exit@GLIBC_2.17>
  400ad0:	9102a000 	add	x0, x0, #0xa8
  400ad4:	cb000021 	sub	x1, x1, x0
  400ad8:	d2800042 	mov	x2, #0x2                   	// #2
  400adc:	9343fc21 	asr	x1, x1, #3
  400ae0:	9ac20c21 	sdiv	x1, x1, x2
  400ae4:	b4000141 	cbz	x1, 400b0c <register_tm_clones+0x48>
  400ae8:	d10043ff 	sub	sp, sp, #0x10
  400aec:	b0000002 	adrp	x2, 401000 <main+0x130>
  400af0:	f9423042 	ldr	x2, [x2, #1120]
  400af4:	f90007e2 	str	x2, [sp, #8]
  400af8:	b4000062 	cbz	x2, 400b04 <register_tm_clones+0x40>
  400afc:	910043ff 	add	sp, sp, #0x10
  400b00:	d61f0040 	br	x2
  400b04:	910043ff 	add	sp, sp, #0x10
  400b08:	d65f03c0 	ret
  400b0c:	d65f03c0 	ret

0000000000400b10 <__do_global_dtors_aux>:
  400b10:	a9be7bfd 	stp	x29, x30, [sp, #-32]!
  400b14:	910003fd 	mov	x29, sp
  400b18:	f9000bf3 	str	x19, [sp, #16]
  400b1c:	d0000093 	adrp	x19, 412000 <exit@GLIBC_2.17>
  400b20:	3942c260 	ldrb	w0, [x19, #176]
  400b24:	35000080 	cbnz	w0, 400b34 <__do_global_dtors_aux+0x24>
  400b28:	97ffffd7 	bl	400a84 <deregister_tm_clones>
  400b2c:	52800020 	mov	w0, #0x1                   	// #1
  400b30:	3902c260 	strb	w0, [x19, #176]
  400b34:	f9400bf3 	ldr	x19, [sp, #16]
  400b38:	a8c27bfd 	ldp	x29, x30, [sp], #32
  400b3c:	d65f03c0 	ret

0000000000400b40 <frame_dummy>:
  400b40:	17ffffe1 	b	400ac4 <register_tm_clones>

0000000000400b44 <polybench_flush_cache>:
  400b44:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  400b48:	52802000 	mov	w0, #0x100                 	// #256
  400b4c:	72a00800 	movk	w0, #0x40, lsl #16
  400b50:	52800101 	mov	w1, #0x8                   	// #8
  400b54:	910003fd 	mov	x29, sp
  400b58:	97ffff82 	bl	400960 <calloc@plt>
  400b5c:	5280ff09 	mov	w9, #0x7f8                 	// #2040
  400b60:	aa1f03e8 	mov	x8, xzr
  400b64:	9e6703e0 	fmov	d0, xzr
  400b68:	72a04009 	movk	w9, #0x200, lsl #16
  400b6c:	8b08000a 	add	x10, x0, x8
  400b70:	fd400541 	ldr	d1, [x10, #8]
  400b74:	91002108 	add	x8, x8, #0x8
  400b78:	eb09011f 	cmp	x8, x9
  400b7c:	1e612800 	fadd	d0, d0, d1
  400b80:	54ffff61 	b.ne	400b6c <polybench_flush_cache+0x28>  // b.any
  400b84:	1e649001 	fmov	d1, #1.000000000000000000e+01
  400b88:	1e612000 	fcmp	d0, d1
  400b8c:	54000068 	b.hi	400b98 <polybench_flush_cache+0x54>  // b.pmore
  400b90:	a8c17bfd 	ldp	x29, x30, [sp], #16
  400b94:	17ffff87 	b	4009b0 <free@plt>
  400b98:	b0000000 	adrp	x0, 401000 <main+0x130>
  400b9c:	b0000001 	adrp	x1, 401000 <main+0x130>
  400ba0:	b0000003 	adrp	x3, 401000 <main+0x130>
  400ba4:	9111a000 	add	x0, x0, #0x468
  400ba8:	9111d021 	add	x1, x1, #0x474
  400bac:	91121063 	add	x3, x3, #0x484
  400bb0:	52800c02 	mov	w2, #0x60                  	// #96
  400bb4:	97ffff8f 	bl	4009f0 <__assert_fail@plt>

0000000000400bb8 <polybench_prepare_instruments>:
  400bb8:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  400bbc:	52802000 	mov	w0, #0x100                 	// #256
  400bc0:	72a00800 	movk	w0, #0x40, lsl #16
  400bc4:	52800101 	mov	w1, #0x8                   	// #8
  400bc8:	910003fd 	mov	x29, sp
  400bcc:	97ffff65 	bl	400960 <calloc@plt>
  400bd0:	5280ff09 	mov	w9, #0x7f8                 	// #2040
  400bd4:	aa1f03e8 	mov	x8, xzr
  400bd8:	9e6703e0 	fmov	d0, xzr
  400bdc:	72a04009 	movk	w9, #0x200, lsl #16
  400be0:	8b08000a 	add	x10, x0, x8
  400be4:	fd400541 	ldr	d1, [x10, #8]
  400be8:	91002108 	add	x8, x8, #0x8
  400bec:	eb09011f 	cmp	x8, x9
  400bf0:	1e602820 	fadd	d0, d1, d0
  400bf4:	54ffff61 	b.ne	400be0 <polybench_prepare_instruments+0x28>  // b.any
  400bf8:	1e649001 	fmov	d1, #1.000000000000000000e+01
  400bfc:	1e612000 	fcmp	d0, d1
  400c00:	54000068 	b.hi	400c0c <polybench_prepare_instruments+0x54>  // b.pmore
  400c04:	a8c17bfd 	ldp	x29, x30, [sp], #16
  400c08:	17ffff6a 	b	4009b0 <free@plt>
  400c0c:	b0000000 	adrp	x0, 401000 <main+0x130>
  400c10:	b0000001 	adrp	x1, 401000 <main+0x130>
  400c14:	b0000003 	adrp	x3, 401000 <main+0x130>
  400c18:	9111a000 	add	x0, x0, #0x468
  400c1c:	9111d021 	add	x1, x1, #0x474
  400c20:	91121063 	add	x3, x3, #0x484
  400c24:	52800c02 	mov	w2, #0x60                  	// #96
  400c28:	97ffff72 	bl	4009f0 <__assert_fail@plt>

0000000000400c2c <polybench_timer_start>:
  400c2c:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  400c30:	52802000 	mov	w0, #0x100                 	// #256
  400c34:	72a00800 	movk	w0, #0x40, lsl #16
  400c38:	52800101 	mov	w1, #0x8                   	// #8
  400c3c:	910003fd 	mov	x29, sp
  400c40:	97ffff48 	bl	400960 <calloc@plt>
  400c44:	5280ff09 	mov	w9, #0x7f8                 	// #2040
  400c48:	aa1f03e8 	mov	x8, xzr
  400c4c:	9e6703e0 	fmov	d0, xzr
  400c50:	72a04009 	movk	w9, #0x200, lsl #16
  400c54:	8b08000a 	add	x10, x0, x8
  400c58:	fd400541 	ldr	d1, [x10, #8]
  400c5c:	91002108 	add	x8, x8, #0x8
  400c60:	eb09011f 	cmp	x8, x9
  400c64:	1e612800 	fadd	d0, d0, d1
  400c68:	54ffff61 	b.ne	400c54 <polybench_timer_start+0x28>  // b.any
  400c6c:	1e649001 	fmov	d1, #1.000000000000000000e+01
  400c70:	1e612000 	fcmp	d0, d1
  400c74:	540000c8 	b.hi	400c8c <polybench_timer_start+0x60>  // b.pmore
  400c78:	97ffff4e 	bl	4009b0 <free@plt>
  400c7c:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400c80:	f9006d1f 	str	xzr, [x8, #216]
  400c84:	a8c17bfd 	ldp	x29, x30, [sp], #16
  400c88:	d65f03c0 	ret
  400c8c:	b0000000 	adrp	x0, 401000 <main+0x130>
  400c90:	b0000001 	adrp	x1, 401000 <main+0x130>
  400c94:	b0000003 	adrp	x3, 401000 <main+0x130>
  400c98:	9111a000 	add	x0, x0, #0x468
  400c9c:	9111d021 	add	x1, x1, #0x474
  400ca0:	91121063 	add	x3, x3, #0x484
  400ca4:	52800c02 	mov	w2, #0x60                  	// #96
  400ca8:	97ffff52 	bl	4009f0 <__assert_fail@plt>

0000000000400cac <polybench_timer_stop>:
  400cac:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400cb0:	f900691f 	str	xzr, [x8, #208]
  400cb4:	d65f03c0 	ret

0000000000400cb8 <polybench_timer_print>:
  400cb8:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400cbc:	d0000089 	adrp	x9, 412000 <exit@GLIBC_2.17>
  400cc0:	fd406900 	ldr	d0, [x8, #208]
  400cc4:	fd406d21 	ldr	d1, [x9, #216]
  400cc8:	b0000000 	adrp	x0, 401000 <main+0x130>
  400ccc:	91128400 	add	x0, x0, #0x4a1
  400cd0:	1e613800 	fsub	d0, d0, d1
  400cd4:	17ffff43 	b	4009e0 <printf@plt>

0000000000400cd8 <polybench_alloc_data>:
  400cd8:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  400cdc:	93407c28 	sxtw	x8, w1
  400ce0:	9b007d00 	mul	x0, x8, x0
  400ce4:	910003fd 	mov	x29, sp
  400ce8:	97ffff16 	bl	400940 <malloc@plt>
  400cec:	b4000060 	cbz	x0, 400cf8 <polybench_alloc_data+0x20>
  400cf0:	a8c17bfd 	ldp	x29, x30, [sp], #16
  400cf4:	d65f03c0 	ret
  400cf8:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400cfc:	f9405503 	ldr	x3, [x8, #168]
  400d00:	b0000000 	adrp	x0, 401000 <main+0x130>
  400d04:	9112a000 	add	x0, x0, #0x4a8
  400d08:	52800641 	mov	w1, #0x32                  	// #50
  400d0c:	52800022 	mov	w2, #0x1                   	// #1
  400d10:	97ffff2c 	bl	4009c0 <fwrite@plt>
  400d14:	52800020 	mov	w0, #0x1                   	// #1
  400d18:	97fffef6 	bl	4008f0 <exit@plt>

0000000000400d1c <eval_kern_time>:
  400d1c:	d2d9acaa 	mov	x10, #0xcd6500000000        	// #225833675390976
  400d20:	cb010069 	sub	x9, x3, x1
  400d24:	f2e839aa 	movk	x10, #0x41cd, lsl #48
  400d28:	cb000048 	sub	x8, x2, x0
  400d2c:	9e620121 	scvtf	d1, x9
  400d30:	9e670142 	fmov	d2, x10
  400d34:	9e620100 	scvtf	d0, x8
  400d38:	1e621821 	fdiv	d1, d1, d2
  400d3c:	b0000000 	adrp	x0, 401000 <main+0x130>
  400d40:	1e602820 	fadd	d0, d1, d0
  400d44:	9113c000 	add	x0, x0, #0x4f0
  400d48:	17ffff26 	b	4009e0 <printf@plt>

0000000000400d4c <check_file>:
  400d4c:	b4000060 	cbz	x0, 400d58 <check_file+0xc>
  400d50:	52800020 	mov	w0, #0x1                   	// #1
  400d54:	d65f03c0 	ret
  400d58:	f81e0ff3 	str	x19, [sp, #-32]!
  400d5c:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400d60:	f9405513 	ldr	x19, [x8, #168]
  400d64:	a9017bfd 	stp	x29, x30, [sp, #16]
  400d68:	910043fd 	add	x29, sp, #0x10
  400d6c:	97ffff25 	bl	400a00 <__errno_location@plt>
  400d70:	b9400000 	ldr	w0, [x0]
  400d74:	97fffeff 	bl	400970 <strerror@plt>
  400d78:	b0000001 	adrp	x1, 401000 <main+0x130>
  400d7c:	aa0003e2 	mov	x2, x0
  400d80:	9113d421 	add	x1, x1, #0x4f5
  400d84:	aa1303e0 	mov	x0, x19
  400d88:	97ffff22 	bl	400a10 <fprintf@plt>
  400d8c:	a9417bfd 	ldp	x29, x30, [sp, #16]
  400d90:	2a1f03e0 	mov	w0, wzr
  400d94:	f84207f3 	ldr	x19, [sp], #32
  400d98:	d65f03c0 	ret

0000000000400d9c <wait_for_the_flag>:
  400d9c:	a9bd57f6 	stp	x22, x21, [sp, #-48]!
  400da0:	b0000000 	adrp	x0, 401000 <main+0x130>
  400da4:	b0000001 	adrp	x1, 401000 <main+0x130>
  400da8:	91143400 	add	x0, x0, #0x50d
  400dac:	91144821 	add	x1, x1, #0x512
  400db0:	a9014ff4 	stp	x20, x19, [sp, #16]
  400db4:	a9027bfd 	stp	x29, x30, [sp, #32]
  400db8:	910083fd 	add	x29, sp, #0x20
  400dbc:	97fffedd 	bl	400930 <fopen@plt>
  400dc0:	b4000340 	cbz	x0, 400e28 <wait_for_the_flag+0x8c>
  400dc4:	aa0003f3 	mov	x19, x0
  400dc8:	97fffeee 	bl	400980 <fgetc_unlocked@plt>
  400dcc:	2a0003f4 	mov	w20, w0
  400dd0:	aa1303e0 	mov	x0, x19
  400dd4:	97fffed3 	bl	400920 <fclose@plt>
  400dd8:	7100c29f 	cmp	w20, #0x30
  400ddc:	540001e1 	b.ne	400e18 <wait_for_the_flag+0x7c>  // b.any
  400de0:	b0000013 	adrp	x19, 401000 <main+0x130>
  400de4:	b0000014 	adrp	x20, 401000 <main+0x130>
  400de8:	91143673 	add	x19, x19, #0x50d
  400dec:	91144a94 	add	x20, x20, #0x512
  400df0:	aa1303e0 	mov	x0, x19
  400df4:	aa1403e1 	mov	x1, x20
  400df8:	97fffece 	bl	400930 <fopen@plt>
  400dfc:	aa0003f5 	mov	x21, x0
  400e00:	97fffee0 	bl	400980 <fgetc_unlocked@plt>
  400e04:	2a0003f6 	mov	w22, w0
  400e08:	aa1503e0 	mov	x0, x21
  400e0c:	97fffec5 	bl	400920 <fclose@plt>
  400e10:	7100c2df 	cmp	w22, #0x30
  400e14:	54fffee0 	b.eq	400df0 <wait_for_the_flag+0x54>  // b.none
  400e18:	a9427bfd 	ldp	x29, x30, [sp, #32]
  400e1c:	a9414ff4 	ldp	x20, x19, [sp, #16]
  400e20:	a8c357f6 	ldp	x22, x21, [sp], #48
  400e24:	d65f03c0 	ret
  400e28:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400e2c:	f9405513 	ldr	x19, [x8, #168]
  400e30:	97fffef4 	bl	400a00 <__errno_location@plt>
  400e34:	b9400000 	ldr	w0, [x0]
  400e38:	97fffece 	bl	400970 <strerror@plt>
  400e3c:	aa0003e2 	mov	x2, x0
  400e40:	aa1303e0 	mov	x0, x19
  400e44:	a9427bfd 	ldp	x29, x30, [sp, #32]
  400e48:	a9414ff4 	ldp	x20, x19, [sp, #16]
  400e4c:	b0000001 	adrp	x1, 401000 <main+0x130>
  400e50:	9113d421 	add	x1, x1, #0x4f5
  400e54:	a8c357f6 	ldp	x22, x21, [sp], #48
  400e58:	17fffeee 	b	400a10 <fprintf@plt>

0000000000400e5c <set_the_flag>:
  400e5c:	f81e0ff3 	str	x19, [sp, #-32]!
  400e60:	b0000000 	adrp	x0, 401000 <main+0x130>
  400e64:	b0000001 	adrp	x1, 401000 <main+0x130>
  400e68:	91143400 	add	x0, x0, #0x50d
  400e6c:	91145021 	add	x1, x1, #0x514
  400e70:	a9017bfd 	stp	x29, x30, [sp, #16]
  400e74:	910043fd 	add	x29, sp, #0x10
  400e78:	97fffeae 	bl	400930 <fopen@plt>
  400e7c:	b4000120 	cbz	x0, 400ea0 <set_the_flag+0x44>
  400e80:	aa0003f3 	mov	x19, x0
  400e84:	52800620 	mov	w0, #0x31                  	// #49
  400e88:	aa1303e1 	mov	x1, x19
  400e8c:	97fffed1 	bl	4009d0 <fputc_unlocked@plt>
  400e90:	a9417bfd 	ldp	x29, x30, [sp, #16]
  400e94:	aa1303e0 	mov	x0, x19
  400e98:	f84207f3 	ldr	x19, [sp], #32
  400e9c:	17fffea1 	b	400920 <fclose@plt>
  400ea0:	d0000088 	adrp	x8, 412000 <exit@GLIBC_2.17>
  400ea4:	f9405513 	ldr	x19, [x8, #168]
  400ea8:	97fffed6 	bl	400a00 <__errno_location@plt>
  400eac:	b9400000 	ldr	w0, [x0]
  400eb0:	97fffeb0 	bl	400970 <strerror@plt>
  400eb4:	a9417bfd 	ldp	x29, x30, [sp, #16]
  400eb8:	b0000001 	adrp	x1, 401000 <main+0x130>
  400ebc:	9113d421 	add	x1, x1, #0x4f5
  400ec0:	aa0003e2 	mov	x2, x0
  400ec4:	aa1303e0 	mov	x0, x19
  400ec8:	f84207f3 	ldr	x19, [sp], #32
  400ecc:	17fffed1 	b	400a10 <fprintf@plt>

0000000000400ed0 <main>:
  400ed0:	f81b0ff9 	str	x25, [sp, #-80]!
  400ed4:	a90257f6 	stp	x22, x21, [sp, #32]
  400ed8:	aa0103f5 	mov	x21, x1
  400edc:	2a0003f6 	mov	w22, w0
  400ee0:	52a00080 	mov	w0, #0x40000               	// #262144
  400ee4:	52800081 	mov	w1, #0x4                   	// #4
  400ee8:	a9015ff8 	stp	x24, x23, [sp, #16]
  400eec:	a9034ff4 	stp	x20, x19, [sp, #48]
  400ef0:	a9047bfd 	stp	x29, x30, [sp, #64]
  400ef4:	910103fd 	add	x29, sp, #0x40
  400ef8:	97ffff78 	bl	400cd8 <polybench_alloc_data>
  400efc:	aa0003f3 	mov	x19, x0
  400f00:	52a00080 	mov	w0, #0x40000               	// #262144
  400f04:	52800081 	mov	w1, #0x4                   	// #4
  400f08:	97ffff74 	bl	400cd8 <polybench_alloc_data>
  400f0c:	b0000008 	adrp	x8, 401000 <main+0x130>
  400f10:	3dc13900 	ldr	q0, [x8, #1248]
  400f14:	aa0003f4 	mov	x20, x0
  400f18:	aa1f03e9 	mov	x9, xzr
  400f1c:	4f000481 	movi	v1.4s, #0x4
  400f20:	4f000502 	movi	v2.4s, #0x8
  400f24:	4ea18403 	add	v3.4s, v0.4s, v1.4s
  400f28:	8b09026a 	add	x10, x19, x9
  400f2c:	91008129 	add	x9, x9, #0x20
  400f30:	4e21d804 	scvtf	v4.4s, v0.4s
  400f34:	4e21d863 	scvtf	v3.4s, v3.4s
  400f38:	f144013f 	cmp	x9, #0x100, lsl #12
  400f3c:	4ea28400 	add	v0.4s, v0.4s, v2.4s
  400f40:	ad000d44 	stp	q4, q3, [x10]
  400f44:	54ffff01 	b.ne	400f24 <main+0x54>  // b.any
  400f48:	3dc13900 	ldr	q0, [x8, #1248]
  400f4c:	aa1f03e9 	mov	x9, xzr
  400f50:	4f000481 	movi	v1.4s, #0x4
  400f54:	4f000502 	movi	v2.4s, #0x8
  400f58:	4ea18403 	add	v3.4s, v0.4s, v1.4s
  400f5c:	8b090288 	add	x8, x20, x9
  400f60:	91008129 	add	x9, x9, #0x20
  400f64:	4e21d804 	scvtf	v4.4s, v0.4s
  400f68:	4e21d863 	scvtf	v3.4s, v3.4s
  400f6c:	f144013f 	cmp	x9, #0x100, lsl #12
  400f70:	4ea28400 	add	v0.4s, v0.4s, v2.4s
  400f74:	ad000d04 	stp	q4, q3, [x8]
  400f78:	54ffff01 	b.ne	400f58 <main+0x88>  // b.any
  400f7c:	97ffff88 	bl	400d9c <wait_for_the_flag>
  400f80:	d0000097 	adrp	x23, 412000 <exit@GLIBC_2.17>
  400f84:	9103a2f7 	add	x23, x23, #0xe8
  400f88:	52800080 	mov	w0, #0x4                   	// #4
  400f8c:	aa1703e1 	mov	x1, x23
  400f90:	97fffe60 	bl	400910 <clock_gettime@plt>
  400f94:	aa1f03e8 	mov	x8, xzr
  400f98:	bc687a60 	ldr	s0, [x19, x8, lsl #2]
  400f9c:	52801009 	mov	w9, #0x80                  	// #128
  400fa0:	d37ef50a 	lsl	x10, x8, #2
  400fa4:	bc6a6a81 	ldr	s1, [x20, x10]
  400fa8:	71000529 	subs	w9, w9, #0x1
  400fac:	1e212800 	fadd	s0, s0, s1
  400fb0:	bc2a6a60 	str	s0, [x19, x10]
  400fb4:	54ffff61 	b.ne	400fa0 <main+0xd0>  // b.any
  400fb8:	91004108 	add	x8, x8, #0x10
  400fbc:	f141011f 	cmp	x8, #0x40, lsl #12
  400fc0:	54fffec3 	b.cc	400f98 <main+0xc8>  // b.lo, b.ul, b.last
  400fc4:	aa1f03e8 	mov	x8, xzr
  400fc8:	b2400109 	orr	x9, x8, #0x1
  400fcc:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  400fd0:	5280100a 	mov	w10, #0x80                  	// #128
  400fd4:	d37ef52b 	lsl	x11, x9, #2
  400fd8:	bc6b6a81 	ldr	s1, [x20, x11]
  400fdc:	7100054a 	subs	w10, w10, #0x1
  400fe0:	1e212800 	fadd	s0, s0, s1
  400fe4:	bc2b6a60 	str	s0, [x19, x11]
  400fe8:	54ffff61 	b.ne	400fd4 <main+0x104>  // b.any
  400fec:	91004108 	add	x8, x8, #0x10
  400ff0:	f141011f 	cmp	x8, #0x40, lsl #12
  400ff4:	54fffea3 	b.cc	400fc8 <main+0xf8>  // b.lo, b.ul, b.last
  400ff8:	aa1f03e8 	mov	x8, xzr
  400ffc:	b27f0109 	orr	x9, x8, #0x2
  401000:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  401004:	5280100a 	mov	w10, #0x80                  	// #128
  401008:	d37ef52b 	lsl	x11, x9, #2
  40100c:	bc6b6a81 	ldr	s1, [x20, x11]
  401010:	7100054a 	subs	w10, w10, #0x1
  401014:	1e212800 	fadd	s0, s0, s1
  401018:	bc2b6a60 	str	s0, [x19, x11]
  40101c:	54ffff61 	b.ne	401008 <main+0x138>  // b.any
  401020:	91004108 	add	x8, x8, #0x10
  401024:	f141011f 	cmp	x8, #0x40, lsl #12
  401028:	54fffea3 	b.cc	400ffc <main+0x12c>  // b.lo, b.ul, b.last
  40102c:	aa1f03e8 	mov	x8, xzr
  401030:	b2400509 	orr	x9, x8, #0x3
  401034:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  401038:	5280100a 	mov	w10, #0x80                  	// #128
  40103c:	d37ef52b 	lsl	x11, x9, #2
  401040:	bc6b6a81 	ldr	s1, [x20, x11]
  401044:	7100054a 	subs	w10, w10, #0x1
  401048:	1e212800 	fadd	s0, s0, s1
  40104c:	bc2b6a60 	str	s0, [x19, x11]
  401050:	54ffff61 	b.ne	40103c <main+0x16c>  // b.any
  401054:	91004108 	add	x8, x8, #0x10
  401058:	f141011f 	cmp	x8, #0x40, lsl #12
  40105c:	54fffea3 	b.cc	401030 <main+0x160>  // b.lo, b.ul, b.last
  401060:	aa1f03e8 	mov	x8, xzr
  401064:	b27e0109 	orr	x9, x8, #0x4
  401068:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  40106c:	5280100a 	mov	w10, #0x80                  	// #128
  401070:	d37ef52b 	lsl	x11, x9, #2
  401074:	bc6b6a81 	ldr	s1, [x20, x11]
  401078:	7100054a 	subs	w10, w10, #0x1
  40107c:	1e212800 	fadd	s0, s0, s1
  401080:	bc2b6a60 	str	s0, [x19, x11]
  401084:	54ffff61 	b.ne	401070 <main+0x1a0>  // b.any
  401088:	91004108 	add	x8, x8, #0x10
  40108c:	f141011f 	cmp	x8, #0x40, lsl #12
  401090:	54fffea3 	b.cc	401064 <main+0x194>  // b.lo, b.ul, b.last
  401094:	aa1f03e8 	mov	x8, xzr
  401098:	528000a9 	mov	w9, #0x5                   	// #5
  40109c:	aa09010a 	orr	x10, x8, x9
  4010a0:	bc6a7a60 	ldr	s0, [x19, x10, lsl #2]
  4010a4:	5280100b 	mov	w11, #0x80                  	// #128
  4010a8:	d37ef54c 	lsl	x12, x10, #2
  4010ac:	bc6c6a81 	ldr	s1, [x20, x12]
  4010b0:	7100056b 	subs	w11, w11, #0x1
  4010b4:	1e212800 	fadd	s0, s0, s1
  4010b8:	bc2c6a60 	str	s0, [x19, x12]
  4010bc:	54ffff61 	b.ne	4010a8 <main+0x1d8>  // b.any
  4010c0:	91004108 	add	x8, x8, #0x10
  4010c4:	f141011f 	cmp	x8, #0x40, lsl #12
  4010c8:	54fffea3 	b.cc	40109c <main+0x1cc>  // b.lo, b.ul, b.last
  4010cc:	aa1f03e8 	mov	x8, xzr
  4010d0:	b27f0509 	orr	x9, x8, #0x6
  4010d4:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  4010d8:	5280100a 	mov	w10, #0x80                  	// #128
  4010dc:	d37ef52b 	lsl	x11, x9, #2
  4010e0:	bc6b6a81 	ldr	s1, [x20, x11]
  4010e4:	7100054a 	subs	w10, w10, #0x1
  4010e8:	1e212800 	fadd	s0, s0, s1
  4010ec:	bc2b6a60 	str	s0, [x19, x11]
  4010f0:	54ffff61 	b.ne	4010dc <main+0x20c>  // b.any
  4010f4:	91004108 	add	x8, x8, #0x10
  4010f8:	f141011f 	cmp	x8, #0x40, lsl #12
  4010fc:	54fffea3 	b.cc	4010d0 <main+0x200>  // b.lo, b.ul, b.last
  401100:	aa1f03e8 	mov	x8, xzr
  401104:	b2400909 	orr	x9, x8, #0x7
  401108:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  40110c:	5280100a 	mov	w10, #0x80                  	// #128
  401110:	d37ef52b 	lsl	x11, x9, #2
  401114:	bc6b6a81 	ldr	s1, [x20, x11]
  401118:	7100054a 	subs	w10, w10, #0x1
  40111c:	1e212800 	fadd	s0, s0, s1
  401120:	bc2b6a60 	str	s0, [x19, x11]
  401124:	54ffff61 	b.ne	401110 <main+0x240>  // b.any
  401128:	91004108 	add	x8, x8, #0x10
  40112c:	f141011f 	cmp	x8, #0x40, lsl #12
  401130:	54fffea3 	b.cc	401104 <main+0x234>  // b.lo, b.ul, b.last
  401134:	aa1f03e8 	mov	x8, xzr
  401138:	b27d0109 	orr	x9, x8, #0x8
  40113c:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  401140:	5280100a 	mov	w10, #0x80                  	// #128
  401144:	d37ef52b 	lsl	x11, x9, #2
  401148:	bc6b6a81 	ldr	s1, [x20, x11]
  40114c:	7100054a 	subs	w10, w10, #0x1
  401150:	1e212800 	fadd	s0, s0, s1
  401154:	bc2b6a60 	str	s0, [x19, x11]
  401158:	54ffff61 	b.ne	401144 <main+0x274>  // b.any
  40115c:	91004108 	add	x8, x8, #0x10
  401160:	f141011f 	cmp	x8, #0x40, lsl #12
  401164:	54fffea3 	b.cc	401138 <main+0x268>  // b.lo, b.ul, b.last
  401168:	aa1f03e8 	mov	x8, xzr
  40116c:	52800129 	mov	w9, #0x9                   	// #9
  401170:	aa09010a 	orr	x10, x8, x9
  401174:	bc6a7a60 	ldr	s0, [x19, x10, lsl #2]
  401178:	5280100b 	mov	w11, #0x80                  	// #128
  40117c:	d37ef54c 	lsl	x12, x10, #2
  401180:	bc6c6a81 	ldr	s1, [x20, x12]
  401184:	7100056b 	subs	w11, w11, #0x1
  401188:	1e212800 	fadd	s0, s0, s1
  40118c:	bc2c6a60 	str	s0, [x19, x12]
  401190:	54ffff61 	b.ne	40117c <main+0x2ac>  // b.any
  401194:	91004108 	add	x8, x8, #0x10
  401198:	f141011f 	cmp	x8, #0x40, lsl #12
  40119c:	54fffea3 	b.cc	401170 <main+0x2a0>  // b.lo, b.ul, b.last
  4011a0:	aa1f03e8 	mov	x8, xzr
  4011a4:	52800149 	mov	w9, #0xa                   	// #10
  4011a8:	aa09010a 	orr	x10, x8, x9
  4011ac:	bc6a7a60 	ldr	s0, [x19, x10, lsl #2]
  4011b0:	5280100b 	mov	w11, #0x80                  	// #128
  4011b4:	d37ef54c 	lsl	x12, x10, #2
  4011b8:	bc6c6a81 	ldr	s1, [x20, x12]
  4011bc:	7100056b 	subs	w11, w11, #0x1
  4011c0:	1e212800 	fadd	s0, s0, s1
  4011c4:	bc2c6a60 	str	s0, [x19, x12]
  4011c8:	54ffff61 	b.ne	4011b4 <main+0x2e4>  // b.any
  4011cc:	91004108 	add	x8, x8, #0x10
  4011d0:	f141011f 	cmp	x8, #0x40, lsl #12
  4011d4:	54fffea3 	b.cc	4011a8 <main+0x2d8>  // b.lo, b.ul, b.last
  4011d8:	aa1f03e8 	mov	x8, xzr
  4011dc:	52800169 	mov	w9, #0xb                   	// #11
  4011e0:	aa09010a 	orr	x10, x8, x9
  4011e4:	bc6a7a60 	ldr	s0, [x19, x10, lsl #2]
  4011e8:	5280100b 	mov	w11, #0x80                  	// #128
  4011ec:	d37ef54c 	lsl	x12, x10, #2
  4011f0:	bc6c6a81 	ldr	s1, [x20, x12]
  4011f4:	7100056b 	subs	w11, w11, #0x1
  4011f8:	1e212800 	fadd	s0, s0, s1
  4011fc:	bc2c6a60 	str	s0, [x19, x12]
  401200:	54ffff61 	b.ne	4011ec <main+0x31c>  // b.any
  401204:	91004108 	add	x8, x8, #0x10
  401208:	f141011f 	cmp	x8, #0x40, lsl #12
  40120c:	54fffea3 	b.cc	4011e0 <main+0x310>  // b.lo, b.ul, b.last
  401210:	aa1f03e8 	mov	x8, xzr
  401214:	b27e0509 	orr	x9, x8, #0xc
  401218:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  40121c:	5280100a 	mov	w10, #0x80                  	// #128
  401220:	d37ef52b 	lsl	x11, x9, #2
  401224:	bc6b6a81 	ldr	s1, [x20, x11]
  401228:	7100054a 	subs	w10, w10, #0x1
  40122c:	1e212800 	fadd	s0, s0, s1
  401230:	bc2b6a60 	str	s0, [x19, x11]
  401234:	54ffff61 	b.ne	401220 <main+0x350>  // b.any
  401238:	91004108 	add	x8, x8, #0x10
  40123c:	f141011f 	cmp	x8, #0x40, lsl #12
  401240:	54fffea3 	b.cc	401214 <main+0x344>  // b.lo, b.ul, b.last
  401244:	aa1f03e8 	mov	x8, xzr
  401248:	528001a9 	mov	w9, #0xd                   	// #13
  40124c:	aa09010a 	orr	x10, x8, x9
  401250:	bc6a7a60 	ldr	s0, [x19, x10, lsl #2]
  401254:	5280100b 	mov	w11, #0x80                  	// #128
  401258:	d37ef54c 	lsl	x12, x10, #2
  40125c:	bc6c6a81 	ldr	s1, [x20, x12]
  401260:	7100056b 	subs	w11, w11, #0x1
  401264:	1e212800 	fadd	s0, s0, s1
  401268:	bc2c6a60 	str	s0, [x19, x12]
  40126c:	54ffff61 	b.ne	401258 <main+0x388>  // b.any
  401270:	91004108 	add	x8, x8, #0x10
  401274:	f141011f 	cmp	x8, #0x40, lsl #12
  401278:	54fffea3 	b.cc	40124c <main+0x37c>  // b.lo, b.ul, b.last
  40127c:	aa1f03e8 	mov	x8, xzr
  401280:	b27f0909 	orr	x9, x8, #0xe
  401284:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  401288:	5280100a 	mov	w10, #0x80                  	// #128
  40128c:	d37ef52b 	lsl	x11, x9, #2
  401290:	bc6b6a81 	ldr	s1, [x20, x11]
  401294:	7100054a 	subs	w10, w10, #0x1
  401298:	1e212800 	fadd	s0, s0, s1
  40129c:	bc2b6a60 	str	s0, [x19, x11]
  4012a0:	54ffff61 	b.ne	40128c <main+0x3bc>  // b.any
  4012a4:	91004108 	add	x8, x8, #0x10
  4012a8:	f141011f 	cmp	x8, #0x40, lsl #12
  4012ac:	54fffea3 	b.cc	401280 <main+0x3b0>  // b.lo, b.ul, b.last
  4012b0:	aa1f03e8 	mov	x8, xzr
  4012b4:	b2400d09 	orr	x9, x8, #0xf
  4012b8:	bc697a60 	ldr	s0, [x19, x9, lsl #2]
  4012bc:	5280100a 	mov	w10, #0x80                  	// #128
  4012c0:	d37ef52b 	lsl	x11, x9, #2
  4012c4:	bc6b6a81 	ldr	s1, [x20, x11]
  4012c8:	7100054a 	subs	w10, w10, #0x1
  4012cc:	1e212800 	fadd	s0, s0, s1
  4012d0:	bc2b6a60 	str	s0, [x19, x11]
  4012d4:	54ffff61 	b.ne	4012c0 <main+0x3f0>  // b.any
  4012d8:	91004108 	add	x8, x8, #0x10
  4012dc:	f141011f 	cmp	x8, #0x40, lsl #12
  4012e0:	54fffea3 	b.cc	4012b4 <main+0x3e4>  // b.lo, b.ul, b.last
  4012e4:	b0000098 	adrp	x24, 412000 <exit@GLIBC_2.17>
  4012e8:	9103e318 	add	x24, x24, #0xf8
  4012ec:	52800080 	mov	w0, #0x4                   	// #4
  4012f0:	aa1803e1 	mov	x1, x24
  4012f4:	97fffd87 	bl	400910 <clock_gettime@plt>
  4012f8:	7100aedf 	cmp	w22, #0x2b
  4012fc:	5400008b 	b.lt	40130c <main+0x43c>  // b.tstop
  401300:	f94002a8 	ldr	x8, [x21]
  401304:	39400108 	ldrb	w8, [x8]
  401308:	34000348 	cbz	w8, 401370 <main+0x4a0>
  40130c:	aa1303e0 	mov	x0, x19
  401310:	97fffda8 	bl	4009b0 <free@plt>
  401314:	aa1403e0 	mov	x0, x20
  401318:	97fffda6 	bl	4009b0 <free@plt>
  40131c:	a94026e8 	ldp	x8, x9, [x23]
  401320:	a9402f0a 	ldp	x10, x11, [x24]
  401324:	d2d9acac 	mov	x12, #0xcd6500000000        	// #225833675390976
  401328:	f2e839ac 	movk	x12, #0x41cd, lsl #48
  40132c:	9e670182 	fmov	d2, x12
  401330:	cb090169 	sub	x9, x11, x9
  401334:	cb080148 	sub	x8, x10, x8
  401338:	9e620121 	scvtf	d1, x9
  40133c:	9e620100 	scvtf	d0, x8
  401340:	1e621821 	fdiv	d1, d1, d2
  401344:	90000000 	adrp	x0, 401000 <main+0x130>
  401348:	1e602820 	fadd	d0, d1, d0
  40134c:	9113c000 	add	x0, x0, #0x4f0
  401350:	97fffda4 	bl	4009e0 <printf@plt>
  401354:	a9447bfd 	ldp	x29, x30, [sp, #64]
  401358:	a9434ff4 	ldp	x20, x19, [sp, #48]
  40135c:	a94257f6 	ldp	x22, x21, [sp, #32]
  401360:	a9415ff8 	ldp	x24, x23, [sp, #16]
  401364:	2a1f03e0 	mov	w0, wzr
  401368:	f84507f9 	ldr	x25, [sp], #80
  40136c:	d65f03c0 	ret
  401370:	b0000099 	adrp	x25, 412000 <exit@GLIBC_2.17>
  401374:	f9405721 	ldr	x1, [x25, #168]
  401378:	90000015 	adrp	x21, 401000 <main+0x130>
  40137c:	aa1f03f6 	mov	x22, xzr
  401380:	91145eb5 	add	x21, x21, #0x517
  401384:	bc766a60 	ldr	s0, [x19, x22]
  401388:	aa0103e0 	mov	x0, x1
  40138c:	aa1503e1 	mov	x1, x21
  401390:	1e22c000 	fcvt	d0, s0
  401394:	97fffd9f 	bl	400a10 <fprintf@plt>
  401398:	f9405721 	ldr	x1, [x25, #168]
  40139c:	910012d6 	add	x22, x22, #0x4
  4013a0:	f14402df 	cmp	x22, #0x100, lsl #12
  4013a4:	54ffff01 	b.ne	401384 <main+0x4b4>  // b.any
  4013a8:	52800140 	mov	w0, #0xa                   	// #10
  4013ac:	97fffd55 	bl	400900 <fputc@plt>
  4013b0:	17ffffd7 	b	40130c <main+0x43c>
  4013b4:	d503201f 	nop

00000000004013b8 <__libc_csu_init>:
  4013b8:	a9bc7bfd 	stp	x29, x30, [sp, #-64]!
  4013bc:	910003fd 	mov	x29, sp
  4013c0:	a90153f3 	stp	x19, x20, [sp, #16]
  4013c4:	90000094 	adrp	x20, 411000 <__FRAME_END__+0xfa08>
  4013c8:	91378294 	add	x20, x20, #0xde0
  4013cc:	a9025bf5 	stp	x21, x22, [sp, #32]
  4013d0:	90000095 	adrp	x21, 411000 <__FRAME_END__+0xfa08>
  4013d4:	913762b5 	add	x21, x21, #0xdd8
  4013d8:	cb150294 	sub	x20, x20, x21
  4013dc:	2a0003f6 	mov	w22, w0
  4013e0:	a90363f7 	stp	x23, x24, [sp, #48]
  4013e4:	aa0103f7 	mov	x23, x1
  4013e8:	aa0203f8 	mov	x24, x2
  4013ec:	9343fe94 	asr	x20, x20, #3
  4013f0:	97fffd32 	bl	4008b8 <_init>
  4013f4:	b4000174 	cbz	x20, 401420 <__libc_csu_init+0x68>
  4013f8:	d2800013 	mov	x19, #0x0                   	// #0
  4013fc:	d503201f 	nop
  401400:	f8737aa3 	ldr	x3, [x21, x19, lsl #3]
  401404:	aa1803e2 	mov	x2, x24
  401408:	91000673 	add	x19, x19, #0x1
  40140c:	aa1703e1 	mov	x1, x23
  401410:	2a1603e0 	mov	w0, w22
  401414:	d63f0060 	blr	x3
  401418:	eb13029f 	cmp	x20, x19
  40141c:	54ffff21 	b.ne	401400 <__libc_csu_init+0x48>  // b.any
  401420:	a94153f3 	ldp	x19, x20, [sp, #16]
  401424:	a9425bf5 	ldp	x21, x22, [sp, #32]
  401428:	a94363f7 	ldp	x23, x24, [sp, #48]
  40142c:	a8c47bfd 	ldp	x29, x30, [sp], #64
  401430:	d65f03c0 	ret
  401434:	d503201f 	nop

0000000000401438 <__libc_csu_fini>:
  401438:	d65f03c0 	ret

Disassembly of section .fini:

000000000040143c <_fini>:
  40143c:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  401440:	910003fd 	mov	x29, sp
  401444:	a8c17bfd 	ldp	x29, x30, [sp], #16
  401448:	d65f03c0 	ret
