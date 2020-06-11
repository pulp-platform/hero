
; __CLANG_OFFLOAD_BUNDLE____START__ openmp-riscv32-hero-unknown-elf
; ModuleID = '2mm.c'
source_filename = "2mm.c"
target datalayout = "e-m:e-p:32:32-p1:64:32-i64:64-n32-S128-P0-A0"
target triple = "riscv32-hero-unknown-elf"

%struct.__tgt_offload_entry = type { i8*, i8*, i32, i32, i32 }

@.str = private unnamed_addr constant [18 x i8] c"# loading 0x%llx\0A\00", align 1
@.str.1 = private unnamed_addr constant [17 x i8] c"RET: %x %x %llx\0A\00", align 1
@.omp_offloading.entry_name = internal unnamed_addr constant [41 x i8] c"__omp_offloading_3d_a2bf1_kernel_2mm_l94\00"
@.omp_offloading.entry.__omp_offloading_3d_a2bf1_kernel_2mm_l94 = weak local_unnamed_addr constant %struct.__tgt_offload_entry { i8* bitcast (void (i32, i32, [128 x i32]*, i32, i32, [128 x i32]*, [128 x i32]*)* @__omp_offloading_3d_a2bf1_kernel_2mm_l94 to i8*), i8* getelementptr inbounds ([41 x i8], [41 x i8]* @.omp_offloading.entry_name, i32 0, i32 0), i32 0, i32 0, i32 0 }, section ".omp_offloading.entries", align 1
@.omp_offloading.entry_name.2 = internal unnamed_addr constant [42 x i8] c"__omp_offloading_3d_a2bf1_kernel_2mm_l114\00"
@.omp_offloading.entry.__omp_offloading_3d_a2bf1_kernel_2mm_l114 = weak local_unnamed_addr constant %struct.__tgt_offload_entry { i8* bitcast (void (i32, i32, [128 x i32]*, i32, i32, [128 x i32]*, [128 x i32]*)* @__omp_offloading_3d_a2bf1_kernel_2mm_l114 to i8*), i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.omp_offloading.entry_name.2, i32 0, i32 0), i32 0, i32 0, i32 0 }, section ".omp_offloading.entries", align 1
@llvm.used = appending global [16 x i8*] [i8* bitcast (i16 (i64)* @hero_load_uint16 to i8*), i8* bitcast (i32 (i64, i16*)* @hero_load_uint16_noblock to i8*), i8* bitcast (i32 (i64)* @hero_load_uint32 to i8*), i8* bitcast (i32 (i64, i32*)* @hero_load_uint32_noblock to i8*), i8* bitcast (i64 (i64)* @hero_load_uint64 to i8*), i8* bitcast (i32 (i64, i64*)* @hero_load_uint64_noblock to i8*), i8* bitcast (i8 (i64)* @hero_load_uint8 to i8*), i8* bitcast (i32 (i64, i8*)* @hero_load_uint8_noblock to i8*), i8* bitcast (void (i64, i16)* @hero_store_uint16 to i8*), i8* bitcast (i32 (i64, i16)* @hero_store_uint16_noblock to i8*), i8* bitcast (void (i64, i32)* @hero_store_uint32 to i8*), i8* bitcast (i32 (i64, i32)* @hero_store_uint32_noblock to i8*), i8* bitcast (void (i64, i64)* @hero_store_uint64 to i8*), i8* bitcast (i32 (i64, i64)* @hero_store_uint64_noblock to i8*), i8* bitcast (void (i64, i8)* @hero_store_uint8 to i8*), i8* bitcast (i32 (i64, i8)* @hero_store_uint8_noblock to i8*)], section "llvm.metadata"

; Function Attrs: inlinehint nounwind
define internal i32 @hero_load_uint32_noblock(i64, i32* nocapture) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i32*
  %7 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0)
  %8 = tail call { i32, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lw $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i32* %6, i32 undef) #3, !srcloc !4
  %9 = extractvalue { i32, i32, i32 } %8, 0
  store i32 %9, i32* %1, align 4, !tbaa !5
  ret i32 0
}

; Function Attrs: nofree nounwind
declare dso_local i32 @printf(i8* nocapture readonly, ...) local_unnamed_addr #1

; Function Attrs: inlinehint nounwind
define internal i32 @hero_load_uint32(i64) #0 {
  %2 = lshr i64 %0, 32
  %3 = trunc i64 %2 to i32
  %4 = trunc i64 %0 to i32
  %5 = inttoptr i32 %4 to i32*
  %6 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0) #3
  %7 = tail call { i32, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lw $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %3, i32* nonnull inttoptr (i32 270535672 to i32*), i32* %5, i32 undef) #3, !srcloc !4
  %8 = extractvalue { i32, i32, i32 } %7, 0
  ret i32 %8
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_store_uint32_noblock(i64, i32) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i32*
  %7 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sw $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i32 %1, i32* %6, i32 undef) #3, !srcloc !9
  ret i32 0
}

; Function Attrs: inlinehint nounwind
define internal void @hero_store_uint32(i64, i32) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i32*
  %7 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sw $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i32 %1, i32* %6, i32 undef) #3, !srcloc !9
  ret void
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_load_uint16_noblock(i64, i16* nocapture) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i16*
  %7 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0)
  %8 = tail call { i16, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lhu $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i16* %6, i32 undef) #3, !srcloc !10
  %9 = extractvalue { i16, i32, i32 } %8, 0
  store i16 %9, i16* %1, align 2, !tbaa !11
  ret i32 0
}

; Function Attrs: inlinehint nounwind
define internal zeroext i16 @hero_load_uint16(i64) #0 {
  %2 = lshr i64 %0, 32
  %3 = trunc i64 %2 to i32
  %4 = trunc i64 %0 to i32
  %5 = inttoptr i32 %4 to i16*
  %6 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0) #3
  %7 = tail call { i16, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lhu $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %3, i32* nonnull inttoptr (i32 270535672 to i32*), i16* %5, i32 undef) #3, !srcloc !10
  %8 = extractvalue { i16, i32, i32 } %7, 0
  ret i16 %8
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_store_uint16_noblock(i64, i16 zeroext) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i16*
  %7 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sh $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i16 %1, i16* %6, i32 undef) #3, !srcloc !13
  ret i32 0
}

; Function Attrs: inlinehint nounwind
define internal void @hero_store_uint16(i64, i16 zeroext) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i16*
  %7 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sh $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i16 %1, i16* %6, i32 undef) #3, !srcloc !13
  ret void
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_load_uint8_noblock(i64, i8* nocapture) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i8*
  %7 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0)
  %8 = tail call { i8, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lbu $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i8* %6, i32 undef) #3, !srcloc !14
  %9 = extractvalue { i8, i32, i32 } %8, 0
  store i8 %9, i8* %1, align 1, !tbaa !15
  ret i32 0
}

; Function Attrs: inlinehint nounwind
define internal zeroext i8 @hero_load_uint8(i64) #0 {
  %2 = lshr i64 %0, 32
  %3 = trunc i64 %2 to i32
  %4 = trunc i64 %0 to i32
  %5 = inttoptr i32 %4 to i8*
  %6 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0) #3
  %7 = tail call { i8, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lbu $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %3, i32* nonnull inttoptr (i32 270535672 to i32*), i8* %5, i32 undef) #3, !srcloc !14
  %8 = extractvalue { i8, i32, i32 } %7, 0
  ret i8 %8
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_store_uint8_noblock(i64, i8 zeroext) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i8*
  %7 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sb $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i8 %1, i8* %6, i32 undef) #3, !srcloc !16
  ret i32 0
}

; Function Attrs: inlinehint nounwind
define internal void @hero_store_uint8(i64, i8 zeroext) #0 {
  %3 = lshr i64 %0, 32
  %4 = trunc i64 %3 to i32
  %5 = trunc i64 %0 to i32
  %6 = inttoptr i32 %5 to i8*
  %7 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sb $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %4, i32* nonnull inttoptr (i32 270535672 to i32*), i8 %1, i8* %6, i32 undef) #3, !srcloc !16
  ret void
}

; Function Attrs: inlinehint nounwind
define internal i64 @hero_load_uint64(i64) #0 {
  %2 = lshr i64 %0, 32
  %3 = trunc i64 %2 to i32
  %4 = trunc i64 %0 to i32
  %5 = inttoptr i32 %4 to i32*
  %6 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0) #3
  %7 = tail call { i32, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lw $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %3, i32* nonnull inttoptr (i32 270535672 to i32*), i32* %5, i32 undef) #3, !srcloc !4
  %8 = extractvalue { i32, i32, i32 } %7, 0
  %9 = add i64 %0, 4
  %10 = lshr i64 %9, 32
  %11 = trunc i64 %10 to i32
  %12 = trunc i64 %9 to i32
  %13 = inttoptr i32 %12 to i32*
  %14 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %9) #3
  %15 = tail call { i32, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lw $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %11, i32* nonnull inttoptr (i32 270535672 to i32*), i32* %13, i32 undef) #3, !srcloc !4
  %16 = extractvalue { i32, i32, i32 } %15, 0
  %17 = zext i32 %16 to i64
  %18 = shl nuw i64 %17, 32
  %19 = zext i32 %8 to i64
  %20 = or i64 %18, %19
  %21 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.1, i32 0, i32 0), i32 %8, i32 %16, i64 %20)
  ret i64 %20
}

; Function Attrs: inlinehint nounwind
define internal void @hero_store_uint64(i64, i64) #0 {
  %3 = trunc i64 %1 to i32
  %4 = lshr i64 %0, 32
  %5 = trunc i64 %4 to i32
  %6 = trunc i64 %0 to i32
  %7 = inttoptr i32 %6 to i32*
  %8 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sw $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %5, i32* nonnull inttoptr (i32 270535672 to i32*), i32 %3, i32* %7, i32 undef) #3, !srcloc !9
  %9 = lshr i64 %1, 32
  %10 = trunc i64 %9 to i32
  %11 = add i64 %0, 4
  %12 = lshr i64 %11, 32
  %13 = trunc i64 %12 to i32
  %14 = trunc i64 %11 to i32
  %15 = inttoptr i32 %14 to i32*
  %16 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sw $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %13, i32* nonnull inttoptr (i32 270535672 to i32*), i32 %10, i32* %15, i32 undef) #3, !srcloc !9
  ret void
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_load_uint64_noblock(i64, i64* nocapture) #0 {
  %3 = bitcast i64* %1 to i32*
  %4 = lshr i64 %0, 32
  %5 = trunc i64 %4 to i32
  %6 = trunc i64 %0 to i32
  %7 = inttoptr i32 %6 to i32*
  %8 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %0) #3
  %9 = tail call { i32, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lw $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %5, i32* nonnull inttoptr (i32 270535672 to i32*), i32* %7, i32 undef) #3, !srcloc !4
  %10 = extractvalue { i32, i32, i32 } %9, 0
  store i32 %10, i32* %3, align 4, !tbaa !5
  %11 = getelementptr inbounds i32, i32* %3, i32 1
  %12 = add i64 %0, 4
  %13 = lshr i64 %12, 32
  %14 = trunc i64 %13 to i32
  %15 = trunc i64 %12 to i32
  %16 = inttoptr i32 %15 to i32*
  %17 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str, i32 0, i32 0), i64 %12) #3
  %18 = tail call { i32, i32, i32 } asm sideeffect "csrrci $2, 0x300, 3\0A\09sw $3, 0($4)\0A\09lw $0, 0($5)\0A\09lw $1, 4($4)\0A\09csrrw x0, 0x300, $2", "=&r,=r,=&r,r,r,r,2,~{memory}"(i32 %14, i32* nonnull inttoptr (i32 270535672 to i32*), i32* %16, i32 undef) #3, !srcloc !4
  %19 = extractvalue { i32, i32, i32 } %18, 0
  store i32 %19, i32* %11, align 4, !tbaa !5
  ret i32 0
}

; Function Attrs: inlinehint nounwind
define internal i32 @hero_store_uint64_noblock(i64, i64) #0 {
  %3 = trunc i64 %1 to i32
  %4 = lshr i64 %0, 32
  %5 = trunc i64 %4 to i32
  %6 = trunc i64 %0 to i32
  %7 = inttoptr i32 %6 to i32*
  %8 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sw $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %5, i32* nonnull inttoptr (i32 270535672 to i32*), i32 %3, i32* %7, i32 undef) #3, !srcloc !9
  %9 = lshr i64 %1, 32
  %10 = trunc i64 %9 to i32
  %11 = add i64 %0, 4
  %12 = lshr i64 %11, 32
  %13 = trunc i64 %12 to i32
  %14 = trunc i64 %11 to i32
  %15 = inttoptr i32 %14 to i32*
  %16 = tail call { i32, i32 } asm sideeffect "csrrci $1, 0x300, 3\0A\09sw $2, 0($3)\0A\09sw $4, 0($5)\0A\09lw $0, 4($3)\0A\09csrrw x0, 0x300, $1", "=r,=&r,r,r,r,r,1,~{memory}"(i32 %13, i32* nonnull inttoptr (i32 270535672 to i32*), i32 %10, i32* %15, i32 undef) #3, !srcloc !9
  ret i32 0
}

; Function Attrs: norecurse nounwind
define weak void @__omp_offloading_3d_a2bf1_kernel_2mm_l94(i32, i32, [128 x i32]*, i32, i32, [128 x i32]*, [128 x i32]*) #2 {
  br label %8

8:                                                ; preds = %28, %7
  %9 = phi i32 [ 0, %7 ], [ %29, %28 ]
  br label %10

10:                                               ; preds = %25, %8
  %11 = phi i32 [ 0, %8 ], [ %26, %25 ]
  %12 = getelementptr inbounds [128 x i32], [128 x i32]* %2, i32 %11, i32 %9
  store i32 0, i32* %12, align 4, !tbaa !5
  br label %13

13:                                               ; preds = %13, %10
  %14 = phi i32 [ 0, %10 ], [ %22, %13 ]
  %15 = phi i32 [ 0, %10 ], [ %23, %13 ]
  %16 = getelementptr inbounds [128 x i32], [128 x i32]* %5, i32 %11, i32 %15
  %17 = load i32, i32* %16, align 4, !tbaa !5
  %18 = mul nsw i32 %17, %4
  %19 = getelementptr inbounds [128 x i32], [128 x i32]* %6, i32 %15, i32 %9
  %20 = load i32, i32* %19, align 4, !tbaa !5
  %21 = mul nsw i32 %18, %20
  %22 = add nsw i32 %14, %21
  store i32 %22, i32* %12, align 4, !tbaa !5
  %23 = add nuw nsw i32 %15, 1
  %24 = icmp eq i32 %23, 128
  br i1 %24, label %25, label %13

25:                                               ; preds = %13
  %26 = add nuw nsw i32 %11, 1
  %27 = icmp eq i32 %26, 128
  br i1 %27, label %28, label %10

28:                                               ; preds = %25
  %29 = add nuw nsw i32 %9, 1
  %30 = icmp eq i32 %29, 128
  br i1 %30, label %31, label %8

31:                                               ; preds = %28
  ret void
}

; Function Attrs: norecurse nounwind
define weak void @__omp_offloading_3d_a2bf1_kernel_2mm_l114(i32, i32, [128 x i32]*, i32, i32, [128 x i32]*, [128 x i32]*) #2 {
  br label %8

8:                                                ; preds = %29, %7
  %9 = phi i32 [ 0, %7 ], [ %30, %29 ]
  br label %10

10:                                               ; preds = %26, %8
  %11 = phi i32 [ 0, %8 ], [ %27, %26 ]
  %12 = getelementptr inbounds [128 x i32], [128 x i32]* %2, i32 %11, i32 %9
  %13 = load i32, i32* %12, align 4, !tbaa !5
  %14 = mul nsw i32 %13, %3
  store i32 %14, i32* %12, align 4, !tbaa !5
  br label %15

15:                                               ; preds = %15, %10
  %16 = phi i32 [ %14, %10 ], [ %23, %15 ]
  %17 = phi i32 [ 0, %10 ], [ %24, %15 ]
  %18 = getelementptr inbounds [128 x i32], [128 x i32]* %5, i32 %11, i32 %17
  %19 = load i32, i32* %18, align 4, !tbaa !5
  %20 = getelementptr inbounds [128 x i32], [128 x i32]* %6, i32 %17, i32 %9
  %21 = load i32, i32* %20, align 4, !tbaa !5
  %22 = mul nsw i32 %21, %19
  %23 = add nsw i32 %16, %22
  store i32 %23, i32* %12, align 4, !tbaa !5
  %24 = add nuw nsw i32 %17, 1
  %25 = icmp eq i32 %24, 128
  br i1 %25, label %26, label %15

26:                                               ; preds = %15
  %27 = add nuw nsw i32 %11, 1
  %28 = icmp eq i32 %27, 128
  br i1 %28, label %29, label %10

29:                                               ; preds = %26
  %30 = add nuw nsw i32 %9, 1
  %31 = icmp eq i32 %30, 128
  br i1 %31, label %32, label %8

32:                                               ; preds = %29
  ret void
}

attributes #0 = { inlinehint nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-features"="+a,+c,+f,+m,+relax,+xpulpv2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-features"="+a,+c,+f,+m,+relax,+xpulpv2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { norecurse nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-features"="+a,+c,+f,+m,+relax,+xpulpv2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!omp_offload.info = !{!0, !1}
!llvm.module.flags = !{!2}
!llvm.ident = !{!3}

!0 = !{i32 0, i32 61, i32 666609, !"kernel_2mm", i32 94, i32 0}
!1 = !{i32 0, i32 61, i32 666609, !"kernel_2mm", i32 114, i32 1}
!2 = !{i32 1, !"wchar_size", i32 4}
!3 = !{!"clang version 9.0.0 (git@iis-git.ee.ethz.ch:hero/llvm-project.git 0c0a49096d3021242dbe3b3d22967d13328e9505)"}
!4 = !{i32 -2147175900, i32 -2147176992, i32 -2147176945, i32 -2147176835, i32 -2147176764}
!5 = !{!6, !6, i64 0}
!6 = !{!"int", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
!9 = !{i32 -2147174014, i32 -2147174961, i32 -2147174914, i32 -2147174805, i32 -2147174733}
!10 = !{i32 -2147171724, i32 -2147172816, i32 -2147172769, i32 -2147172659, i32 -2147172588}
!11 = !{!12, !12, i64 0}
!12 = !{!"short", !7, i64 0}
!13 = !{i32 -2147169775, i32 -2147170722, i32 -2147170675, i32 -2147170566, i32 -2147170494}
!14 = !{i32 -2147167443, i32 -2147168524, i32 -2147168477, i32 -2147168367, i32 -2147168296}
!15 = !{!7, !7, i64 0}
!16 = !{i32 -2147165515, i32 -2147166453, i32 -2147166406, i32 -2147166297, i32 -2147166225}

; __CLANG_OFFLOAD_BUNDLE____END__ openmp-riscv32-hero-unknown-elf

; __CLANG_OFFLOAD_BUNDLE____START__ host-aarch64-hero-linux-gnu
; ModuleID = '/tmp/2mm-0ee948.bc'
source_filename = "2mm.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-hero-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque
%struct.__tgt_offload_entry = type { i8*, i8*, i64, i32, i32 }
%struct.__tgt_device_image = type { i8*, i8*, %struct.__tgt_offload_entry*, %struct.__tgt_offload_entry* }
%struct.__tgt_bin_desc = type { i32, %struct.__tgt_device_image*, %struct.__tgt_offload_entry*, %struct.__tgt_offload_entry* }

$.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf = comdat any

@polybench_hero_mem_level = dso_local local_unnamed_addr global i32 2, align 4
@.offload_sizes = private unnamed_addr constant [5 x i64] [i64 65536, i64 65536, i64 65536, i64 65536, i64 65536]
@.offload_maptypes = private unnamed_addr constant [5 x i64] [i64 33, i64 33, i64 33, i64 32, i64 35]
@.__omp_offloading_3d_a2bf1_kernel_2mm_l94.region_id = weak constant i8 0
@.__omp_offloading_3d_a2bf1_kernel_2mm_l114.region_id = weak constant i8 0
@.offload_sizes.3 = private unnamed_addr constant [7 x i64] [i64 4, i64 4, i64 0, i64 4, i64 4, i64 0, i64 0]
@.offload_maptypes.4 = private unnamed_addr constant [7 x i64] [i64 800, i64 800, i64 544, i64 800, i64 800, i64 544, i64 544]
@stderr = external dso_local local_unnamed_addr global %struct._IO_FILE*, align 8
@.str = private unnamed_addr constant [8 x i8] c"%0.2lf \00", align 1
@.omp_offloading.entry_name = internal unnamed_addr constant [41 x i8] c"__omp_offloading_3d_a2bf1_kernel_2mm_l94\00"
@.omp_offloading.entry.__omp_offloading_3d_a2bf1_kernel_2mm_l94 = weak local_unnamed_addr constant %struct.__tgt_offload_entry { i8* @.__omp_offloading_3d_a2bf1_kernel_2mm_l94.region_id, i8* getelementptr inbounds ([41 x i8], [41 x i8]* @.omp_offloading.entry_name, i32 0, i32 0), i64 0, i32 0, i32 0 }, section ".omp_offloading.entries", align 1
@.omp_offloading.entry_name.6 = internal unnamed_addr constant [42 x i8] c"__omp_offloading_3d_a2bf1_kernel_2mm_l114\00"
@.omp_offloading.entry.__omp_offloading_3d_a2bf1_kernel_2mm_l114 = weak local_unnamed_addr constant %struct.__tgt_offload_entry { i8* @.__omp_offloading_3d_a2bf1_kernel_2mm_l114.region_id, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.omp_offloading.entry_name.6, i32 0, i32 0), i64 0, i32 0, i32 0 }, section ".omp_offloading.entries", align 1
@.omp_offloading.entries_begin = external constant %struct.__tgt_offload_entry
@.omp_offloading.entries_end = external constant %struct.__tgt_offload_entry
@.omp_offloading.img_start.riscv32-hero-unknown-elf = extern_weak constant i8
@.omp_offloading.img_end.riscv32-hero-unknown-elf = extern_weak constant i8
@.omp_offloading.device_images = internal unnamed_addr constant [1 x %struct.__tgt_device_image] [%struct.__tgt_device_image { i8* @.omp_offloading.img_start.riscv32-hero-unknown-elf, i8* @.omp_offloading.img_end.riscv32-hero-unknown-elf, %struct.__tgt_offload_entry* @.omp_offloading.entries_begin, %struct.__tgt_offload_entry* @.omp_offloading.entries_end }], comdat($.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf), align 8
@.omp_offloading.descriptor = internal constant %struct.__tgt_bin_desc { i32 1, %struct.__tgt_device_image* getelementptr inbounds ([1 x %struct.__tgt_device_image], [1 x %struct.__tgt_device_image]* @.omp_offloading.device_images, i32 0, i32 0), %struct.__tgt_offload_entry* @.omp_offloading.entries_begin, %struct.__tgt_offload_entry* @.omp_offloading.entries_end }, comdat($.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf), align 8
@__dso_handle = external hidden global i8
@llvm.global_ctors = appending global [2 x { i32, void ()*, i8* }] [{ i32, void ()*, i8* } { i32 0, void ()* @.omp_offloading.requires_reg, i8* null }, { i32, void ()*, i8* } { i32 0, void ()* @.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf, i8* bitcast (void ()* @.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf to i8*) }]

; Function Attrs: nounwind
define dso_local i32 @main(i32, i8** nocapture readnone) local_unnamed_addr #0 {
  %3 = alloca [5 x i8*], align 8
  %4 = alloca [5 x i8*], align 8
  %5 = alloca [7 x i8*], align 16
  %6 = alloca [7 x i8*], align 16
  %7 = alloca [7 x i8*], align 16
  %8 = alloca [7 x i8*], align 16
  %9 = tail call i8* @polybench_alloc_data(i64 16384, i32 4) #5
  %10 = tail call i8* @polybench_alloc_data(i64 16384, i32 4) #5
  %11 = tail call i8* @polybench_alloc_data(i64 16384, i32 4) #5
  %12 = tail call i8* @polybench_alloc_data(i64 16384, i32 4) #5
  %13 = tail call i8* @polybench_alloc_data(i64 16384, i32 4) #5
  %14 = bitcast i8* %10 to [128 x i32]*
  br label %15

15:                                               ; preds = %2, %15
  %16 = phi i64 [ 0, %2 ], [ %148, %15 ]
  %17 = trunc i64 %16 to i32
  %18 = insertelement <4 x i32> undef, i32 %17, i32 0
  %19 = shufflevector <4 x i32> %18, <4 x i32> undef, <4 x i32> zeroinitializer
  %20 = mul <4 x i32> %19, <i32 0, i32 1, i32 2, i32 3>
  %21 = mul <4 x i32> %19, <i32 4, i32 5, i32 6, i32 7>
  %22 = lshr <4 x i32> %20, <i32 7, i32 7, i32 7, i32 7>
  %23 = lshr <4 x i32> %21, <i32 7, i32 7, i32 7, i32 7>
  %24 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 0
  %25 = bitcast i32* %24 to <4 x i32>*
  store <4 x i32> %22, <4 x i32>* %25, align 4, !tbaa !4
  %26 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 4
  %27 = bitcast i32* %26 to <4 x i32>*
  store <4 x i32> %23, <4 x i32>* %27, align 4, !tbaa !4
  %28 = mul <4 x i32> %19, <i32 8, i32 9, i32 10, i32 11>
  %29 = mul <4 x i32> %19, <i32 12, i32 13, i32 14, i32 15>
  %30 = lshr <4 x i32> %28, <i32 7, i32 7, i32 7, i32 7>
  %31 = lshr <4 x i32> %29, <i32 7, i32 7, i32 7, i32 7>
  %32 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 8
  %33 = bitcast i32* %32 to <4 x i32>*
  store <4 x i32> %30, <4 x i32>* %33, align 4, !tbaa !4
  %34 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 12
  %35 = bitcast i32* %34 to <4 x i32>*
  store <4 x i32> %31, <4 x i32>* %35, align 4, !tbaa !4
  %36 = mul <4 x i32> %19, <i32 16, i32 17, i32 18, i32 19>
  %37 = mul <4 x i32> %19, <i32 20, i32 21, i32 22, i32 23>
  %38 = lshr <4 x i32> %36, <i32 7, i32 7, i32 7, i32 7>
  %39 = lshr <4 x i32> %37, <i32 7, i32 7, i32 7, i32 7>
  %40 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 16
  %41 = bitcast i32* %40 to <4 x i32>*
  store <4 x i32> %38, <4 x i32>* %41, align 4, !tbaa !4
  %42 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 20
  %43 = bitcast i32* %42 to <4 x i32>*
  store <4 x i32> %39, <4 x i32>* %43, align 4, !tbaa !4
  %44 = mul <4 x i32> %19, <i32 24, i32 25, i32 26, i32 27>
  %45 = mul <4 x i32> %19, <i32 28, i32 29, i32 30, i32 31>
  %46 = lshr <4 x i32> %44, <i32 7, i32 7, i32 7, i32 7>
  %47 = lshr <4 x i32> %45, <i32 7, i32 7, i32 7, i32 7>
  %48 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 24
  %49 = bitcast i32* %48 to <4 x i32>*
  store <4 x i32> %46, <4 x i32>* %49, align 4, !tbaa !4
  %50 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 28
  %51 = bitcast i32* %50 to <4 x i32>*
  store <4 x i32> %47, <4 x i32>* %51, align 4, !tbaa !4
  %52 = mul <4 x i32> %19, <i32 32, i32 33, i32 34, i32 35>
  %53 = mul <4 x i32> %19, <i32 36, i32 37, i32 38, i32 39>
  %54 = lshr <4 x i32> %52, <i32 7, i32 7, i32 7, i32 7>
  %55 = lshr <4 x i32> %53, <i32 7, i32 7, i32 7, i32 7>
  %56 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 32
  %57 = bitcast i32* %56 to <4 x i32>*
  store <4 x i32> %54, <4 x i32>* %57, align 4, !tbaa !4
  %58 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 36
  %59 = bitcast i32* %58 to <4 x i32>*
  store <4 x i32> %55, <4 x i32>* %59, align 4, !tbaa !4
  %60 = mul <4 x i32> %19, <i32 40, i32 41, i32 42, i32 43>
  %61 = mul <4 x i32> %19, <i32 44, i32 45, i32 46, i32 47>
  %62 = lshr <4 x i32> %60, <i32 7, i32 7, i32 7, i32 7>
  %63 = lshr <4 x i32> %61, <i32 7, i32 7, i32 7, i32 7>
  %64 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 40
  %65 = bitcast i32* %64 to <4 x i32>*
  store <4 x i32> %62, <4 x i32>* %65, align 4, !tbaa !4
  %66 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 44
  %67 = bitcast i32* %66 to <4 x i32>*
  store <4 x i32> %63, <4 x i32>* %67, align 4, !tbaa !4
  %68 = mul <4 x i32> %19, <i32 48, i32 49, i32 50, i32 51>
  %69 = mul <4 x i32> %19, <i32 52, i32 53, i32 54, i32 55>
  %70 = lshr <4 x i32> %68, <i32 7, i32 7, i32 7, i32 7>
  %71 = lshr <4 x i32> %69, <i32 7, i32 7, i32 7, i32 7>
  %72 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 48
  %73 = bitcast i32* %72 to <4 x i32>*
  store <4 x i32> %70, <4 x i32>* %73, align 4, !tbaa !4
  %74 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 52
  %75 = bitcast i32* %74 to <4 x i32>*
  store <4 x i32> %71, <4 x i32>* %75, align 4, !tbaa !4
  %76 = mul <4 x i32> %19, <i32 56, i32 57, i32 58, i32 59>
  %77 = mul <4 x i32> %19, <i32 60, i32 61, i32 62, i32 63>
  %78 = lshr <4 x i32> %76, <i32 7, i32 7, i32 7, i32 7>
  %79 = lshr <4 x i32> %77, <i32 7, i32 7, i32 7, i32 7>
  %80 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 56
  %81 = bitcast i32* %80 to <4 x i32>*
  store <4 x i32> %78, <4 x i32>* %81, align 4, !tbaa !4
  %82 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 60
  %83 = bitcast i32* %82 to <4 x i32>*
  store <4 x i32> %79, <4 x i32>* %83, align 4, !tbaa !4
  %84 = mul <4 x i32> %19, <i32 64, i32 65, i32 66, i32 67>
  %85 = mul <4 x i32> %19, <i32 68, i32 69, i32 70, i32 71>
  %86 = lshr <4 x i32> %84, <i32 7, i32 7, i32 7, i32 7>
  %87 = lshr <4 x i32> %85, <i32 7, i32 7, i32 7, i32 7>
  %88 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 64
  %89 = bitcast i32* %88 to <4 x i32>*
  store <4 x i32> %86, <4 x i32>* %89, align 4, !tbaa !4
  %90 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 68
  %91 = bitcast i32* %90 to <4 x i32>*
  store <4 x i32> %87, <4 x i32>* %91, align 4, !tbaa !4
  %92 = mul <4 x i32> %19, <i32 72, i32 73, i32 74, i32 75>
  %93 = mul <4 x i32> %19, <i32 76, i32 77, i32 78, i32 79>
  %94 = lshr <4 x i32> %92, <i32 7, i32 7, i32 7, i32 7>
  %95 = lshr <4 x i32> %93, <i32 7, i32 7, i32 7, i32 7>
  %96 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 72
  %97 = bitcast i32* %96 to <4 x i32>*
  store <4 x i32> %94, <4 x i32>* %97, align 4, !tbaa !4
  %98 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 76
  %99 = bitcast i32* %98 to <4 x i32>*
  store <4 x i32> %95, <4 x i32>* %99, align 4, !tbaa !4
  %100 = mul <4 x i32> %19, <i32 80, i32 81, i32 82, i32 83>
  %101 = mul <4 x i32> %19, <i32 84, i32 85, i32 86, i32 87>
  %102 = lshr <4 x i32> %100, <i32 7, i32 7, i32 7, i32 7>
  %103 = lshr <4 x i32> %101, <i32 7, i32 7, i32 7, i32 7>
  %104 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 80
  %105 = bitcast i32* %104 to <4 x i32>*
  store <4 x i32> %102, <4 x i32>* %105, align 4, !tbaa !4
  %106 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 84
  %107 = bitcast i32* %106 to <4 x i32>*
  store <4 x i32> %103, <4 x i32>* %107, align 4, !tbaa !4
  %108 = mul <4 x i32> %19, <i32 88, i32 89, i32 90, i32 91>
  %109 = mul <4 x i32> %19, <i32 92, i32 93, i32 94, i32 95>
  %110 = lshr <4 x i32> %108, <i32 7, i32 7, i32 7, i32 7>
  %111 = lshr <4 x i32> %109, <i32 7, i32 7, i32 7, i32 7>
  %112 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 88
  %113 = bitcast i32* %112 to <4 x i32>*
  store <4 x i32> %110, <4 x i32>* %113, align 4, !tbaa !4
  %114 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 92
  %115 = bitcast i32* %114 to <4 x i32>*
  store <4 x i32> %111, <4 x i32>* %115, align 4, !tbaa !4
  %116 = mul <4 x i32> %19, <i32 96, i32 97, i32 98, i32 99>
  %117 = mul <4 x i32> %19, <i32 100, i32 101, i32 102, i32 103>
  %118 = lshr <4 x i32> %116, <i32 7, i32 7, i32 7, i32 7>
  %119 = lshr <4 x i32> %117, <i32 7, i32 7, i32 7, i32 7>
  %120 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 96
  %121 = bitcast i32* %120 to <4 x i32>*
  store <4 x i32> %118, <4 x i32>* %121, align 4, !tbaa !4
  %122 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 100
  %123 = bitcast i32* %122 to <4 x i32>*
  store <4 x i32> %119, <4 x i32>* %123, align 4, !tbaa !4
  %124 = mul <4 x i32> %19, <i32 104, i32 105, i32 106, i32 107>
  %125 = mul <4 x i32> %19, <i32 108, i32 109, i32 110, i32 111>
  %126 = lshr <4 x i32> %124, <i32 7, i32 7, i32 7, i32 7>
  %127 = lshr <4 x i32> %125, <i32 7, i32 7, i32 7, i32 7>
  %128 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 104
  %129 = bitcast i32* %128 to <4 x i32>*
  store <4 x i32> %126, <4 x i32>* %129, align 4, !tbaa !4
  %130 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 108
  %131 = bitcast i32* %130 to <4 x i32>*
  store <4 x i32> %127, <4 x i32>* %131, align 4, !tbaa !4
  %132 = mul <4 x i32> %19, <i32 112, i32 113, i32 114, i32 115>
  %133 = mul <4 x i32> %19, <i32 116, i32 117, i32 118, i32 119>
  %134 = lshr <4 x i32> %132, <i32 7, i32 7, i32 7, i32 7>
  %135 = lshr <4 x i32> %133, <i32 7, i32 7, i32 7, i32 7>
  %136 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 112
  %137 = bitcast i32* %136 to <4 x i32>*
  store <4 x i32> %134, <4 x i32>* %137, align 4, !tbaa !4
  %138 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 116
  %139 = bitcast i32* %138 to <4 x i32>*
  store <4 x i32> %135, <4 x i32>* %139, align 4, !tbaa !4
  %140 = mul <4 x i32> %19, <i32 120, i32 121, i32 122, i32 123>
  %141 = mul <4 x i32> %19, <i32 124, i32 125, i32 126, i32 127>
  %142 = lshr <4 x i32> %140, <i32 7, i32 7, i32 7, i32 7>
  %143 = lshr <4 x i32> %141, <i32 7, i32 7, i32 7, i32 7>
  %144 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 120
  %145 = bitcast i32* %144 to <4 x i32>*
  store <4 x i32> %142, <4 x i32>* %145, align 4, !tbaa !4
  %146 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %16, i64 124
  %147 = bitcast i32* %146 to <4 x i32>*
  store <4 x i32> %143, <4 x i32>* %147, align 4, !tbaa !4
  %148 = add nuw nsw i64 %16, 1
  %149 = icmp eq i64 %148, 128
  br i1 %149, label %150, label %15

150:                                              ; preds = %15
  %151 = bitcast i8* %12 to [128 x i32]*
  %152 = bitcast i8* %11 to [128 x i32]*
  br label %153

153:                                              ; preds = %153, %150
  %154 = phi i64 [ %286, %153 ], [ 0, %150 ]
  %155 = trunc i64 %154 to i32
  %156 = insertelement <4 x i32> undef, i32 %155, i32 0
  %157 = shufflevector <4 x i32> %156, <4 x i32> undef, <4 x i32> zeroinitializer
  %158 = mul <4 x i32> %157, <i32 1, i32 2, i32 3, i32 4>
  %159 = mul <4 x i32> %157, <i32 5, i32 6, i32 7, i32 8>
  %160 = lshr <4 x i32> %158, <i32 7, i32 7, i32 7, i32 7>
  %161 = lshr <4 x i32> %159, <i32 7, i32 7, i32 7, i32 7>
  %162 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 0
  %163 = bitcast i32* %162 to <4 x i32>*
  store <4 x i32> %160, <4 x i32>* %163, align 4, !tbaa !4
  %164 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 4
  %165 = bitcast i32* %164 to <4 x i32>*
  store <4 x i32> %161, <4 x i32>* %165, align 4, !tbaa !4
  %166 = mul <4 x i32> %157, <i32 9, i32 10, i32 11, i32 12>
  %167 = mul <4 x i32> %157, <i32 13, i32 14, i32 15, i32 16>
  %168 = lshr <4 x i32> %166, <i32 7, i32 7, i32 7, i32 7>
  %169 = lshr <4 x i32> %167, <i32 7, i32 7, i32 7, i32 7>
  %170 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 8
  %171 = bitcast i32* %170 to <4 x i32>*
  store <4 x i32> %168, <4 x i32>* %171, align 4, !tbaa !4
  %172 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 12
  %173 = bitcast i32* %172 to <4 x i32>*
  store <4 x i32> %169, <4 x i32>* %173, align 4, !tbaa !4
  %174 = mul <4 x i32> %157, <i32 17, i32 18, i32 19, i32 20>
  %175 = mul <4 x i32> %157, <i32 21, i32 22, i32 23, i32 24>
  %176 = lshr <4 x i32> %174, <i32 7, i32 7, i32 7, i32 7>
  %177 = lshr <4 x i32> %175, <i32 7, i32 7, i32 7, i32 7>
  %178 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 16
  %179 = bitcast i32* %178 to <4 x i32>*
  store <4 x i32> %176, <4 x i32>* %179, align 4, !tbaa !4
  %180 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 20
  %181 = bitcast i32* %180 to <4 x i32>*
  store <4 x i32> %177, <4 x i32>* %181, align 4, !tbaa !4
  %182 = mul <4 x i32> %157, <i32 25, i32 26, i32 27, i32 28>
  %183 = mul <4 x i32> %157, <i32 29, i32 30, i32 31, i32 32>
  %184 = lshr <4 x i32> %182, <i32 7, i32 7, i32 7, i32 7>
  %185 = lshr <4 x i32> %183, <i32 7, i32 7, i32 7, i32 7>
  %186 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 24
  %187 = bitcast i32* %186 to <4 x i32>*
  store <4 x i32> %184, <4 x i32>* %187, align 4, !tbaa !4
  %188 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 28
  %189 = bitcast i32* %188 to <4 x i32>*
  store <4 x i32> %185, <4 x i32>* %189, align 4, !tbaa !4
  %190 = mul <4 x i32> %157, <i32 33, i32 34, i32 35, i32 36>
  %191 = mul <4 x i32> %157, <i32 37, i32 38, i32 39, i32 40>
  %192 = lshr <4 x i32> %190, <i32 7, i32 7, i32 7, i32 7>
  %193 = lshr <4 x i32> %191, <i32 7, i32 7, i32 7, i32 7>
  %194 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 32
  %195 = bitcast i32* %194 to <4 x i32>*
  store <4 x i32> %192, <4 x i32>* %195, align 4, !tbaa !4
  %196 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 36
  %197 = bitcast i32* %196 to <4 x i32>*
  store <4 x i32> %193, <4 x i32>* %197, align 4, !tbaa !4
  %198 = mul <4 x i32> %157, <i32 41, i32 42, i32 43, i32 44>
  %199 = mul <4 x i32> %157, <i32 45, i32 46, i32 47, i32 48>
  %200 = lshr <4 x i32> %198, <i32 7, i32 7, i32 7, i32 7>
  %201 = lshr <4 x i32> %199, <i32 7, i32 7, i32 7, i32 7>
  %202 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 40
  %203 = bitcast i32* %202 to <4 x i32>*
  store <4 x i32> %200, <4 x i32>* %203, align 4, !tbaa !4
  %204 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 44
  %205 = bitcast i32* %204 to <4 x i32>*
  store <4 x i32> %201, <4 x i32>* %205, align 4, !tbaa !4
  %206 = mul <4 x i32> %157, <i32 49, i32 50, i32 51, i32 52>
  %207 = mul <4 x i32> %157, <i32 53, i32 54, i32 55, i32 56>
  %208 = lshr <4 x i32> %206, <i32 7, i32 7, i32 7, i32 7>
  %209 = lshr <4 x i32> %207, <i32 7, i32 7, i32 7, i32 7>
  %210 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 48
  %211 = bitcast i32* %210 to <4 x i32>*
  store <4 x i32> %208, <4 x i32>* %211, align 4, !tbaa !4
  %212 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 52
  %213 = bitcast i32* %212 to <4 x i32>*
  store <4 x i32> %209, <4 x i32>* %213, align 4, !tbaa !4
  %214 = mul <4 x i32> %157, <i32 57, i32 58, i32 59, i32 60>
  %215 = mul <4 x i32> %157, <i32 61, i32 62, i32 63, i32 64>
  %216 = lshr <4 x i32> %214, <i32 7, i32 7, i32 7, i32 7>
  %217 = lshr <4 x i32> %215, <i32 7, i32 7, i32 7, i32 7>
  %218 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 56
  %219 = bitcast i32* %218 to <4 x i32>*
  store <4 x i32> %216, <4 x i32>* %219, align 4, !tbaa !4
  %220 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 60
  %221 = bitcast i32* %220 to <4 x i32>*
  store <4 x i32> %217, <4 x i32>* %221, align 4, !tbaa !4
  %222 = mul <4 x i32> %157, <i32 65, i32 66, i32 67, i32 68>
  %223 = mul <4 x i32> %157, <i32 69, i32 70, i32 71, i32 72>
  %224 = lshr <4 x i32> %222, <i32 7, i32 7, i32 7, i32 7>
  %225 = lshr <4 x i32> %223, <i32 7, i32 7, i32 7, i32 7>
  %226 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 64
  %227 = bitcast i32* %226 to <4 x i32>*
  store <4 x i32> %224, <4 x i32>* %227, align 4, !tbaa !4
  %228 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 68
  %229 = bitcast i32* %228 to <4 x i32>*
  store <4 x i32> %225, <4 x i32>* %229, align 4, !tbaa !4
  %230 = mul <4 x i32> %157, <i32 73, i32 74, i32 75, i32 76>
  %231 = mul <4 x i32> %157, <i32 77, i32 78, i32 79, i32 80>
  %232 = lshr <4 x i32> %230, <i32 7, i32 7, i32 7, i32 7>
  %233 = lshr <4 x i32> %231, <i32 7, i32 7, i32 7, i32 7>
  %234 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 72
  %235 = bitcast i32* %234 to <4 x i32>*
  store <4 x i32> %232, <4 x i32>* %235, align 4, !tbaa !4
  %236 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 76
  %237 = bitcast i32* %236 to <4 x i32>*
  store <4 x i32> %233, <4 x i32>* %237, align 4, !tbaa !4
  %238 = mul <4 x i32> %157, <i32 81, i32 82, i32 83, i32 84>
  %239 = mul <4 x i32> %157, <i32 85, i32 86, i32 87, i32 88>
  %240 = lshr <4 x i32> %238, <i32 7, i32 7, i32 7, i32 7>
  %241 = lshr <4 x i32> %239, <i32 7, i32 7, i32 7, i32 7>
  %242 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 80
  %243 = bitcast i32* %242 to <4 x i32>*
  store <4 x i32> %240, <4 x i32>* %243, align 4, !tbaa !4
  %244 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 84
  %245 = bitcast i32* %244 to <4 x i32>*
  store <4 x i32> %241, <4 x i32>* %245, align 4, !tbaa !4
  %246 = mul <4 x i32> %157, <i32 89, i32 90, i32 91, i32 92>
  %247 = mul <4 x i32> %157, <i32 93, i32 94, i32 95, i32 96>
  %248 = lshr <4 x i32> %246, <i32 7, i32 7, i32 7, i32 7>
  %249 = lshr <4 x i32> %247, <i32 7, i32 7, i32 7, i32 7>
  %250 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 88
  %251 = bitcast i32* %250 to <4 x i32>*
  store <4 x i32> %248, <4 x i32>* %251, align 4, !tbaa !4
  %252 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 92
  %253 = bitcast i32* %252 to <4 x i32>*
  store <4 x i32> %249, <4 x i32>* %253, align 4, !tbaa !4
  %254 = mul <4 x i32> %157, <i32 97, i32 98, i32 99, i32 100>
  %255 = mul <4 x i32> %157, <i32 101, i32 102, i32 103, i32 104>
  %256 = lshr <4 x i32> %254, <i32 7, i32 7, i32 7, i32 7>
  %257 = lshr <4 x i32> %255, <i32 7, i32 7, i32 7, i32 7>
  %258 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 96
  %259 = bitcast i32* %258 to <4 x i32>*
  store <4 x i32> %256, <4 x i32>* %259, align 4, !tbaa !4
  %260 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 100
  %261 = bitcast i32* %260 to <4 x i32>*
  store <4 x i32> %257, <4 x i32>* %261, align 4, !tbaa !4
  %262 = mul <4 x i32> %157, <i32 105, i32 106, i32 107, i32 108>
  %263 = mul <4 x i32> %157, <i32 109, i32 110, i32 111, i32 112>
  %264 = lshr <4 x i32> %262, <i32 7, i32 7, i32 7, i32 7>
  %265 = lshr <4 x i32> %263, <i32 7, i32 7, i32 7, i32 7>
  %266 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 104
  %267 = bitcast i32* %266 to <4 x i32>*
  store <4 x i32> %264, <4 x i32>* %267, align 4, !tbaa !4
  %268 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 108
  %269 = bitcast i32* %268 to <4 x i32>*
  store <4 x i32> %265, <4 x i32>* %269, align 4, !tbaa !4
  %270 = mul <4 x i32> %157, <i32 113, i32 114, i32 115, i32 116>
  %271 = mul <4 x i32> %157, <i32 117, i32 118, i32 119, i32 120>
  %272 = lshr <4 x i32> %270, <i32 7, i32 7, i32 7, i32 7>
  %273 = lshr <4 x i32> %271, <i32 7, i32 7, i32 7, i32 7>
  %274 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 112
  %275 = bitcast i32* %274 to <4 x i32>*
  store <4 x i32> %272, <4 x i32>* %275, align 4, !tbaa !4
  %276 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 116
  %277 = bitcast i32* %276 to <4 x i32>*
  store <4 x i32> %273, <4 x i32>* %277, align 4, !tbaa !4
  %278 = mul <4 x i32> %157, <i32 121, i32 122, i32 123, i32 124>
  %279 = mul <4 x i32> %157, <i32 125, i32 126, i32 127, i32 128>
  %280 = lshr <4 x i32> %278, <i32 7, i32 7, i32 7, i32 7>
  %281 = lshr <4 x i32> %279, <i32 7, i32 7, i32 7, i32 7>
  %282 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 120
  %283 = bitcast i32* %282 to <4 x i32>*
  store <4 x i32> %280, <4 x i32>* %283, align 4, !tbaa !4
  %284 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %154, i64 124
  %285 = bitcast i32* %284 to <4 x i32>*
  store <4 x i32> %281, <4 x i32>* %285, align 4, !tbaa !4
  %286 = add nuw nsw i64 %154, 1
  %287 = icmp eq i64 %286, 128
  br i1 %287, label %.preheader9.preheader, label %153

.preheader9.preheader:                            ; preds = %153
  %288 = bitcast i8* %13 to [128 x i32]*
  br label %.preheader9

.preheader9:                                      ; preds = %.preheader9.preheader, %.preheader9
  %289 = phi i64 [ %421, %.preheader9 ], [ 0, %.preheader9.preheader ]
  %290 = trunc i64 %289 to i32
  %291 = insertelement <4 x i32> undef, i32 %290, i32 0
  %292 = shufflevector <4 x i32> %291, <4 x i32> undef, <4 x i32> zeroinitializer
  %293 = mul <4 x i32> %292, <i32 3, i32 4, i32 5, i32 6>
  %294 = mul <4 x i32> %292, <i32 7, i32 8, i32 9, i32 10>
  %295 = lshr <4 x i32> %293, <i32 7, i32 7, i32 7, i32 7>
  %296 = lshr <4 x i32> %294, <i32 7, i32 7, i32 7, i32 7>
  %297 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 0
  %298 = bitcast i32* %297 to <4 x i32>*
  store <4 x i32> %295, <4 x i32>* %298, align 4, !tbaa !4
  %299 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 4
  %300 = bitcast i32* %299 to <4 x i32>*
  store <4 x i32> %296, <4 x i32>* %300, align 4, !tbaa !4
  %301 = mul <4 x i32> %292, <i32 11, i32 12, i32 13, i32 14>
  %302 = mul <4 x i32> %292, <i32 15, i32 16, i32 17, i32 18>
  %303 = lshr <4 x i32> %301, <i32 7, i32 7, i32 7, i32 7>
  %304 = lshr <4 x i32> %302, <i32 7, i32 7, i32 7, i32 7>
  %305 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 8
  %306 = bitcast i32* %305 to <4 x i32>*
  store <4 x i32> %303, <4 x i32>* %306, align 4, !tbaa !4
  %307 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 12
  %308 = bitcast i32* %307 to <4 x i32>*
  store <4 x i32> %304, <4 x i32>* %308, align 4, !tbaa !4
  %309 = mul <4 x i32> %292, <i32 19, i32 20, i32 21, i32 22>
  %310 = mul <4 x i32> %292, <i32 23, i32 24, i32 25, i32 26>
  %311 = lshr <4 x i32> %309, <i32 7, i32 7, i32 7, i32 7>
  %312 = lshr <4 x i32> %310, <i32 7, i32 7, i32 7, i32 7>
  %313 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 16
  %314 = bitcast i32* %313 to <4 x i32>*
  store <4 x i32> %311, <4 x i32>* %314, align 4, !tbaa !4
  %315 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 20
  %316 = bitcast i32* %315 to <4 x i32>*
  store <4 x i32> %312, <4 x i32>* %316, align 4, !tbaa !4
  %317 = mul <4 x i32> %292, <i32 27, i32 28, i32 29, i32 30>
  %318 = mul <4 x i32> %292, <i32 31, i32 32, i32 33, i32 34>
  %319 = lshr <4 x i32> %317, <i32 7, i32 7, i32 7, i32 7>
  %320 = lshr <4 x i32> %318, <i32 7, i32 7, i32 7, i32 7>
  %321 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 24
  %322 = bitcast i32* %321 to <4 x i32>*
  store <4 x i32> %319, <4 x i32>* %322, align 4, !tbaa !4
  %323 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 28
  %324 = bitcast i32* %323 to <4 x i32>*
  store <4 x i32> %320, <4 x i32>* %324, align 4, !tbaa !4
  %325 = mul <4 x i32> %292, <i32 35, i32 36, i32 37, i32 38>
  %326 = mul <4 x i32> %292, <i32 39, i32 40, i32 41, i32 42>
  %327 = lshr <4 x i32> %325, <i32 7, i32 7, i32 7, i32 7>
  %328 = lshr <4 x i32> %326, <i32 7, i32 7, i32 7, i32 7>
  %329 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 32
  %330 = bitcast i32* %329 to <4 x i32>*
  store <4 x i32> %327, <4 x i32>* %330, align 4, !tbaa !4
  %331 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 36
  %332 = bitcast i32* %331 to <4 x i32>*
  store <4 x i32> %328, <4 x i32>* %332, align 4, !tbaa !4
  %333 = mul <4 x i32> %292, <i32 43, i32 44, i32 45, i32 46>
  %334 = mul <4 x i32> %292, <i32 47, i32 48, i32 49, i32 50>
  %335 = lshr <4 x i32> %333, <i32 7, i32 7, i32 7, i32 7>
  %336 = lshr <4 x i32> %334, <i32 7, i32 7, i32 7, i32 7>
  %337 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 40
  %338 = bitcast i32* %337 to <4 x i32>*
  store <4 x i32> %335, <4 x i32>* %338, align 4, !tbaa !4
  %339 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 44
  %340 = bitcast i32* %339 to <4 x i32>*
  store <4 x i32> %336, <4 x i32>* %340, align 4, !tbaa !4
  %341 = mul <4 x i32> %292, <i32 51, i32 52, i32 53, i32 54>
  %342 = mul <4 x i32> %292, <i32 55, i32 56, i32 57, i32 58>
  %343 = lshr <4 x i32> %341, <i32 7, i32 7, i32 7, i32 7>
  %344 = lshr <4 x i32> %342, <i32 7, i32 7, i32 7, i32 7>
  %345 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 48
  %346 = bitcast i32* %345 to <4 x i32>*
  store <4 x i32> %343, <4 x i32>* %346, align 4, !tbaa !4
  %347 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 52
  %348 = bitcast i32* %347 to <4 x i32>*
  store <4 x i32> %344, <4 x i32>* %348, align 4, !tbaa !4
  %349 = mul <4 x i32> %292, <i32 59, i32 60, i32 61, i32 62>
  %350 = mul <4 x i32> %292, <i32 63, i32 64, i32 65, i32 66>
  %351 = lshr <4 x i32> %349, <i32 7, i32 7, i32 7, i32 7>
  %352 = lshr <4 x i32> %350, <i32 7, i32 7, i32 7, i32 7>
  %353 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 56
  %354 = bitcast i32* %353 to <4 x i32>*
  store <4 x i32> %351, <4 x i32>* %354, align 4, !tbaa !4
  %355 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 60
  %356 = bitcast i32* %355 to <4 x i32>*
  store <4 x i32> %352, <4 x i32>* %356, align 4, !tbaa !4
  %357 = mul <4 x i32> %292, <i32 67, i32 68, i32 69, i32 70>
  %358 = mul <4 x i32> %292, <i32 71, i32 72, i32 73, i32 74>
  %359 = lshr <4 x i32> %357, <i32 7, i32 7, i32 7, i32 7>
  %360 = lshr <4 x i32> %358, <i32 7, i32 7, i32 7, i32 7>
  %361 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 64
  %362 = bitcast i32* %361 to <4 x i32>*
  store <4 x i32> %359, <4 x i32>* %362, align 4, !tbaa !4
  %363 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 68
  %364 = bitcast i32* %363 to <4 x i32>*
  store <4 x i32> %360, <4 x i32>* %364, align 4, !tbaa !4
  %365 = mul <4 x i32> %292, <i32 75, i32 76, i32 77, i32 78>
  %366 = mul <4 x i32> %292, <i32 79, i32 80, i32 81, i32 82>
  %367 = lshr <4 x i32> %365, <i32 7, i32 7, i32 7, i32 7>
  %368 = lshr <4 x i32> %366, <i32 7, i32 7, i32 7, i32 7>
  %369 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 72
  %370 = bitcast i32* %369 to <4 x i32>*
  store <4 x i32> %367, <4 x i32>* %370, align 4, !tbaa !4
  %371 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 76
  %372 = bitcast i32* %371 to <4 x i32>*
  store <4 x i32> %368, <4 x i32>* %372, align 4, !tbaa !4
  %373 = mul <4 x i32> %292, <i32 83, i32 84, i32 85, i32 86>
  %374 = mul <4 x i32> %292, <i32 87, i32 88, i32 89, i32 90>
  %375 = lshr <4 x i32> %373, <i32 7, i32 7, i32 7, i32 7>
  %376 = lshr <4 x i32> %374, <i32 7, i32 7, i32 7, i32 7>
  %377 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 80
  %378 = bitcast i32* %377 to <4 x i32>*
  store <4 x i32> %375, <4 x i32>* %378, align 4, !tbaa !4
  %379 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 84
  %380 = bitcast i32* %379 to <4 x i32>*
  store <4 x i32> %376, <4 x i32>* %380, align 4, !tbaa !4
  %381 = mul <4 x i32> %292, <i32 91, i32 92, i32 93, i32 94>
  %382 = mul <4 x i32> %292, <i32 95, i32 96, i32 97, i32 98>
  %383 = lshr <4 x i32> %381, <i32 7, i32 7, i32 7, i32 7>
  %384 = lshr <4 x i32> %382, <i32 7, i32 7, i32 7, i32 7>
  %385 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 88
  %386 = bitcast i32* %385 to <4 x i32>*
  store <4 x i32> %383, <4 x i32>* %386, align 4, !tbaa !4
  %387 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 92
  %388 = bitcast i32* %387 to <4 x i32>*
  store <4 x i32> %384, <4 x i32>* %388, align 4, !tbaa !4
  %389 = mul <4 x i32> %292, <i32 99, i32 100, i32 101, i32 102>
  %390 = mul <4 x i32> %292, <i32 103, i32 104, i32 105, i32 106>
  %391 = lshr <4 x i32> %389, <i32 7, i32 7, i32 7, i32 7>
  %392 = lshr <4 x i32> %390, <i32 7, i32 7, i32 7, i32 7>
  %393 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 96
  %394 = bitcast i32* %393 to <4 x i32>*
  store <4 x i32> %391, <4 x i32>* %394, align 4, !tbaa !4
  %395 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 100
  %396 = bitcast i32* %395 to <4 x i32>*
  store <4 x i32> %392, <4 x i32>* %396, align 4, !tbaa !4
  %397 = mul <4 x i32> %292, <i32 107, i32 108, i32 109, i32 110>
  %398 = mul <4 x i32> %292, <i32 111, i32 112, i32 113, i32 114>
  %399 = lshr <4 x i32> %397, <i32 7, i32 7, i32 7, i32 7>
  %400 = lshr <4 x i32> %398, <i32 7, i32 7, i32 7, i32 7>
  %401 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 104
  %402 = bitcast i32* %401 to <4 x i32>*
  store <4 x i32> %399, <4 x i32>* %402, align 4, !tbaa !4
  %403 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 108
  %404 = bitcast i32* %403 to <4 x i32>*
  store <4 x i32> %400, <4 x i32>* %404, align 4, !tbaa !4
  %405 = mul <4 x i32> %292, <i32 115, i32 116, i32 117, i32 118>
  %406 = mul <4 x i32> %292, <i32 119, i32 120, i32 121, i32 122>
  %407 = lshr <4 x i32> %405, <i32 7, i32 7, i32 7, i32 7>
  %408 = lshr <4 x i32> %406, <i32 7, i32 7, i32 7, i32 7>
  %409 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 112
  %410 = bitcast i32* %409 to <4 x i32>*
  store <4 x i32> %407, <4 x i32>* %410, align 4, !tbaa !4
  %411 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 116
  %412 = bitcast i32* %411 to <4 x i32>*
  store <4 x i32> %408, <4 x i32>* %412, align 4, !tbaa !4
  %413 = mul <4 x i32> %292, <i32 123, i32 124, i32 125, i32 126>
  %414 = mul <4 x i32> %292, <i32 127, i32 128, i32 129, i32 130>
  %415 = lshr <4 x i32> %413, <i32 7, i32 7, i32 7, i32 7>
  %416 = lshr <4 x i32> %414, <i32 7, i32 7, i32 7, i32 7>
  %417 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 120
  %418 = bitcast i32* %417 to <4 x i32>*
  store <4 x i32> %415, <4 x i32>* %418, align 4, !tbaa !4
  %419 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %289, i64 124
  %420 = bitcast i32* %419 to <4 x i32>*
  store <4 x i32> %416, <4 x i32>* %420, align 4, !tbaa !4
  %421 = add nuw nsw i64 %289, 1
  %422 = icmp eq i64 %421, 128
  br i1 %422, label %.preheader8, label %.preheader9

.preheader8:                                      ; preds = %.preheader9, %.preheader8
  %423 = phi i64 [ %555, %.preheader8 ], [ 0, %.preheader9 ]
  %424 = trunc i64 %423 to i32
  %425 = insertelement <4 x i32> undef, i32 %424, i32 0
  %426 = shufflevector <4 x i32> %425, <4 x i32> undef, <4 x i32> zeroinitializer
  %427 = mul <4 x i32> %426, <i32 2, i32 3, i32 4, i32 5>
  %428 = mul <4 x i32> %426, <i32 6, i32 7, i32 8, i32 9>
  %429 = lshr <4 x i32> %427, <i32 7, i32 7, i32 7, i32 7>
  %430 = lshr <4 x i32> %428, <i32 7, i32 7, i32 7, i32 7>
  %431 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 0
  %432 = bitcast i32* %431 to <4 x i32>*
  store <4 x i32> %429, <4 x i32>* %432, align 4, !tbaa !4
  %433 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 4
  %434 = bitcast i32* %433 to <4 x i32>*
  store <4 x i32> %430, <4 x i32>* %434, align 4, !tbaa !4
  %435 = mul <4 x i32> %426, <i32 10, i32 11, i32 12, i32 13>
  %436 = mul <4 x i32> %426, <i32 14, i32 15, i32 16, i32 17>
  %437 = lshr <4 x i32> %435, <i32 7, i32 7, i32 7, i32 7>
  %438 = lshr <4 x i32> %436, <i32 7, i32 7, i32 7, i32 7>
  %439 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 8
  %440 = bitcast i32* %439 to <4 x i32>*
  store <4 x i32> %437, <4 x i32>* %440, align 4, !tbaa !4
  %441 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 12
  %442 = bitcast i32* %441 to <4 x i32>*
  store <4 x i32> %438, <4 x i32>* %442, align 4, !tbaa !4
  %443 = mul <4 x i32> %426, <i32 18, i32 19, i32 20, i32 21>
  %444 = mul <4 x i32> %426, <i32 22, i32 23, i32 24, i32 25>
  %445 = lshr <4 x i32> %443, <i32 7, i32 7, i32 7, i32 7>
  %446 = lshr <4 x i32> %444, <i32 7, i32 7, i32 7, i32 7>
  %447 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 16
  %448 = bitcast i32* %447 to <4 x i32>*
  store <4 x i32> %445, <4 x i32>* %448, align 4, !tbaa !4
  %449 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 20
  %450 = bitcast i32* %449 to <4 x i32>*
  store <4 x i32> %446, <4 x i32>* %450, align 4, !tbaa !4
  %451 = mul <4 x i32> %426, <i32 26, i32 27, i32 28, i32 29>
  %452 = mul <4 x i32> %426, <i32 30, i32 31, i32 32, i32 33>
  %453 = lshr <4 x i32> %451, <i32 7, i32 7, i32 7, i32 7>
  %454 = lshr <4 x i32> %452, <i32 7, i32 7, i32 7, i32 7>
  %455 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 24
  %456 = bitcast i32* %455 to <4 x i32>*
  store <4 x i32> %453, <4 x i32>* %456, align 4, !tbaa !4
  %457 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 28
  %458 = bitcast i32* %457 to <4 x i32>*
  store <4 x i32> %454, <4 x i32>* %458, align 4, !tbaa !4
  %459 = mul <4 x i32> %426, <i32 34, i32 35, i32 36, i32 37>
  %460 = mul <4 x i32> %426, <i32 38, i32 39, i32 40, i32 41>
  %461 = lshr <4 x i32> %459, <i32 7, i32 7, i32 7, i32 7>
  %462 = lshr <4 x i32> %460, <i32 7, i32 7, i32 7, i32 7>
  %463 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 32
  %464 = bitcast i32* %463 to <4 x i32>*
  store <4 x i32> %461, <4 x i32>* %464, align 4, !tbaa !4
  %465 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 36
  %466 = bitcast i32* %465 to <4 x i32>*
  store <4 x i32> %462, <4 x i32>* %466, align 4, !tbaa !4
  %467 = mul <4 x i32> %426, <i32 42, i32 43, i32 44, i32 45>
  %468 = mul <4 x i32> %426, <i32 46, i32 47, i32 48, i32 49>
  %469 = lshr <4 x i32> %467, <i32 7, i32 7, i32 7, i32 7>
  %470 = lshr <4 x i32> %468, <i32 7, i32 7, i32 7, i32 7>
  %471 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 40
  %472 = bitcast i32* %471 to <4 x i32>*
  store <4 x i32> %469, <4 x i32>* %472, align 4, !tbaa !4
  %473 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 44
  %474 = bitcast i32* %473 to <4 x i32>*
  store <4 x i32> %470, <4 x i32>* %474, align 4, !tbaa !4
  %475 = mul <4 x i32> %426, <i32 50, i32 51, i32 52, i32 53>
  %476 = mul <4 x i32> %426, <i32 54, i32 55, i32 56, i32 57>
  %477 = lshr <4 x i32> %475, <i32 7, i32 7, i32 7, i32 7>
  %478 = lshr <4 x i32> %476, <i32 7, i32 7, i32 7, i32 7>
  %479 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 48
  %480 = bitcast i32* %479 to <4 x i32>*
  store <4 x i32> %477, <4 x i32>* %480, align 4, !tbaa !4
  %481 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 52
  %482 = bitcast i32* %481 to <4 x i32>*
  store <4 x i32> %478, <4 x i32>* %482, align 4, !tbaa !4
  %483 = mul <4 x i32> %426, <i32 58, i32 59, i32 60, i32 61>
  %484 = mul <4 x i32> %426, <i32 62, i32 63, i32 64, i32 65>
  %485 = lshr <4 x i32> %483, <i32 7, i32 7, i32 7, i32 7>
  %486 = lshr <4 x i32> %484, <i32 7, i32 7, i32 7, i32 7>
  %487 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 56
  %488 = bitcast i32* %487 to <4 x i32>*
  store <4 x i32> %485, <4 x i32>* %488, align 4, !tbaa !4
  %489 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 60
  %490 = bitcast i32* %489 to <4 x i32>*
  store <4 x i32> %486, <4 x i32>* %490, align 4, !tbaa !4
  %491 = mul <4 x i32> %426, <i32 66, i32 67, i32 68, i32 69>
  %492 = mul <4 x i32> %426, <i32 70, i32 71, i32 72, i32 73>
  %493 = lshr <4 x i32> %491, <i32 7, i32 7, i32 7, i32 7>
  %494 = lshr <4 x i32> %492, <i32 7, i32 7, i32 7, i32 7>
  %495 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 64
  %496 = bitcast i32* %495 to <4 x i32>*
  store <4 x i32> %493, <4 x i32>* %496, align 4, !tbaa !4
  %497 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 68
  %498 = bitcast i32* %497 to <4 x i32>*
  store <4 x i32> %494, <4 x i32>* %498, align 4, !tbaa !4
  %499 = mul <4 x i32> %426, <i32 74, i32 75, i32 76, i32 77>
  %500 = mul <4 x i32> %426, <i32 78, i32 79, i32 80, i32 81>
  %501 = lshr <4 x i32> %499, <i32 7, i32 7, i32 7, i32 7>
  %502 = lshr <4 x i32> %500, <i32 7, i32 7, i32 7, i32 7>
  %503 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 72
  %504 = bitcast i32* %503 to <4 x i32>*
  store <4 x i32> %501, <4 x i32>* %504, align 4, !tbaa !4
  %505 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 76
  %506 = bitcast i32* %505 to <4 x i32>*
  store <4 x i32> %502, <4 x i32>* %506, align 4, !tbaa !4
  %507 = mul <4 x i32> %426, <i32 82, i32 83, i32 84, i32 85>
  %508 = mul <4 x i32> %426, <i32 86, i32 87, i32 88, i32 89>
  %509 = lshr <4 x i32> %507, <i32 7, i32 7, i32 7, i32 7>
  %510 = lshr <4 x i32> %508, <i32 7, i32 7, i32 7, i32 7>
  %511 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 80
  %512 = bitcast i32* %511 to <4 x i32>*
  store <4 x i32> %509, <4 x i32>* %512, align 4, !tbaa !4
  %513 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 84
  %514 = bitcast i32* %513 to <4 x i32>*
  store <4 x i32> %510, <4 x i32>* %514, align 4, !tbaa !4
  %515 = mul <4 x i32> %426, <i32 90, i32 91, i32 92, i32 93>
  %516 = mul <4 x i32> %426, <i32 94, i32 95, i32 96, i32 97>
  %517 = lshr <4 x i32> %515, <i32 7, i32 7, i32 7, i32 7>
  %518 = lshr <4 x i32> %516, <i32 7, i32 7, i32 7, i32 7>
  %519 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 88
  %520 = bitcast i32* %519 to <4 x i32>*
  store <4 x i32> %517, <4 x i32>* %520, align 4, !tbaa !4
  %521 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 92
  %522 = bitcast i32* %521 to <4 x i32>*
  store <4 x i32> %518, <4 x i32>* %522, align 4, !tbaa !4
  %523 = mul <4 x i32> %426, <i32 98, i32 99, i32 100, i32 101>
  %524 = mul <4 x i32> %426, <i32 102, i32 103, i32 104, i32 105>
  %525 = lshr <4 x i32> %523, <i32 7, i32 7, i32 7, i32 7>
  %526 = lshr <4 x i32> %524, <i32 7, i32 7, i32 7, i32 7>
  %527 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 96
  %528 = bitcast i32* %527 to <4 x i32>*
  store <4 x i32> %525, <4 x i32>* %528, align 4, !tbaa !4
  %529 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 100
  %530 = bitcast i32* %529 to <4 x i32>*
  store <4 x i32> %526, <4 x i32>* %530, align 4, !tbaa !4
  %531 = mul <4 x i32> %426, <i32 106, i32 107, i32 108, i32 109>
  %532 = mul <4 x i32> %426, <i32 110, i32 111, i32 112, i32 113>
  %533 = lshr <4 x i32> %531, <i32 7, i32 7, i32 7, i32 7>
  %534 = lshr <4 x i32> %532, <i32 7, i32 7, i32 7, i32 7>
  %535 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 104
  %536 = bitcast i32* %535 to <4 x i32>*
  store <4 x i32> %533, <4 x i32>* %536, align 4, !tbaa !4
  %537 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 108
  %538 = bitcast i32* %537 to <4 x i32>*
  store <4 x i32> %534, <4 x i32>* %538, align 4, !tbaa !4
  %539 = mul <4 x i32> %426, <i32 114, i32 115, i32 116, i32 117>
  %540 = mul <4 x i32> %426, <i32 118, i32 119, i32 120, i32 121>
  %541 = lshr <4 x i32> %539, <i32 7, i32 7, i32 7, i32 7>
  %542 = lshr <4 x i32> %540, <i32 7, i32 7, i32 7, i32 7>
  %543 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 112
  %544 = bitcast i32* %543 to <4 x i32>*
  store <4 x i32> %541, <4 x i32>* %544, align 4, !tbaa !4
  %545 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 116
  %546 = bitcast i32* %545 to <4 x i32>*
  store <4 x i32> %542, <4 x i32>* %546, align 4, !tbaa !4
  %547 = mul <4 x i32> %426, <i32 122, i32 123, i32 124, i32 125>
  %548 = mul <4 x i32> %426, <i32 126, i32 127, i32 128, i32 129>
  %549 = lshr <4 x i32> %547, <i32 7, i32 7, i32 7, i32 7>
  %550 = lshr <4 x i32> %548, <i32 7, i32 7, i32 7, i32 7>
  %551 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 120
  %552 = bitcast i32* %551 to <4 x i32>*
  store <4 x i32> %549, <4 x i32>* %552, align 4, !tbaa !4
  %553 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %423, i64 124
  %554 = bitcast i32* %553 to <4 x i32>*
  store <4 x i32> %550, <4 x i32>* %554, align 4, !tbaa !4
  %555 = add nuw nsw i64 %423, 1
  %556 = icmp eq i64 %555, 128
  br i1 %556, label %557, label %.preheader8

557:                                              ; preds = %.preheader8
  %558 = tail call i32 bitcast (i32 (...)* @wait_for_the_flag to i32 ()*)() #5
  %559 = bitcast i8* %9 to [128 x i32]*
  %560 = bitcast [5 x i8*]* %3 to i8*
  call void @llvm.lifetime.start.p0i8(i64 40, i8* nonnull %560)
  %561 = bitcast [5 x i8*]* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 40, i8* nonnull %561)
  %562 = bitcast [7 x i8*]* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 56, i8* nonnull %562)
  %563 = bitcast [7 x i8*]* %6 to i8*
  call void @llvm.lifetime.start.p0i8(i64 56, i8* nonnull %563)
  %564 = bitcast [7 x i8*]* %7 to i8*
  call void @llvm.lifetime.start.p0i8(i64 56, i8* nonnull %564)
  %565 = bitcast [7 x i8*]* %8 to i8*
  call void @llvm.lifetime.start.p0i8(i64 56, i8* nonnull %565)
  %566 = getelementptr inbounds [5 x i8*], [5 x i8*]* %3, i64 0, i64 0
  store i8* %10, i8** %566, align 8
  %567 = getelementptr inbounds [5 x i8*], [5 x i8*]* %4, i64 0, i64 0
  store i8* %10, i8** %567, align 8
  %568 = getelementptr inbounds [5 x i8*], [5 x i8*]* %3, i64 0, i64 1
  store i8* %11, i8** %568, align 8
  %569 = getelementptr inbounds [5 x i8*], [5 x i8*]* %4, i64 0, i64 1
  store i8* %11, i8** %569, align 8
  %570 = getelementptr inbounds [5 x i8*], [5 x i8*]* %3, i64 0, i64 2
  store i8* %12, i8** %570, align 8
  %571 = getelementptr inbounds [5 x i8*], [5 x i8*]* %4, i64 0, i64 2
  store i8* %12, i8** %571, align 8
  %572 = getelementptr inbounds [5 x i8*], [5 x i8*]* %3, i64 0, i64 3
  store i8* %9, i8** %572, align 8
  %573 = getelementptr inbounds [5 x i8*], [5 x i8*]* %4, i64 0, i64 3
  store i8* %9, i8** %573, align 8
  %574 = getelementptr inbounds [5 x i8*], [5 x i8*]* %3, i64 0, i64 4
  store i8* %13, i8** %574, align 8
  %575 = getelementptr inbounds [5 x i8*], [5 x i8*]* %4, i64 0, i64 4
  store i8* %13, i8** %575, align 8
  call void @__tgt_target_data_begin(i64 -1, i32 5, i8** nonnull %566, i8** nonnull %567, i64* getelementptr inbounds ([5 x i64], [5 x i64]* @.offload_sizes, i64 0, i64 0), i64* getelementptr inbounds ([5 x i64], [5 x i64]* @.offload_maptypes, i64 0, i64 0)) #5
  %576 = getelementptr inbounds [7 x i8*], [7 x i8*]* %5, i64 0, i64 0
  %577 = getelementptr inbounds [7 x i8*], [7 x i8*]* %6, i64 0, i64 0
  %578 = bitcast [7 x i8*]* %5 to <2 x i64>*
  store <2 x i64> zeroinitializer, <2 x i64>* %578, align 16
  %579 = bitcast [7 x i8*]* %6 to <2 x i64>*
  store <2 x i64> zeroinitializer, <2 x i64>* %579, align 16
  %580 = getelementptr inbounds [7 x i8*], [7 x i8*]* %5, i64 0, i64 2
  store i8* %9, i8** %580, align 16
  %581 = getelementptr inbounds [7 x i8*], [7 x i8*]* %6, i64 0, i64 2
  store i8* %9, i8** %581, align 16
  %582 = getelementptr inbounds [7 x i8*], [7 x i8*]* %5, i64 0, i64 3
  %583 = getelementptr inbounds [7 x i8*], [7 x i8*]* %6, i64 0, i64 3
  %584 = bitcast i8** %582 to <2 x i64>*
  store <2 x i64> <i64 0, i64 32412>, <2 x i64>* %584, align 8
  %585 = bitcast i8** %583 to <2 x i64>*
  store <2 x i64> <i64 0, i64 32412>, <2 x i64>* %585, align 8
  %586 = getelementptr inbounds [7 x i8*], [7 x i8*]* %5, i64 0, i64 5
  store i8* %10, i8** %586, align 8
  %587 = getelementptr inbounds [7 x i8*], [7 x i8*]* %6, i64 0, i64 5
  store i8* %10, i8** %587, align 8
  %588 = getelementptr inbounds [7 x i8*], [7 x i8*]* %5, i64 0, i64 6
  store i8* %11, i8** %588, align 16
  %589 = getelementptr inbounds [7 x i8*], [7 x i8*]* %6, i64 0, i64 6
  store i8* %11, i8** %589, align 16
  %590 = call i32 @__tgt_target(i64 -1, i8* nonnull @.__omp_offloading_3d_a2bf1_kernel_2mm_l94.region_id, i32 7, i8** nonnull %576, i8** nonnull %577, i64* getelementptr inbounds ([7 x i64], [7 x i64]* @.offload_sizes.3, i64 0, i64 0), i64* getelementptr inbounds ([7 x i64], [7 x i64]* @.offload_maptypes.4, i64 0, i64 0)) #5
  %591 = icmp eq i32 %590, 0
  br i1 %591, label %.loopexit7, label %.preheader6

.preheader6:                                      ; preds = %557, %611
  %592 = phi i64 [ %612, %611 ], [ 0, %557 ]
  br label %593

593:                                              ; preds = %608, %.preheader6
  %594 = phi i64 [ 0, %.preheader6 ], [ %609, %608 ]
  %595 = getelementptr inbounds [128 x i32], [128 x i32]* %559, i64 %594, i64 %592
  store i32 0, i32* %595, align 4, !tbaa !4
  br label %596

596:                                              ; preds = %596, %593
  %597 = phi i32 [ 0, %593 ], [ %605, %596 ]
  %598 = phi i64 [ 0, %593 ], [ %606, %596 ]
  %599 = getelementptr inbounds [128 x i32], [128 x i32]* %14, i64 %594, i64 %598
  %600 = load i32, i32* %599, align 4, !tbaa !4
  %601 = mul nsw i32 %600, 32412
  %602 = getelementptr inbounds [128 x i32], [128 x i32]* %152, i64 %598, i64 %592
  %603 = load i32, i32* %602, align 4, !tbaa !4
  %604 = mul nsw i32 %601, %603
  %605 = add nsw i32 %604, %597
  store i32 %605, i32* %595, align 4, !tbaa !4
  %606 = add nuw nsw i64 %598, 1
  %607 = icmp eq i64 %606, 128
  br i1 %607, label %608, label %596

608:                                              ; preds = %596
  %609 = add nuw nsw i64 %594, 1
  %610 = icmp eq i64 %609, 128
  br i1 %610, label %611, label %593

611:                                              ; preds = %608
  %612 = add nuw nsw i64 %592, 1
  %613 = icmp eq i64 %612, 128
  br i1 %613, label %.loopexit7, label %.preheader6

.loopexit7:                                       ; preds = %611, %557
  %614 = getelementptr inbounds [7 x i8*], [7 x i8*]* %7, i64 0, i64 0
  %615 = getelementptr inbounds [7 x i8*], [7 x i8*]* %8, i64 0, i64 0
  %616 = bitcast [7 x i8*]* %7 to <2 x i64>*
  store <2 x i64> zeroinitializer, <2 x i64>* %616, align 16
  %617 = bitcast [7 x i8*]* %8 to <2 x i64>*
  store <2 x i64> zeroinitializer, <2 x i64>* %617, align 16
  %618 = getelementptr inbounds [7 x i8*], [7 x i8*]* %7, i64 0, i64 2
  store i8* %13, i8** %618, align 16
  %619 = getelementptr inbounds [7 x i8*], [7 x i8*]* %8, i64 0, i64 2
  store i8* %13, i8** %619, align 16
  %620 = getelementptr inbounds [7 x i8*], [7 x i8*]* %7, i64 0, i64 3
  %621 = getelementptr inbounds [7 x i8*], [7 x i8*]* %8, i64 0, i64 3
  %622 = bitcast i8** %620 to <2 x i64>*
  store <2 x i64> <i64 2123, i64 0>, <2 x i64>* %622, align 8
  %623 = bitcast i8** %621 to <2 x i64>*
  store <2 x i64> <i64 2123, i64 0>, <2 x i64>* %623, align 8
  %624 = getelementptr inbounds [7 x i8*], [7 x i8*]* %7, i64 0, i64 5
  store i8* %9, i8** %624, align 8
  %625 = getelementptr inbounds [7 x i8*], [7 x i8*]* %8, i64 0, i64 5
  store i8* %9, i8** %625, align 8
  %626 = getelementptr inbounds [7 x i8*], [7 x i8*]* %7, i64 0, i64 6
  store i8* %12, i8** %626, align 16
  %627 = getelementptr inbounds [7 x i8*], [7 x i8*]* %8, i64 0, i64 6
  store i8* %12, i8** %627, align 16
  %628 = call i32 @__tgt_target(i64 -1, i8* nonnull @.__omp_offloading_3d_a2bf1_kernel_2mm_l114.region_id, i32 7, i8** nonnull %614, i8** nonnull %615, i64* getelementptr inbounds ([7 x i64], [7 x i64]* @.offload_sizes.3, i64 0, i64 0), i64* getelementptr inbounds ([7 x i64], [7 x i64]* @.offload_maptypes.4, i64 0, i64 0)) #5
  %629 = icmp eq i32 %628, 0
  br i1 %629, label %.loopexit, label %.preheader

.preheader:                                       ; preds = %.loopexit7, %650
  %630 = phi i64 [ %651, %650 ], [ 0, %.loopexit7 ]
  br label %631

631:                                              ; preds = %647, %.preheader
  %632 = phi i64 [ 0, %.preheader ], [ %648, %647 ]
  %633 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %632, i64 %630
  %634 = load i32, i32* %633, align 4, !tbaa !4
  %635 = mul nsw i32 %634, 2123
  store i32 %635, i32* %633, align 4, !tbaa !4
  br label %636

636:                                              ; preds = %636, %631
  %637 = phi i32 [ %635, %631 ], [ %644, %636 ]
  %638 = phi i64 [ 0, %631 ], [ %645, %636 ]
  %639 = getelementptr inbounds [128 x i32], [128 x i32]* %559, i64 %632, i64 %638
  %640 = load i32, i32* %639, align 4, !tbaa !4
  %641 = getelementptr inbounds [128 x i32], [128 x i32]* %151, i64 %638, i64 %630
  %642 = load i32, i32* %641, align 4, !tbaa !4
  %643 = mul nsw i32 %642, %640
  %644 = add nsw i32 %643, %637
  store i32 %644, i32* %633, align 4, !tbaa !4
  %645 = add nuw nsw i64 %638, 1
  %646 = icmp eq i64 %645, 128
  br i1 %646, label %647, label %636

647:                                              ; preds = %636
  %648 = add nuw nsw i64 %632, 1
  %649 = icmp eq i64 %648, 128
  br i1 %649, label %650, label %631

650:                                              ; preds = %647
  %651 = add nuw nsw i64 %630, 1
  %652 = icmp eq i64 %651, 128
  br i1 %652, label %.loopexit, label %.preheader

.loopexit:                                        ; preds = %650, %.loopexit7
  call void @__tgt_target_data_end(i64 -1, i32 5, i8** nonnull %566, i8** nonnull %567, i64* getelementptr inbounds ([5 x i64], [5 x i64]* @.offload_sizes, i64 0, i64 0), i64* getelementptr inbounds ([5 x i64], [5 x i64]* @.offload_maptypes, i64 0, i64 0)) #5
  call void @llvm.lifetime.end.p0i8(i64 40, i8* nonnull %560)
  call void @llvm.lifetime.end.p0i8(i64 40, i8* nonnull %561)
  call void @llvm.lifetime.end.p0i8(i64 56, i8* nonnull %562)
  call void @llvm.lifetime.end.p0i8(i64 56, i8* nonnull %563)
  call void @llvm.lifetime.end.p0i8(i64 56, i8* nonnull %564)
  call void @llvm.lifetime.end.p0i8(i64 56, i8* nonnull %565)
  br label %653

653:                                              ; preds = %672, %.loopexit
  %654 = phi i64 [ 0, %.loopexit ], [ %673, %672 ]
  %655 = shl i64 %654, 7
  br label %656

656:                                              ; preds = %669, %653
  %657 = phi i64 [ 0, %653 ], [ %670, %669 ]
  %658 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8, !tbaa !8
  %659 = getelementptr inbounds [128 x i32], [128 x i32]* %288, i64 %654, i64 %657
  %660 = load i32, i32* %659, align 4, !tbaa !4
  %661 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %658, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str, i64 0, i64 0), i32 %660) #6
  %662 = add nuw nsw i64 %657, %655
  %663 = trunc i64 %662 to i32
  %664 = urem i32 %663, 20
  %665 = icmp eq i32 %664, 0
  br i1 %665, label %666, label %669

666:                                              ; preds = %656
  %667 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8, !tbaa !8
  %668 = call i32 @fputc(i32 10, %struct._IO_FILE* %667) #6
  br label %669

669:                                              ; preds = %666, %656
  %670 = add nuw nsw i64 %657, 1
  %671 = icmp eq i64 %670, 128
  br i1 %671, label %672, label %656

672:                                              ; preds = %669
  %673 = add nuw nsw i64 %654, 1
  %674 = icmp eq i64 %673, 128
  br i1 %674, label %675, label %653

675:                                              ; preds = %672
  %676 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8, !tbaa !8
  %677 = call i32 @fputc(i32 10, %struct._IO_FILE* %676) #6
  call void @polybench_dealloc_data(i8* %9) #5
  call void @polybench_dealloc_data(i8* %10) #5
  call void @polybench_dealloc_data(i8* %11) #5
  call void @polybench_dealloc_data(i8* %12) #5
  call void @polybench_dealloc_data(i8* nonnull %13) #5
  ret i32 0
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

declare dso_local i8* @polybench_alloc_data(i64, i32) local_unnamed_addr #2

declare dso_local i32 @wait_for_the_flag(...) local_unnamed_addr #2

declare dso_local void @polybench_dealloc_data(i8*) local_unnamed_addr #2

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

declare dso_local void @__tgt_target_data_begin(i64, i32, i8**, i8**, i64*, i64*) local_unnamed_addr

declare dso_local i32 @__tgt_target(i64, i8*, i32, i8**, i8**, i64*, i64*) local_unnamed_addr

declare dso_local void @__tgt_target_data_end(i64, i32, i8**, i8**, i64*, i64*) local_unnamed_addr

; Function Attrs: nofree nounwind
declare dso_local i32 @fprintf(%struct._IO_FILE* nocapture, i8* nocapture readonly, ...) local_unnamed_addr #3

; Function Attrs: nounwind
define internal void @.omp_offloading.requires_reg() #0 section ".text.startup" {
  tail call void @__tgt_register_requires(i64 1) #5
  ret void
}

declare dso_local void @__tgt_register_requires(i64) local_unnamed_addr

; Function Attrs: nounwind
define internal void @.omp_offloading.descriptor_unreg(i8* nocapture readnone) #0 section ".text.startup" comdat($.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf) {
  %2 = tail call i32 @__tgt_unregister_lib(%struct.__tgt_bin_desc* nonnull @.omp_offloading.descriptor) #5
  ret void
}

declare dso_local i32 @__tgt_unregister_lib(%struct.__tgt_bin_desc*) local_unnamed_addr

; Function Attrs: nounwind
define linkonce hidden void @.omp_offloading.descriptor_reg.riscv32-hero-unknown-elf() #0 section ".text.startup" comdat {
  %1 = tail call i32 @__tgt_register_lib(%struct.__tgt_bin_desc* nonnull @.omp_offloading.descriptor) #5
  %2 = tail call i32 @__cxa_atexit(void (i8*)* nonnull @.omp_offloading.descriptor_unreg, i8* bitcast (%struct.__tgt_bin_desc* @.omp_offloading.descriptor to i8*), i8* nonnull @__dso_handle) #5
  ret void
}

declare dso_local i32 @__tgt_register_lib(%struct.__tgt_bin_desc*) local_unnamed_addr

; Function Attrs: nofree nounwind
declare dso_local i32 @__cxa_atexit(void (i8*)*, i8*, i8*) local_unnamed_addr #4

; Function Attrs: nofree nounwind
declare i32 @fputc(i32, %struct._IO_FILE* nocapture) local_unnamed_addr #4

attributes #0 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+neon" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+neon" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nofree nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+neon" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nofree nounwind }
attributes #5 = { nounwind }
attributes #6 = { cold nounwind }

!omp_offload.info = !{!0, !1}
!llvm.module.flags = !{!2}
!llvm.ident = !{!3}

!0 = !{i32 0, i32 61, i32 666609, !"kernel_2mm", i32 94, i32 0}
!1 = !{i32 0, i32 61, i32 666609, !"kernel_2mm", i32 114, i32 1}
!2 = !{i32 1, !"wchar_size", i32 4}
!3 = !{!"clang version 9.0.0 (git@iis-git.ee.ethz.ch:hero/llvm-project.git 0c0a49096d3021242dbe3b3d22967d13328e9505)"}
!4 = !{!5, !5, i64 0}
!5 = !{!"int", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
!8 = !{!9, !9, i64 0}
!9 = !{!"any pointer", !6, i64 0}

; __CLANG_OFFLOAD_BUNDLE____END__ host-aarch64-hero-linux-gnu
