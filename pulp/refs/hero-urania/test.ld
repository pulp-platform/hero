
OUTPUT_ARCH(riscv)
ENTRY( _start )
MEMORY
{
  L2                 : ORIGIN = 0x1c000000, LENGTH = 0x00080000
  L1                 : ORIGIN = 0x10000004, LENGTH = 0x00040000
  L1_aliased         : ORIGIN = 0x1b000004, LENGTH = 0x0003fffc
}

SECTIONS
{
  .vectors :
  {
    . = ALIGN(4);
    __irq_vector_base = .;KEEP(*(.vectors))
  } > L2

  .l1FcTiny :
  {
    . = ALIGN(4);
    _l1FcShared_start = .;
    *(.l1FcTiny)
    *(.l1FcTiny.*)
    *(.fcTcdmTiny)
    *(.fcTcdmTiny.*)
    . = ALIGN(4);
    _l1FcShared_end = .;
  } > L1

  .data_tiny_fc :
  {
    . = ALIGN(4);
    *(.data_tiny_fc)
    *(.data_tiny_fc.*)
  } > L1

  .text :
  {
    . = ALIGN(4);
    _stext = .;
    *(.text)
    *(.text.*)
    . = ALIGN(4);
    __cluster_text_start = .;*(.cluster.text)
    *(.cluster.text.*)
    __cluster_text_end = .;_etext  =  .;
    *(.lit)
    *(.shdata)
    _endtext = .;
  } > L2

  __fc_code_end = ALIGN(8);

  .init :
  {
    . = ALIGN(4);
    KEEP( *(.init) )
  } > L1

  .fini :
  {
    . = ALIGN(4);
    KEEP( *(.fini) )
  } > L1

  .preinit_array :
  {
    . = ALIGN(4);
    PROVIDE_HIDDEN (__preinit_array_start = .);
    KEEP (*(.preinit_array))
    PROVIDE_HIDDEN (__preinit_array_end = .);
  } > L2

  .init_array :
  {
    . = ALIGN(4);
    PROVIDE_HIDDEN (__init_array_start = .);
    __CTOR_LIST__ = .;
    LONG((__CTOR_END__ - __CTOR_LIST__) / 4 - 2)
    KEEP(*(.ctors.start))
    KEEP(*(.ctors))
    KEEP (*(SORT(.init_array.*)))
    KEEP (*(.init_array ))
    LONG(0)
    __CTOR_END__ = .;
    PROVIDE_HIDDEN (__init_array_end = .);
  } > L2

  .fini_array :
  {
    . = ALIGN(4);
    PROVIDE_HIDDEN (__fini_array_start = .);
    __DTOR_LIST__ = .;
    LONG((__DTOR_END__ - __DTOR_LIST__) / 4 - 2)
    KEEP(*(.dtors.start))
    KEEP(*(.dtors))
    LONG(0)
    __DTOR_END__ = .;
    KEEP (*(SORT(.fini_array.*)))
    KEEP (*(.fini_array ))
    PROVIDE_HIDDEN (__fini_array_end = .);
  } > L2

  .boot :
  {
    . = ALIGN(4);
    *(.boot)
    *(.boot.data)
  } > L2

  .rodata :
  {
    . = ALIGN(4);
    *(.rodata);
    *(.rodata.*)
    *(.srodata);
    *(.srodata.*)
    *(.eh_frame*)
  } > L2

  .got :
  {
    . = ALIGN(4);
    *(.got.plt) * (.igot.plt) *(.got) *(.igot)
  } > L1

  .shbss :
  {
    . = ALIGN(4);
    *(.shbss)
  } > L1

  .talias :
  {
  } > L1

  .stack :
  {
    . = ALIGN(4);
    . = ALIGN(16);
    . = . + 0x800;
    stack = .;
  } > L1

  .data_fc :
  {
    . = ALIGN(4);
    *(.data_fc)
    *(.data_fc.*)
  } > L1

  .data_fc_shared :
  {
    . = ALIGN(4);
    *(.data_fc_shared)
    *(.data_fc_shared.*)
  } > L1

  .data_tiny_l1 (ORIGIN(L1_aliased) + SIZEOF(.l1FcTiny) + SIZEOF(.data_tiny_fc) + SIZEOF(.init) + SIZEOF(.fini) + SIZEOF(.preinit_array) + SIZEOF(.init_array) + SIZEOF(.fini_array) + SIZEOF(.boot) + SIZEOF(.got) + SIZEOF(.shbss) + SIZEOF(.talias) +  SIZEOF(.stack) + SIZEOF(.data_fc) + SIZEOF(.data_fc_shared)): AT(ADDR(.l1FcTiny) + SIZEOF(.l1FcTiny) + SIZEOF(.data_tiny_fc) + SIZEOF(.init) + SIZEOF(.fini) + SIZEOF(.preinit_array) + SIZEOF(.init_array) + SIZEOF(.fini_array) + SIZEOF(.boot) + SIZEOF(.got) + SIZEOF(.shbss) + SIZEOF(.talias) +  SIZEOF(.stack) + SIZEOF(.data_fc) + SIZEOF(.data_fc_shared))
  {
    . = ALIGN(4);
    *(.data_tiny_l1)
    *(.data_tiny_l1.*)
    *(.data_alias_l1)
    *(.data_alias_l1.*)
  } > L1_aliased

  .tls (ADDR(.data_tiny_l1) + SIZEOF(.data_tiny_l1)): AT(ADDR(.l1FcTiny) + SIZEOF(.l1FcTiny) + SIZEOF(.data_tiny_fc) + SIZEOF(.init) + SIZEOF(.fini) + SIZEOF(.preinit_array) + SIZEOF(.init_array) + SIZEOF(.fini_array) + SIZEOF(.boot) + SIZEOF(.got) + SIZEOF(.shbss) + SIZEOF(.talias) + SIZEOF(.stack) + SIZEOF(.data_fc) + SIZEOF(.data_fc_shared) + SIZEOF(.data_tiny_l1))
  {
    . = ALIGN(4);
    _tls_start = .;
    *(.tls)
    *(.tls.*)
    . = ALIGN(4);
    _tls_end = .;
  } > L1_aliased

  .heapsram (ADDR(.tls) + SIZEOF(.tls) * __NB_ACTIVE_PE): AT(ADDR(.l1FcTiny) + SIZEOF(.l1FcTiny) + SIZEOF(.data_tiny_fc) + SIZEOF(.init) + SIZEOF(.fini) + SIZEOF(.preinit_array) + SIZEOF(.init_array) + SIZEOF(.fini_array) + SIZEOF(.boot) + SIZEOF(.got) + SIZEOF(.shbss) + SIZEOF(.talias) + SIZEOF(.stack) + SIZEOF(.data_fc) + SIZEOF(.data_fc_shared) + SIZEOF(.data_tiny_l1) + SIZEOF(.tls) * __NB_ACTIVE_PE)
  {
    . = ALIGN(4);
    *(.heapsram)
    *(.heapsram.*)
  } > L1_aliased

  .l1cluster_g (ADDR(.data_fc_shared) + SIZEOF(.data_fc_shared) + SIZEOF(.data_tiny_l1) + SIZEOF(.tls) * __NB_ACTIVE_PE + SIZEOF(.heapsram)): AT(ADDR(.l1FcTiny) + SIZEOF(.l1FcTiny) + SIZEOF(.data_tiny_fc) + SIZEOF(.init) + SIZEOF(.fini) + SIZEOF(.preinit_array) + SIZEOF(.init_array) + SIZEOF(.fini_array) + SIZEOF(.boot) + SIZEOF(.got) + SIZEOF(.shbss) + SIZEOF(.talias) + SIZEOF(.stack) + SIZEOF(.data_fc) + SIZEOF(.data_fc_shared) + SIZEOF(.data_tiny_l1) + SIZEOF(.tls) * __NB_ACTIVE_PE + SIZEOF(.heapsram))
  {
    . = ALIGN(4);
    *(.l1cluster_g)
    *(.l1cluster_g.*)
    *(.data_l1)
    *(.data_l1.*)
    . = ALIGN(4);
    _libgomp_start = .;
    *(.libgomp)
    *(.libgomp.*)
    . = ALIGN(4);
    _heapsram_start = .;
  } > L1

  __l1_heap_start = ALIGN(4);

  __l1_heap_size = LENGTH(L1) - __l1_heap_start + ORIGIN(L1);

  _heapsram_size = LENGTH(L1) - _heapsram_start + ORIGIN(L1);

  _l1_preload_size = SIZEOF(.data_tiny_l1) + SIZEOF(.tls) + SIZEOF(.heapsram) + SIZEOF(.l1cluster_g);

  .bss_l1 (ADDR(.l1cluster_g) + SIZEOF(.l1cluster_g)): AT(ADDR(.l1FcTiny) + SIZEOF(.l1FcTiny) + SIZEOF(.data_tiny_fc) + SIZEOF(.init) + SIZEOF(.fini) + SIZEOF(.preinit_array) + SIZEOF(.init_array) + SIZEOF(.fini_array) + SIZEOF(.boot) + SIZEOF(.got) + SIZEOF(.shbss) + SIZEOF(.talias) + SIZEOF(.stack) + SIZEOF(.data_fc) + SIZEOF(.data_fc_shared) + SIZEOF(.data_tiny_l1) + SIZEOF(.tls) * __NB_ACTIVE_PE + SIZEOF(.heapsram) + SIZEOF(.l1cluster_g))
  {
    . = ALIGN(4);
    *(.bss_l1)
    *(.bss_l1.*)
    _heapsram_start = .;
    __L1_end = ABSOLUTE(.);
  } > L1

  .data :
  {
    . = ALIGN(4);
    sdata  =  .;
    _sdata  =  .;
    KEEP(*(.gnu.offload_funcs));
    KEEP(*(.gnu.offload_vars));
    *(.data);
    *(.data.*)
    *(.sdata);
    *(.sdata.*)
    . = ALIGN(4);
    edata  =  .;
    _edata  =  .;
  } > L2

  .heapl2ram :
  {
    . = ALIGN(4);
    *(.heapl2ram)
    *(.fcTcdm)
    *(.fcTcdm.*)
    *(.fcTcdm_g)
    *(.fcTcdm_g.*)
  } > L2

  .bss :
  {
    . = ALIGN(8);
    _bss_start = .;
    *(.bss)
    *(.bss.*)
    *(.sbss)
    *(.sbss.*)
    *(COMMON)
    . = ALIGN(4);
    _bss_end = .;
  } > L2

  __fc_data_end = ALIGN(8);

  .shared :
  {
    . = ALIGN(4);
    *(.l2_data)
    *(.l2_data.*)
    __L2_end = ABSOLUTE(.);
  } > L2

  __l2_data_end = ALIGN(8);

  __cluster_text_size = __cluster_text_end - __cluster_text_start;

  __l2_heap_start = ALIGN(4);

  __l2_heap_size = LENGTH(L2) - __l2_heap_start + ORIGIN(L2);

}
